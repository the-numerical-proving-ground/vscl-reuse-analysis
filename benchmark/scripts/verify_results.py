#!/usr/bin/env python3
"""Authenticate VSCLReuse campaign, pair, attempt, proof, and log records."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import statistics
import sys
from typing import Any, Mapping, Sequence

try:
    from . import resources
    from .observed_codex import code_mode_host_launch_failure
    from .common import (
        MeasurementError,
        canonical_digest,
        manifest_for_tree,
        read_object,
        resolved_regular_file,
        sha256_file,
        utc_now,
    )
    from .run_attempt import (
        _task_metadata,
        candidate_loc,
        proof_loc,
        render_effective_prompt,
    )
    from .run_benchmark import (
        CAMPAIGN_KIND,
        CPU_GUARD_ACQUIRE_INTENT_KIND,
        CPU_GUARD_IDLE_SAMPLE_SECONDS,
        CPU_GUARD_MAXIMUM_BUSY_PERCENT,
        CPU_GUARD_FRONTEND_SOURCE_RELATIVE,
        CPU_GUARD_HOST_PATH,
        CPU_GUARD_PATH,
        CPU_GUARD_RECOVERY_KIND,
        CPU_GUARD_RECOVERY_REQUEST_KIND,
        CPU_GUARD_SOURCE_RELATIVE,
        CPU_GUARD_STATUS_KIND,
        PAIR_KIND,
        _CPU_GUARD_LEASE_RE,
        _artifact_path,
        _condition_attempt_command,
        _condition_worker_command,
        _cpu_guard_acquire_command,
        _cpu_guard_launch_command,
        _cpu_guard_release_command,
        _cpu_guard_status_command,
        _failed_pair_terminal_result,
        _load_runtime_snapshot,
        _resource_contract_identity,
        _validate_cpu_guard_acquire_evidence,
        _validate_cpu_guard_release_evidence,
        _load_campaign,
        _order_pairs,
        _repository_root,
        verify_campaign_inputs,
    )
except ImportError:  # pragma: no cover - direct execution
    import resources  # type: ignore
    from observed_codex import code_mode_host_launch_failure  # type: ignore
    from common import (  # type: ignore
        MeasurementError,
        canonical_digest,
        manifest_for_tree,
        read_object,
        resolved_regular_file,
        sha256_file,
        utc_now,
    )
    from run_attempt import (  # type: ignore
        _task_metadata,
        candidate_loc,
        proof_loc,
        render_effective_prompt,
    )
    from run_benchmark import (  # type: ignore
        CAMPAIGN_KIND,
        CPU_GUARD_ACQUIRE_INTENT_KIND,
        CPU_GUARD_IDLE_SAMPLE_SECONDS,
        CPU_GUARD_MAXIMUM_BUSY_PERCENT,
        CPU_GUARD_FRONTEND_SOURCE_RELATIVE,
        CPU_GUARD_HOST_PATH,
        CPU_GUARD_PATH,
        CPU_GUARD_RECOVERY_KIND,
        CPU_GUARD_RECOVERY_REQUEST_KIND,
        CPU_GUARD_SOURCE_RELATIVE,
        CPU_GUARD_STATUS_KIND,
        PAIR_KIND,
        _CPU_GUARD_LEASE_RE,
        _artifact_path,
        _condition_attempt_command,
        _condition_worker_command,
        _cpu_guard_acquire_command,
        _cpu_guard_launch_command,
        _cpu_guard_release_command,
        _cpu_guard_status_command,
        _failed_pair_terminal_result,
        _load_runtime_snapshot,
        _resource_contract_identity,
        _validate_cpu_guard_acquire_evidence,
        _validate_cpu_guard_release_evidence,
        _load_campaign,
        _order_pairs,
        _repository_root,
        verify_campaign_inputs,
    )


STOP_DEADLINE_TOLERANCE_NS = 2_000_000_000
PROCESS_TEARDOWN_GRACE_NS = 30_000_000_000
ATTEMPT_FINALIZATION_GRACE_NS = 120_000_000_000

PROVIDER_CONFIG_OVERRIDES = (
    'model="gpt-6-sol"',
    'model_reasoning_effort="xhigh"',
    'approval_policy="never"',
    'sandbox_mode="danger-full-access"',
    'history.persistence="none"',
    "memories.use_memories=false",
    "memories.generate_memories=false",
)

PROVIDER_DISABLED_FEATURES = (
    "apps",
    "browser_use",
    "computer_use",
    "external_agent_memory_import",
    "goals",
    "image_generation",
    "memories",
    "multi_agent",
    "plugins",
    "remote_plugin",
    "skill_search",
    "standalone_web_search",
)


def _verify_self_hash(value: Mapping[str, Any], label: str) -> None:
    stored = value.get("record_sha256")
    payload = dict(value)
    payload.pop("record_sha256", None)
    if not isinstance(stored, str) or stored != canonical_digest(payload):
        raise MeasurementError(f"{label} has an invalid self-hash")


def _resolve_artifact(
    root: Path, descriptor: Mapping[str, Any], label: str
) -> Path:
    relative = descriptor.get("path")
    expected_bytes = descriptor.get("bytes")
    expected_sha = descriptor.get("sha256")
    if (
        not isinstance(relative, str)
        or not isinstance(expected_bytes, int)
        or not isinstance(expected_sha, str)
    ):
        raise MeasurementError(f"{label} has an invalid artifact descriptor")
    path = resolved_regular_file(root / relative, label=label)
    try:
        path.relative_to(root.resolve())
    except ValueError as error:
        raise MeasurementError(f"{label} escapes its result root") from error
    if path.stat().st_size != expected_bytes or sha256_file(path) != expected_sha:
        raise MeasurementError(f"{label} bytes or digest changed: {path}")
    return path


def _jsonl_records(path: Path, label: str, *, require_nonempty: bool) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as error:
        raise MeasurementError(f"cannot read {label}: {error}") from error
    for line_number, line in enumerate(lines, start=1):
        if not line:
            raise MeasurementError(f"{label} has a blank JSONL line {line_number}")
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise MeasurementError(
                f"{label} has invalid JSON on line {line_number}"
            ) from error
        if not isinstance(value, dict):
            raise MeasurementError(f"{label} line {line_number} is not an object")
        records.append(value)
    if require_nonempty and not records:
        raise MeasurementError(f"{label} is empty")
    return records


def _cgroup_integer_map(value: Any, *, label: str) -> dict[str, int]:
    """Parse kernel ``key integer`` telemetry without accepting free-form text."""

    if not isinstance(value, str) or not value:
        raise MeasurementError(f"{label} is missing")
    parsed: dict[str, int] = {}
    for line in value.splitlines():
        fields = line.split()
        if (
            len(fields) != 2
            or re.fullmatch(r"[a-z][a-z0-9_]*", fields[0]) is None
            or re.fullmatch(r"[0-9]+", fields[1]) is None
            or fields[0] in parsed
        ):
            raise MeasurementError(f"{label} is malformed")
        parsed[fields[0]] = int(fields[1])
    if not parsed:
        raise MeasurementError(f"{label} is empty")
    return parsed


_USAGE_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)


def _recompute_raw_usage(protocol: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    responses: dict[str, dict[str, Any]] = {}
    order: list[str] = []
    duplicates = 0
    totals = {field: 0 for field in _USAGE_FIELDS}
    for item in protocol:
        if item.get("direction") != "app_server_to_adapter":
            continue
        message = item.get("message")
        if not isinstance(message, Mapping) or message.get("method") != "rawResponse/completed":
            continue
        params = message.get("params")
        if not isinstance(params, Mapping):
            raise MeasurementError("rawResponse/completed params are malformed")
        identities = (
            params.get("responseId"),
            params.get("threadId"),
            params.get("turnId"),
        )
        if any(not isinstance(value, str) or not value for value in identities):
            raise MeasurementError("rawResponse/completed identity is malformed")
        raw = params.get("usage")
        if not isinstance(raw, Mapping):
            raise MeasurementError("rawResponse/completed usage is absent")
        names = {
            "input_tokens": "inputTokens",
            "cached_input_tokens": "cachedInputTokens",
            "cache_write_input_tokens": "cacheWriteInputTokens",
            "output_tokens": "outputTokens",
            "reasoning_output_tokens": "reasoningOutputTokens",
            "total_tokens": "totalTokens",
        }
        usage: dict[str, int] = {}
        for normalized, wire in names.items():
            value = raw.get(wire, 0 if wire == "cacheWriteInputTokens" else None)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise MeasurementError("rawResponse/completed has an invalid token count")
            usage[normalized] = value
        if (
            usage["cached_input_tokens"] > usage["input_tokens"]
            or usage["cache_write_input_tokens"] > usage["input_tokens"]
            or usage["reasoning_output_tokens"] > usage["output_tokens"]
            or usage["total_tokens"]
            != usage["input_tokens"] + usage["output_tokens"]
        ):
            raise MeasurementError("rawResponse/completed token totals are inconsistent")
        response_id, thread_id, turn_id = identities
        response = {
            "response_id": response_id,
            "thread_id": thread_id,
            "turn_id": turn_id,
            "usage": usage,
        }
        prior = responses.get(str(response_id))
        if prior is not None:
            if prior != response:
                raise MeasurementError("raw response id was reused inconsistently")
            duplicates += 1
            continue
        responses[str(response_id)] = response
        order.append(str(response_id))
        for field in _USAGE_FIELDS:
            totals[field] += usage[field]
    return {
        "measurement_source": "codex_app_server_rawResponse/completed",
        "scope": "all_observed_unique_completed_responses",
        "limit_enforced": False,
        "input_includes_cached": True,
        "response_count": len(order),
        "duplicate_event_count": duplicates,
        "response_ids": order,
        **totals,
    }


def _reconstruct_root_lifecycle(
    protocol: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Reconstruct and cross-bind the one adapter-created root prompt turn."""

    wire: list[tuple[int, Mapping[str, Any], Mapping[str, Any]]] = []
    for index, record in enumerate(protocol):
        if record.get("record_type") != "app_server_protocol":
            continue
        message = record.get("message")
        if not isinstance(message, Mapping):
            raise MeasurementError("app-server lifecycle record has no message")
        wire.append((index, record, message))

    def request(method: str) -> tuple[int, Mapping[str, Any], Mapping[str, Any]]:
        matches = [
            item
            for item in wire
            if item[1].get("direction") == "adapter_to_app_server"
            and item[2].get("method") == method
        ]
        if len(matches) != 1:
            raise MeasurementError(f"root lifecycle lacks exactly one {method} request")
        index, record, message = matches[0]
        request_id = message.get("id")
        params = message.get("params")
        if (
            not isinstance(request_id, int)
            or isinstance(request_id, bool)
            or not isinstance(params, Mapping)
        ):
            raise MeasurementError(f"root lifecycle has malformed {method} request")
        return index, record, message

    def response(
        request_index: int, request_message: Mapping[str, Any], method: str
    ) -> tuple[int, Mapping[str, Any]]:
        request_id = request_message["id"]
        matches = [
            (index, message)
            for index, record, message in wire
            if record.get("direction") == "app_server_to_adapter"
            and message.get("id") == request_id
            and "method" not in message
        ]
        if len(matches) != 1:
            raise MeasurementError(f"root lifecycle lacks exactly one {method} response")
        index, message = matches[0]
        if (
            index <= request_index
            or message.get("error") is not None
            or not isinstance(message.get("result"), Mapping)
        ):
            raise MeasurementError(f"root lifecycle has malformed {method} response")
        return index, message["result"]

    thread_request_index, _, thread_request = request("thread/start")
    expected_thread_params = {
        "approvalPolicy": "never",
        "cwd": "/workspace",
        "ephemeral": False,
        "experimentalRawEvents": True,
        "historyMode": "legacy",
        "model": "gpt-6-sol",
        "sandbox": "danger-full-access",
    }
    if (
        thread_request.get("id") != 2
        or thread_request.get("params") != expected_thread_params
    ):
        raise MeasurementError("root lifecycle thread/start configuration is wrong")
    thread_response_index, thread_result = response(
        thread_request_index, thread_request, "thread/start"
    )
    thread = thread_result.get("thread")
    root_thread_id = (
        thread.get("id")
        if isinstance(thread, Mapping)
        else thread_result.get("threadId")
    )
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise MeasurementError("root lifecycle thread/start response has no thread id")

    turn_request_index, turn_request_record, turn_request = request("turn/start")
    if (
        turn_request.get("id") != 3
        or turn_request_index <= thread_response_index
        or turn_request.get("id") == thread_request.get("id")
    ):
        raise MeasurementError("root lifecycle turn/start request is out of order")
    turn_params = turn_request.get("params")
    if (
        not isinstance(turn_params, Mapping)
        or turn_params.get("threadId") != root_thread_id
    ):
        raise MeasurementError("root lifecycle turn/start targets another thread")
    turn_response_index, turn_result = response(
        turn_request_index, turn_request, "turn/start"
    )
    turn = turn_result.get("turn")
    root_turn_id = (
        turn.get("id") if isinstance(turn, Mapping) else turn_result.get("turnId")
    )
    if not isinstance(root_turn_id, str) or not root_turn_id:
        raise MeasurementError("root lifecycle turn/start response has no turn id")

    root_thread_notifications: list[int] = []
    starts: dict[tuple[str, str], int] = {}
    completions: dict[tuple[str, str], tuple[int, str]] = {}
    reachable_root_states: set[tuple[str | None, str | None, bool]] = {
        (None, None, False)
    }
    observed_root_turn_id: str | None = None
    observed_root_status: str | None = None
    turn_response_seen = False

    def bind_root_turn(candidate: str) -> None:
        nonlocal observed_root_turn_id
        if candidate != root_turn_id or observed_root_turn_id not in (None, candidate):
            raise MeasurementError("root lifecycle observed inconsistent root turn ids")
        observed_root_turn_id = candidate

    for index, _, message in wire:
        if index == turn_response_index:
            bind_root_turn(root_turn_id)
            turn_response_seen = True
            reachable_root_states.add(
                (observed_root_turn_id, observed_root_status, turn_response_seen)
            )
        method = message.get("method")
        if method not in ("thread/started", "turn/started", "turn/completed"):
            continue
        params = message.get("params")
        if not isinstance(params, Mapping):
            raise MeasurementError(f"root lifecycle has malformed {method} params")
        if method == "thread/started":
            thread_record = params.get("thread")
            if not isinstance(thread_record, Mapping):
                raise MeasurementError("root lifecycle has malformed thread/started")
            candidate = thread_record.get("id")
            if not isinstance(candidate, str) or not candidate:
                raise MeasurementError("root lifecycle thread/started has no thread id")
            parent = thread_record.get("parentThreadId")
            forked_from = thread_record.get("forkedFromId")
            rooted = parent is None and forked_from is None
            if rooted:
                if candidate != root_thread_id:
                    raise MeasurementError(
                        "root lifecycle thread/start notification disagrees with its response"
                    )
                root_thread_notifications.append(index)
            else:
                raise MeasurementError("single-agent protocol emitted a child thread")
            continue

        event_thread_id = params.get("threadId")
        turn_record = params.get("turn")
        event_turn_id = (
            turn_record.get("id") if isinstance(turn_record, Mapping) else None
        )
        if (
            not isinstance(event_thread_id, str)
            or not event_thread_id
            or not isinstance(turn_record, Mapping)
            or not isinstance(event_turn_id, str)
            or not event_turn_id
        ):
            raise MeasurementError(f"root lifecycle has malformed {method}")
        if event_thread_id != root_thread_id:
            raise MeasurementError("single-agent protocol emitted a child turn")
        key = (event_thread_id, event_turn_id)
        if method == "turn/started":
            if turn_record.get("status") != "inProgress" or key in starts:
                raise MeasurementError("root lifecycle has invalid or duplicate turn/started")
            starts[key] = index
            if event_thread_id == root_thread_id:
                bind_root_turn(event_turn_id)
                reachable_root_states.add(
                    (observed_root_turn_id, observed_root_status, turn_response_seen)
                )
            continue
        status = turn_record.get("status")
        if status not in ("completed", "failed", "interrupted"):
            raise MeasurementError("root lifecycle has invalid terminal turn status")
        if key not in starts or starts[key] >= index or key in completions:
            raise MeasurementError(
                "root lifecycle has unmatched or duplicate turn/completed"
            )
        completions[key] = (index, str(status))
        if event_thread_id == root_thread_id:
            bind_root_turn(event_turn_id)
            if observed_root_status is not None:
                raise MeasurementError("root lifecycle has duplicate root turn/completed")
            observed_root_status = str(status)
            reachable_root_states.add(
                (observed_root_turn_id, observed_root_status, turn_response_seen)
            )

    if (
        len(root_thread_notifications) != 1
        or root_thread_notifications[0] <= thread_request_index
    ):
        raise MeasurementError(
            "root lifecycle lacks exactly one matching thread/started notification"
        )
    root_key = (root_thread_id, root_turn_id)
    if set(key for key in starts if key[0] == root_thread_id) != {root_key}:
        raise MeasurementError("root lifecycle has an inconsistent root turn/started")
    if starts[root_key] <= turn_request_index:
        raise MeasurementError("root lifecycle root turn/started predates its request")
    root_completion = completions.get(root_key)
    if any(key[0] == root_thread_id and key != root_key for key in completions):
        raise MeasurementError("root lifecycle has an inconsistent root turn/completed")
    root_terminal_status = root_completion[1] if root_completion is not None else None
    root_turn_completed_record = (
        protocol[root_completion[0]] if root_completion is not None else None
    )

    return {
        "root_thread_id": root_thread_id,
        "root_turn_id": root_turn_id,
        "root_terminal_status": root_terminal_status,
        "turn_start_record": turn_request_record,
        "turn_response_seen": turn_response_seen,
        "root_turn_started_seen": root_key in starts,
        "root_turn_completed_seen": root_completion is not None,
        "root_turn_completed_record": root_turn_completed_record,
        "reachable_root_states": reachable_root_states,
    }


def _verify_single_agent_trace(
    protocol: Sequence[Mapping[str, Any]], root_thread_id: str
) -> None:
    """Reject any provider activity outside the one locked root thread."""

    for record in protocol:
        if record.get("record_type") != "app_server_protocol":
            continue
        message = record.get("message")
        if not isinstance(message, Mapping):
            raise MeasurementError("single-agent protocol record has no message")
        params = message.get("params")
        if not isinstance(params, Mapping):
            continue
        thread_id = params.get("threadId")
        if thread_id is not None and thread_id != root_thread_id:
            raise MeasurementError("single-agent protocol contains non-root activity")
        item = params.get("item")
        if isinstance(item, Mapping) and item.get("name") in {
            "spawn_agent",
            "send_message",
            "followup_task",
            "interrupt_agent",
            "list_agents",
            "wait_agent",
        }:
            raise MeasurementError("single-agent protocol contains a collaboration call")


def _mount_table(argv: Sequence[Any]) -> dict[str, tuple[str, str]]:
    unsupported_mount_options = {
        "--bind-try",
        "--ro-bind-try",
        "--dev-bind",
        "--dev-bind-try",
        "--bind-data",
        "--ro-bind-data",
        "--file",
        "--mqueue",
        "--overlay-src",
        "--overlay",
        "--ro-overlay",
        "--tmp-overlay",
        "--remount-ro",
        "--symlink",
    }
    single_destination_operations = {"--proc", "--dev", "--tmpfs", "--dir"}
    for value in argv:
        if not isinstance(value, str):
            raise MeasurementError("bubblewrap argv contains a non-string argument")
        if value in unsupported_mount_options:
            raise MeasurementError(f"unexpected Bubblewrap mount option: {value}")
        if any(
            value.startswith(option + "=")
            for option in (
                "--bind",
                "--ro-bind",
                *sorted(single_destination_operations),
                *sorted(unsupported_mount_options),
            )
        ):
            raise MeasurementError("Bubblewrap mount options must use separate arguments")
    table: dict[str, tuple[str, str]] = {}
    index = 0
    while index < len(argv):
        value = argv[index]
        if value in ("--ro-bind", "--bind"):
            if index + 2 >= len(argv):
                raise MeasurementError("bubblewrap mount argv is truncated")
            source = argv[index + 1]
            destination = argv[index + 2]
            if not isinstance(source, str) or not isinstance(destination, str):
                raise MeasurementError("bubblewrap mount argv is malformed")
            if destination in table:
                raise MeasurementError("bubblewrap mount destination is repeated")
            table[destination] = (str(value), source)
            index += 3
            continue
        if value in single_destination_operations:
            if index + 1 >= len(argv) or not isinstance(argv[index + 1], str):
                raise MeasurementError("bubblewrap mount argv is truncated")
            destination = argv[index + 1]
            if destination in table:
                raise MeasurementError("bubblewrap mount destination is repeated")
            table[destination] = (str(value), "")
            index += 2
            continue
        index += 1
    return table


def _authenticated_code_mode_host(
    campaign: Mapping[str, Any],
) -> tuple[Path, Mapping[str, Any]]:
    """Authenticate the companion executable required by Codex code-mode tools."""

    agent = campaign.get("agent")
    if not isinstance(agent, Mapping):
        raise MeasurementError("campaign lacks Codex agent identity")
    descriptor = agent.get("code_mode_host")
    if not isinstance(descriptor, Mapping):
        raise MeasurementError("campaign lacks Codex code-mode host identity")
    path_value = descriptor.get("path")
    codex_value = agent.get("path")
    if (
        set(descriptor) != {"path", "bytes", "sha256", "mode"}
        or not isinstance(path_value, str)
        or not Path(path_value).is_absolute()
        or not isinstance(codex_value, str)
        or not Path(codex_value).is_absolute()
    ):
        raise MeasurementError("campaign Codex code-mode host descriptor is invalid")
    code_mode_host = resolved_regular_file(
        Path(path_value), label="Codex code-mode host"
    )
    codex = resolved_regular_file(Path(codex_value), label="Codex executable")
    status = code_mode_host.stat()
    mode = stat.S_IMODE(status.st_mode)
    expected_descriptor = {
        "path": str(code_mode_host),
        "bytes": status.st_size,
        "sha256": sha256_file(code_mode_host),
        "mode": oct(mode & 0o777),
    }
    if (
        dict(descriptor) != expected_descriptor
        or code_mode_host.parent != codex.parent
        or code_mode_host.name != "codex-code-mode-host"
        or mode & 0o7000
        or not os.access(code_mode_host, os.X_OK)
    ):
        raise MeasurementError("campaign Codex code-mode host identity is invalid")
    return code_mode_host, descriptor


def _paper_shared_olean_root(
    attempt_root: Path, campaign: Mapping[str, Any]
) -> Path:
    paper_id = attempt_root.parent.name.split("-", 1)[0]
    if re.fullmatch(r"P[0-9]{2,}", paper_id) is None:
        raise MeasurementError("attempt has no canonical paper id")
    return (Path(str(campaign["shared_olean_root"])) / paper_id).resolve()


def _expected_provider_mounts(
    *,
    attempt_root: Path,
    results_root: Path,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    condition: str,
    actual: Mapping[str, tuple[str, str]],
) -> dict[str, tuple[str, str]]:
    """Reconstruct every host bind visible to the provider-side sandbox."""

    agent = campaign.get("agent")
    runtime_tools = campaign.get("runtime_tools")
    if not isinstance(agent, Mapping) or not isinstance(runtime_tools, Mapping):
        raise MeasurementError("campaign lacks provider mount identity")
    code_mode_host, _ = _authenticated_code_mode_host(campaign)
    bubblewrap = runtime_tools.get("bubblewrap")
    if not isinstance(bubblewrap, Mapping):
        raise MeasurementError("campaign lacks provider Bubblewrap identity")

    workspace = (attempt_root / "workspace").resolve()
    offline_shell = _artifact_path(results_root, campaign["offline_shell"])
    toolchain = Path(str(campaign["toolchain_root"])).resolve()
    shared_olean = _paper_shared_olean_root(attempt_root, campaign)
    packages_root = Path(
        str(runtime["condition_l"]["derived_packages_root"])
    ).resolve()

    state_binding = actual.get("/sandbox/agent")
    if not isinstance(state_binding, tuple) or len(state_binding) != 2:
        raise MeasurementError("provider sandbox lacks its private Codex home mount")
    state_mode, state_source_raw = state_binding
    state_source = Path(state_source_raw)
    if (
        state_mode != "--bind"
        or not state_source.is_absolute()
        or ".." in state_source.parts
        or state_source.name != "home"
        or state_source.parent.parent != attempt_root / "codex_state"
        or re.fullmatch(r"highambench-observed-[A-Za-z0-9_-]+", state_source.parent.name)
        is None
    ):
        raise MeasurementError("provider Codex home mount has an invalid source")

    marker_destinations = sorted(
        destination
        for destination in actual
        if destination.startswith("/run/highambench-audit/")
    )
    if len(marker_destinations) != 1:
        raise MeasurementError("provider sandbox must have one network-audit marker mount")
    marker_destination = marker_destinations[0]
    marker_mode, marker_source_raw = actual[marker_destination]
    marker_source = Path(marker_source_raw)
    marker_name = Path(marker_destination).name
    if (
        marker_mode != "--bind"
        or not marker_source.is_absolute()
        or ".." in marker_source.parts
        or marker_source.parent != state_source.parent
        or marker_source.name != marker_name
        or re.fullmatch(r"network-audit-[A-Za-z0-9_-]+", marker_name) is None
    ):
        raise MeasurementError("provider network-audit marker mount is invalid")

    expected: dict[str, tuple[str, str]] = {
        "/usr": ("--ro-bind", "/usr"),
        "/bin": ("--ro-bind", "/bin"),
        "/lib": ("--ro-bind", "/lib"),
        "/lib64": ("--ro-bind", "/lib64"),
        "/etc": ("--ro-bind", "/etc"),
        "/proc": ("--proc", ""),
        "/dev": ("--dev", ""),
        "/tmp": ("--bind", str(state_source.parent / "tmp")),
        "/run": ("--dir", ""),
        "/run/systemd": ("--dir", ""),
        "/run/highambench-audit": ("--dir", ""),
        "/sandbox": ("--dir", ""),
        "/sandbox/agent": ("--bind", str(state_source)),
        "/workspace": ("--bind", str(workspace)),
        marker_destination: ("--bind", str(marker_source)),
        "/workspace/task": ("--ro-bind", str(workspace / "task")),
        "/shared": ("--ro-bind", str(workspace / "task" / "shared")),
        "/shared-olean": ("--ro-bind", str(shared_olean)),
        "/codex": ("--ro-bind", str(Path(str(agent["path"])).resolve())),
        "/codex-code-mode-host": ("--ro-bind", str(code_mode_host)),
        "/offline-shell": ("--ro-bind", str(offline_shell)),
        "/lean": ("--ro-bind", str(toolchain)),
        "/packages": ("--dir", ""),
    }
    if "/run/systemd/resolve" in actual:
        expected["/run/systemd/resolve"] = (
            "--ro-bind",
            str(Path("/run/systemd/resolve").resolve()),
        )
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if package.is_dir() and not package.is_symlink():
            expected[f"/packages/{package.name}"] = (
                "--ro-bind",
                str(package.resolve()),
            )

    expected_library = _expected_library_record(runtime, condition)
    if expected_library is not None:
        expected.update(
            {
                "/library": ("--dir", ""),
                "/library/docs": ("--dir", ""),
                "/library/NumStability": (
                    "--ro-bind",
                    str(expected_library["source"]),
                ),
                "/library/NumStability.lean": (
                    "--ro-bind",
                    str(expected_library["root_file"]),
                ),
                "/library/docs/LIBRARY_LOOKUP.md": (
                    "--ro-bind",
                    str(expected_library["lookup_guide"]),
                ),
                "/library-olean": (
                    "--ro-bind",
                    str(expected_library["olean"]),
                ),
            }
        )
    return expected


def _append_provider_mount(
    command: list[str],
    mounts: Mapping[str, tuple[str, str]],
    destination: str,
) -> None:
    operation, source = mounts[destination]
    if operation in ("--bind", "--ro-bind"):
        command.extend((operation, source, destination))
    else:
        command.extend((operation, destination))


def _expected_provider_bubblewrap_argv(
    *,
    attempt_root: Path,
    results_root: Path,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    condition: str,
    actual: Sequence[Any],
) -> list[str]:
    """Reconstruct the exact ordered provider process command.

    The temporary Codex-home and network-marker names are randomized by the
    adapter.  Their already-authenticated mount sources are the only inferred
    values; every operation, ordering decision, environment value, executable,
    and Codex feature/configuration argument is fixed by the campaign runner.
    """

    mounts = _mount_table(actual)
    expected_mounts = _expected_provider_mounts(
        attempt_root=attempt_root,
        results_root=results_root,
        campaign=campaign,
        runtime=runtime,
        condition=condition,
        actual=mounts,
    )
    runtime_tools = campaign.get("runtime_tools")
    if not isinstance(runtime_tools, Mapping) or not isinstance(
        runtime_tools.get("bubblewrap"), Mapping
    ):
        raise MeasurementError("campaign lacks provider Bubblewrap identity")
    bubblewrap = str(
        Path(str(runtime_tools["bubblewrap"]["path"])).resolve()
    )
    command = [bubblewrap, "--unshare-all", "--share-net", "--die-with-parent"]
    for destination in ("/usr", "/bin", "/lib", "/lib64", "/etc"):
        _append_provider_mount(command, expected_mounts, destination)
    for destination in (
        "/proc",
        "/dev",
        "/tmp",
        "/run",
        "/run/systemd",
        "/run/highambench-audit",
    ):
        _append_provider_mount(command, expected_mounts, destination)
    if "/run/systemd/resolve" in expected_mounts:
        _append_provider_mount(command, expected_mounts, "/run/systemd/resolve")

    _append_provider_mount(command, expected_mounts, "/sandbox")
    _append_provider_mount(command, expected_mounts, "/sandbox/agent")
    _append_provider_mount(command, expected_mounts, "/workspace")
    marker_destinations = sorted(
        destination
        for destination in expected_mounts
        if destination.startswith("/run/highambench-audit/")
    )
    if len(marker_destinations) != 1:
        raise MeasurementError("provider sandbox lacks one audit-marker mount")
    marker_destination = marker_destinations[0]
    _append_provider_mount(command, expected_mounts, marker_destination)
    for destination in (
        "/workspace/task",
        "/shared",
        "/shared-olean",
        "/codex",
        "/codex-code-mode-host",
        "/offline-shell",
        "/lean",
        "/packages",
    ):
        _append_provider_mount(command, expected_mounts, destination)

    package_destinations = sorted(
        destination
        for destination in expected_mounts
        if destination.startswith("/packages/")
    )
    for destination in package_destinations:
        _append_provider_mount(command, expected_mounts, destination)

    if condition == "L":
        for destination in (
            "/library",
            "/library/docs",
            "/library/NumStability",
            "/library/NumStability.lean",
            "/library/docs/LIBRARY_LOOKUP.md",
            "/library-olean",
        ):
            _append_provider_mount(command, expected_mounts, destination)

    condition_l = runtime.get("condition_l")
    if not isinstance(condition_l, Mapping):
        raise MeasurementError("runtime lacks provider package identity")
    packages_root = Path(str(condition_l["derived_packages_root"])).resolve()
    lean_paths = ["/shared-olean", "/shared"]
    if condition == "L":
        lean_paths.append("/library-olean")
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if not package.is_dir() or package.is_symlink():
            continue
        build = package / ".lake" / "build" / "lib" / "lean"
        if build.is_dir():
            lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    lean_paths.extend(("/lean/lib/lean", "/workspace"))
    command.extend(
        (
            "--setenv",
            "PATH",
            "/lean/bin:/usr/bin:/bin",
            "--setenv",
            "HOME",
            "/sandbox/agent",
            "--setenv",
            "CODEX_HOME",
            "/sandbox/agent/.codex",
            "--setenv",
            "TMPDIR",
            "/tmp",
            "--setenv",
            "LEAN_PATH",
            ":".join(lean_paths),
            "--setenv",
            "SHELL",
            "/offline-shell",
            "--setenv",
            "HIGHAMBENCH_NETWORK_VIOLATION_MARKER",
            marker_destination,
            "--chdir",
            "/workspace",
            "/codex",
            "app-server",
            "--stdio",
            "--strict-config",
        )
    )
    for config in PROVIDER_CONFIG_OVERRIDES:
        command.extend(("--config", config))
    for feature in PROVIDER_DISABLED_FEATURES:
        command.extend(("--disable", feature))
    return command


def _expected_library_record(
    runtime: Mapping[str, Any], condition: str
) -> dict[str, Any] | None:
    if condition == "N":
        return None
    source = runtime["source"]["numstability"]
    condition_l = runtime["condition_l"]
    root = Path(str(source["checkout"])).resolve()
    olean = Path(str(condition_l["lean_build_lib"])).resolve()
    return {
        "root": str(root),
        "pristine_source_checkout_root": str(root),
        "commit": source["commit"],
        "source": str(root / "NumStability"),
        "root_file": str(root / "NumStability.lean"),
        "lookup_guide": str(root / "docs/LIBRARY_LOOKUP.md"),
        "olean": str(olean),
        "derived_olean_root": str(olean),
        "detached_checkout_verified": True,
        "pristine_worktree_verified_including_untracked_and_ignored": True,
        "symlink_escape_rejected": True,
        "git_optional_locks": "0",
        "source_and_olean_roots_separate": True,
        "derived_olean_tree_non_writable": True,
        "mounted_read_only": True,
    }


def _expected_adapter_command(
    benchmark_root: Path,
    results_root: Path,
    attempt_root: Path,
    condition: str,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    artifacts: Mapping[str, Path],
) -> list[str]:
    agent = campaign.get("agent")
    auth = campaign.get("auth")
    runtime_tools = campaign.get("runtime_tools")
    if not all(isinstance(item, Mapping) for item in (agent, auth, runtime_tools)):
        raise MeasurementError("campaign lacks adapter command identity")
    code_mode_host, _ = _authenticated_code_mode_host(campaign)
    python = runtime_tools.get("python")
    bubblewrap = runtime_tools.get("bubblewrap")
    if not isinstance(python, Mapping) or not isinstance(bubblewrap, Mapping):
        raise MeasurementError("campaign lacks Python/bubblewrap identity")
    workspace = attempt_root / "workspace"
    condition_l = runtime["condition_l"]
    packages_root = Path(str(condition_l["derived_packages_root"])).resolve()
    command = [
        str(python["path"]),
        str((benchmark_root / "scripts/observed_codex.py").resolve()),
        "--condition",
        condition,
        "--workspace",
        str(workspace.resolve()),
        "--controlled-relative",
        "task",
        "--shared-source-root",
        str((workspace / "task/shared").resolve()),
        "--shared-olean-root",
        str(_paper_shared_olean_root(attempt_root, campaign)),
        "--prompt-file",
        str(artifacts["effective_prompt"]),
        "--audit-output",
        str(artifacts["protocol"]),
        "--diagnostics-output",
        str(artifacts["diagnostics"]),
        "--summary-output",
        str(artifacts["agent_summary"]),
        "--prompt-start-output",
        str(artifacts["prompt_start"]),
        "--stop-reason-file",
        str(artifacts["stop_reason"]),
        "--codex",
        str(Path(str(agent["path"])).resolve()),
        "--code-mode-host",
        str(code_mode_host),
        "--auth-file",
        str(Path(str(auth["path"])).resolve()),
        "--offline-shell",
        str(_artifact_path(results_root, campaign["offline_shell"])),
        "--bwrap",
        str(Path(str(bubblewrap["path"])).resolve()),
        "--toolchain-root",
        str(Path(str(campaign["toolchain_root"])).resolve()),
        "--packages-root",
        str(packages_root),
        "--state-parent",
        str(attempt_root / "codex_state"),
        "--model",
        "gpt-6-sol",
        "--reasoning-effort",
        "xhigh",
    ]
    if condition == "L":
        command.extend(
            [
                "--library-runtime-root",
                str(Path(str(runtime["source"]["numstability"]["checkout"])).resolve()),
                "--library-runtime-commit",
                str(runtime["source"]["numstability"]["commit"]),
                "--library-olean-root",
                str(Path(str(condition_l["lean_build_lib"])).resolve()),
            ]
        )
    return command


def _same_executable_target(actual: object, expected: object) -> bool:
    """Allow an invoked symlink only when it resolves to the authorized binary."""

    if (
        not isinstance(actual, str)
        or not actual
        or not isinstance(expected, str)
        or not expected
        or not Path(actual).is_absolute()
        or not Path(expected).is_absolute()
    ):
        return False
    try:
        actual_path = Path(actual).resolve(strict=True)
        expected_path = Path(expected).resolve(strict=True)
    except (OSError, RuntimeError):
        return False
    return (
        actual_path == expected_path
        and actual_path.is_file()
        and not actual_path.is_symlink()
    )


def _strict_command_options(
    command: Sequence[str], *, label: str
) -> dict[str, str]:
    tail = list(command[3:])
    if len(tail) % 2:
        raise MeasurementError(f"{label} has a truncated option")
    options: dict[str, str] = {}
    for position in range(0, len(tail), 2):
        option = tail[position]
        value = tail[position + 1]
        if (
            re.fullmatch(r"--[a-z][a-z0-9-]*", option) is None
            or "=" in option
            or option == "--"
            or not value
            or value.startswith("--")
        ):
            raise MeasurementError(f"{label} has malformed option arguments")
        if option in options:
            raise MeasurementError(f"{label} repeats option {option}")
        options[option] = value
    return options


def _validation_command_set(
    *,
    benchmark_root: Path,
    attempt_root: Path,
    task_info: Mapping[str, Any],
    condition: str,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    command: Sequence[str],
    field: str,
) -> dict[str, list[str]]:
    """Infer only randomized validator names, then reconstruct all three argv."""

    runtime_tools = campaign.get("runtime_tools")
    if not isinstance(runtime_tools, Mapping):
        raise MeasurementError("campaign lacks validation runtime-tool identity")
    python = runtime_tools.get("python")
    bubblewrap = runtime_tools.get("bubblewrap")
    if not isinstance(python, Mapping) or not isinstance(bubblewrap, Mapping):
        raise MeasurementError("campaign lacks validation Python/bubblewrap identity")
    expected_python = Path(str(python.get("path"))).resolve()
    expected_bwrap = str(Path(str(bubblewrap.get("path"))).resolve())
    expected_adapter = str((benchmark_root / "tools/lean_isolated.py").resolve())
    label = f"condition {condition} validation {field} command"
    if (
        len(command) < 3
        or not all(isinstance(argument, str) and argument for argument in command)
        or Path(command[0]).resolve() != expected_python
        or command[1] != expected_adapter
        or command[2] not in ("olean", "audit")
    ):
        raise MeasurementError(f"{label} is malformed")
    options = _strict_command_options(command, label=label)
    if options.get("--bwrap") != expected_bwrap:
        raise MeasurementError(
            f"condition {condition} validation {field} Bubblewrap path differs from campaign"
        )
    workspace_raw = options.get("--workspace")
    source_raw = options.get("--source")
    if not isinstance(workspace_raw, str) or not isinstance(source_raw, str):
        raise MeasurementError(f"{label} lacks its hidden workspace/source")
    workspace = Path(workspace_raw)
    source = Path(source_raw)
    validator_parent = (attempt_root / "hidden" / "validator").resolve()
    if (
        not workspace.is_absolute()
        or ".." in workspace.parts
        or str(workspace) != workspace_raw
        or workspace.name != "project"
        or workspace.parent.parent != validator_parent
        or re.fullmatch(
            r"highambench-hidden-[A-Za-z0-9_-]+", workspace.parent.name
        )
        is None
        or not source.is_absolute()
        or ".." in source.parts
        or source.parent != workspace
        or str(source) != source_raw
    ):
        raise MeasurementError(f"{label} has an invalid hidden workspace/source")
    expected_prefix = (
        "VSCLReuseExpected_"
        if field == "expected_statement_compile"
        else "VSCLReuseChecked_"
    )
    source_match = re.fullmatch(
        re.escape(expected_prefix) + r"([0-9a-f]{32})\.lean", source.name
    )
    if source_match is None:
        raise MeasurementError(f"{label} has an invalid generated source name")
    generated_id = source_match.group(1)
    checked_source = workspace / f"VSCLReuseChecked_{generated_id}.lean"
    expected_source = workspace / f"VSCLReuseExpected_{generated_id}.lean"
    checked_module = f"VSCLReuseChecked_{generated_id}"
    expected_module = f"VSCLReuseExpected_{generated_id}"
    target_theorem = str(task_info["target_theorem"])
    target_prefix = target_theorem.rsplit(".", 1)
    expected_leaf = f"highamBenchExpected_{generated_id}"
    expected_theorem = (
        f"{target_prefix[0]}.{expected_leaf}"
        if len(target_prefix) == 2
        else expected_leaf
    )

    condition_l = runtime.get("condition_l")
    source_identity = runtime.get("source")
    if not isinstance(condition_l, Mapping) or not isinstance(source_identity, Mapping):
        raise MeasurementError("runtime lacks hidden validation dependencies")
    numstability = source_identity.get("numstability")
    if not isinstance(numstability, Mapping):
        raise MeasurementError("runtime lacks hidden NumStability identity")
    base = [
        command[0],
        expected_adapter,
        "{action}",
        "--condition",
        condition,
        "--workspace",
        str(workspace),
        "--toolchain-root",
        str(Path(str(campaign["toolchain_root"])).resolve()),
        "--packages-root",
        str(Path(str(condition_l["derived_packages_root"])).resolve()),
        "--shared-olean-root",
        str(_paper_shared_olean_root(attempt_root, campaign)),
        "--bwrap",
        expected_bwrap,
    ]
    if condition == "L":
        source_root = Path(str(numstability["checkout"])).resolve()
        base.extend(
            [
                "--library-source",
                str(source_root / "NumStability"),
                "--library-root-file",
                str(source_root / "NumStability.lean"),
                "--library-olean",
                str(Path(str(condition_l["lean_build_lib"])).resolve()),
            ]
        )

    def action_base(action: str) -> list[str]:
        return [action if value == "{action}" else value for value in base]

    compile_command = [*action_base("olean"), "--source", str(checked_source)]
    expected_compile_command = [
        *action_base("olean"),
        "--source",
        str(expected_source),
    ]
    audit_command = [
        *action_base("audit"),
        "--source",
        str(checked_source),
        "--audit-helper",
        str((benchmark_root / "tools" / "dependency_audit.lean").resolve()),
        "--submission-module",
        checked_module,
        "--target-theorem",
        target_theorem,
        "--expected-module",
        expected_module,
        "--expected-theorem",
        expected_theorem,
        "--local-modules-file",
        str(workspace / f".highambench-validator-local-modules-{generated_id}"),
    ]
    return {
        "compile": compile_command,
        "expected_statement_compile": expected_compile_command,
        "dependency_audit": audit_command,
    }


def _verify_validation_commands(
    benchmark_root: Path,
    attempt_root: Path,
    task_info: Mapping[str, Any],
    condition: str,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    validation_records: Sequence[Mapping[str, Any]],
) -> None:
    """Bind every hidden Lean invocation to its exact fixed validation inputs."""

    command_fields = (
        "compile",
        "expected_statement_compile",
        "dependency_audit",
    )
    for index, validation in enumerate(validation_records, start=1):
        present = [field for field in command_fields if validation.get(field) is not None]
        if validation.get("pass") is True and present != list(command_fields):
            raise MeasurementError(
                f"condition {condition} passing validation {index} lacks commands"
            )
        if "expected_statement_compile" in present and "compile" not in present:
            raise MeasurementError(
                f"condition {condition} validation {index} skipped candidate compilation"
            )
        if "dependency_audit" in present and present[:2] != list(command_fields[:2]):
            raise MeasurementError(
                f"condition {condition} validation {index} skipped a compile stage"
            )
        expected_set: dict[str, list[str]] | None = None
        for field in present:
            result = validation.get(field)
            command = result.get("command") if isinstance(result, Mapping) else None
            if not isinstance(command, list):
                raise MeasurementError(
                    f"condition {condition} validation {field} command is malformed"
                )
            reconstructed = _validation_command_set(
                benchmark_root=benchmark_root,
                attempt_root=attempt_root,
                task_info=task_info,
                condition=condition,
                campaign=campaign,
                runtime=runtime,
                command=command,
                field=field,
            )
            if expected_set is None:
                expected_set = reconstructed
            elif expected_set != reconstructed:
                raise MeasurementError(
                    f"condition {condition} validation {index} mixes hidden workspaces"
                )
            if command != reconstructed[field]:
                raise MeasurementError(
                    f"condition {condition} validation {field} command differs from "
                    "the fixed campaign validation command"
                )


def _verify_validation_result_semantics(
    benchmark_root: Path,
    task_info: Mapping[str, Any],
    condition: str,
    validation_records: Sequence[Mapping[str, Any]],
    *,
    expected_final_candidate_sha256: str | None,
) -> None:
    """Independently replay the non-plural validator's ordered return points."""

    controlled = read_object(
        benchmark_root
        / "metadata"
        / "controlled"
        / f"{task_info['task_id']}.json",
        kind="highambench-controlled-files",
    )
    controlled_files = controlled.get("files")
    if not isinstance(controlled_files, list) or not controlled_files:
        raise MeasurementError("validation controlled manifest is empty")
    controlled_paths = [
        item.get("path") if isinstance(item, Mapping) else None
        for item in controlled_files
    ]
    if not all(isinstance(path, str) and path for path in controlled_paths):
        raise MeasurementError("validation controlled manifest is malformed")
    # The measured runner intentionally does not stage the legacy agent prompt.  Its
    # descriptor remains in construction metadata only, so validator
    # checkpoints count the released task files rather than that descriptor.
    expected_controlled_files = sum(
        path != "agent_prompt.md" for path in controlled_paths
    )
    if expected_controlled_files < 1:
        raise MeasurementError("validation released controlled manifest is empty")
    target_theorem = str(task_info["target_theorem"])
    stage_fields = (
        "controlled_before",
        "candidate_inventory",
        "statement_check",
        "controlled_hidden",
        "compile",
        "controlled_after_compile",
        "expected_statement_compile",
        "controlled_after_expected_compile",
        "local_modules_side_channel",
        "controlled_after_audit",
        "dependency_audit",
        "semantic_statement_check",
    )
    required_fields = {
        "pass",
        "failure_code",
        "note",
        "condition",
        "target_theorem",
        "submission",
        "reject_workspace_local_module_imports",
        "controlled_before",
        "controlled_hidden",
        "controlled_after_compile",
        "controlled_after_expected_compile",
        "controlled_after_audit",
        "candidate_inventory",
        "static_findings",
        "statement_check",
        "semantic_statement_check",
        "compile",
        "expected_statement_compile",
        "local_modules_side_channel",
        "dependency_audit",
        "library_use",
        "library_declarations",
        "library_audit_complete",
        "candidate_sha256",
    }

    def checkpoint(raw: Any, *, label: str) -> bool:
        if not isinstance(raw, Mapping) or set(raw) != {
            "ok",
            "verified",
            "expected",
            "missing",
            "changed",
        }:
            raise MeasurementError(f"{label} controlled checkpoint is malformed")
        verified = raw.get("verified")
        missing = raw.get("missing")
        changed = raw.get("changed")
        if (
            type(raw.get("ok")) is not bool
            or type(verified) is not int
            or verified < 0
            or raw.get("expected") != expected_controlled_files
            or not isinstance(missing, list)
            or not all(isinstance(path, str) and path for path in missing)
            or not isinstance(changed, list)
            or not all(isinstance(item, Mapping) for item in changed)
            or verified + len(missing) + len(changed) != expected_controlled_files
            or raw.get("ok") is not (not missing and not changed)
        ):
            raise MeasurementError(f"{label} controlled checkpoint is inconsistent")
        return bool(raw["ok"])

    def command_result(raw: Any, *, label: str) -> Mapping[str, Any]:
        if not isinstance(raw, Mapping):
            raise MeasurementError(f"{label} command result is malformed")
        seconds = raw.get("seconds")
        exit_code = raw.get("exit_code")
        timed_out = raw.get("timed_out")
        system_error = raw.get("system_error")
        if (
            not isinstance(raw.get("command"), list)
            or not isinstance(raw.get("display"), str)
            or not isinstance(raw.get("output"), str)
            or raw.get("output_truncated") is not False
            or not isinstance(seconds, (int, float))
            or isinstance(seconds, bool)
            or seconds < 0
            or type(timed_out) is not bool
            or not (
                system_error is None
                or (isinstance(system_error, str) and bool(system_error))
            )
            or not (
                exit_code is None
                or (isinstance(exit_code, int) and not isinstance(exit_code, bool))
            )
        ):
            raise MeasurementError(f"{label} command result is malformed")
        if system_error is not None:
            consistent = (
                exit_code is None and timed_out is False and raw.get("output") == ""
            )
        elif timed_out:
            consistent = exit_code is None
        else:
            consistent = exit_code is not None
        if not consistent:
            raise MeasurementError(
                f"{label} exit code/timeout/system-error state is inconsistent"
            )
        return raw

    def classify_compile_failure(output: str) -> str:
        lowered = output.lower()
        syntax_or_elab_markers = (
            "unexpected token",
            "expected token",
            "unexpected end of input",
            "unexpected identifier",
            "expected command",
            "invalid syntax",
            "function expected",
            "unknown identifier",
            "unknown constant",
            "unknown namespace",
            "unknown module",
            "failed to synthesize",
            "invalid field notation",
            "invalid 'end'",
            "declaration name expected",
            "application type mismatch",
        )
        proof_markers = (
            "unsolved goals",
            "tactic 'assumption' failed",
            "tactic 'exact' failed",
            "tactic 'rfl' failed",
            "tactic execution has not been implemented",
            "declaration has metavariables",
        )
        if any(marker in lowered for marker in syntax_or_elab_markers):
            return "SYNTAX_OR_ELAB"
        if any(marker in lowered for marker in proof_markers):
            return "PROOF_ERROR"
        return "SYNTAX_OR_ELAB"

    def parse_audit(output: str) -> tuple[dict[str, Any], list[str]]:
        library: list[dict[str, Any]] = []
        forbidden: list[dict[str, Any]] = []
        local_modules: list[str] = []
        target_names: list[str] = []
        target_seen = False
        format_version: int | None = None
        type_check: dict[str, Any] | None = None
        malformed: list[str] = []
        lean_name = re.compile(
            r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
        )
        for raw_line in output.splitlines():
            fields = raw_line.split("\t")
            if fields[:1] == ["format"] and len(fields) == 2:
                try:
                    format_version = int(fields[1])
                except ValueError:
                    malformed.append(raw_line)
            elif fields[:1] == ["target"] and len(fields) >= 3:
                target_seen = True
                target_names.append(fields[1])
            elif fields[:1] == ["typeeq"] and len(fields) == 4:
                if type_check is not None or fields[3] not in ("true", "false"):
                    malformed.append(raw_line)
                else:
                    type_check = {
                        "candidate": fields[1],
                        "expected": fields[2],
                        "equal": fields[3] == "true",
                    }
            elif fields[:1] == ["localmodule"] and len(fields) == 2:
                if lean_name.fullmatch(fields[1]):
                    local_modules.append(fields[1])
                else:
                    malformed.append(raw_line)
            elif fields[:1] == ["library"] and len(fields) == 4:
                try:
                    distance = int(fields[3])
                except ValueError:
                    malformed.append(raw_line)
                    continue
                library.append(
                    {"name": fields[1], "module": fields[2], "distance": distance}
                )
            elif fields[:1] == ["forbidden"] and len(fields) >= 3:
                forbidden.append({"name": fields[1], "kind": fields[2]})
            elif fields[:1] in (["visited"], ["summary"]):
                continue
            elif raw_line.strip():
                malformed.append(raw_line)
        return (
            {
                "ok": (
                    format_version == 2
                    and target_seen
                    and type_check is not None
                    and type_check["equal"] is True
                    and not malformed
                ),
                "format_version": format_version,
                "target_seen": target_seen,
                "type_check": type_check,
                "local_modules": sorted(set(local_modules)),
                "library_declarations": sorted(
                    library, key=lambda item: (item["distance"], item["name"])
                ),
                "forbidden_dependencies": forbidden,
                "malformed_lines": malformed,
            },
            target_names,
        )

    for index, validation in enumerate(validation_records, start=1):
        label = f"condition {condition} validation {index}"
        missing_fields = sorted(required_fields - set(validation))
        candidate_sha256 = validation.get("candidate_sha256")
        if missing_fields:
            raise MeasurementError(
                f"{label} result lacks validator fields: {missing_fields}"
            )
        if (
            type(validation.get("pass")) is not bool
            or validation.get("condition") != condition
            or validation.get("target_theorem") != target_theorem
            or validation.get("submission") != "candidate.lean"
            or validation.get("reject_workspace_local_module_imports") is not True
            or not isinstance(validation.get("note"), str)
            or not validation.get("note")
            or not isinstance(candidate_sha256, str)
            or re.fullmatch(r"[0-9a-f]{64}", candidate_sha256) is None
        ):
            raise MeasurementError(f"{label} has an invalid fixed validator contract")

        def rejected(code: str, stage_index: int, stage: str) -> None:
            if (
                validation.get("pass") is not False
                or validation.get("failure_code") != code
            ):
                raise MeasurementError(
                    f"{label} pass/failure result disagrees with first failed stage "
                    f"{stage}"
                )
            impossible = [
                field
                for field in stage_fields[stage_index + 1 :]
                if validation.get(field) is not None
            ]
            if impossible:
                raise MeasurementError(
                    f"{label} populates impossible post-{stage} stages: {impossible}"
                )

        controlled_before = validation.get("controlled_before")
        if controlled_before is None:
            rejected("SYSTEM_ERROR", 0, "controlled_before")
            continue
        if not checkpoint(controlled_before, label=label):
            rejected("RULE_VIOLATION", 0, "controlled_before")
            continue

        inventory = validation.get("candidate_inventory")
        if inventory is None:
            rejected("SYSTEM_ERROR", 1, "candidate_inventory")
            continue
        inventory_fields = (
            "scanned_sources",
            "candidate_oleans",
            "ignored_build_roots",
            "local_modules",
            "findings",
            "protected_modules",
        )
        inventory_is_complete = bool(
            isinstance(inventory, Mapping)
            and inventory.get("controlled_file_count") == expected_controlled_files
            and all(
                isinstance(inventory.get(field), list) for field in inventory_fields
            )
            and "candidate.lean" in inventory.get("scanned_sources", [])
            and "candidate" in inventory.get("local_modules", [])
        )
        if not inventory_is_complete:
            rejected("SYSTEM_ERROR", 1, "candidate_inventory")
            continue
        if (
            not isinstance(validation.get("static_findings"), list)
            or validation.get("static_findings", [])[: len(inventory.get("findings", []))]
            != inventory.get("findings")
        ):
            raise MeasurementError(f"{label} candidate inventory is inconsistent")
        if validation["static_findings"]:
            rejected("RULE_VIOLATION", 1, "candidate_inventory_and_static_scan")
            continue

        statement = validation.get("statement_check")
        if statement is None:
            rejected("SYSTEM_ERROR", 2, "statement_check")
            continue
        if not isinstance(statement, Mapping) or type(statement.get("ok")) is not bool:
            raise MeasurementError(f"{label} statement check is malformed")
        if statement.get("ok") is not True:
            rejected("RULE_VIOLATION", 2, "statement_check")
            continue
        if (
            not isinstance(statement.get("submitted"), str)
            or not statement.get("submitted")
            or statement.get("submitted") != statement.get("canonical")
        ):
            raise MeasurementError(f"{label} successful statement check is inconsistent")

        controlled_hidden = validation.get("controlled_hidden")
        if controlled_hidden is None:
            rejected("SYSTEM_ERROR", 3, "controlled_hidden")
            continue
        if not checkpoint(controlled_hidden, label=label):
            rejected("RULE_VIOLATION", 3, "controlled_hidden")
            continue

        compile_result = validation.get("compile")
        if compile_result is None:
            rejected("SYSTEM_ERROR", 4, "candidate_compile")
            continue
        compile_result = command_result(compile_result, label=f"{label} compile")
        after_compile = validation.get("controlled_after_compile")
        if after_compile is None:
            rejected("SYSTEM_ERROR", 5, "controlled_after_compile")
            continue
        if not checkpoint(after_compile, label=label):
            rejected("RULE_VIOLATION", 5, "controlled_after_compile")
            continue
        if compile_result.get("system_error") is not None:
            rejected("SYSTEM_ERROR", 5, "candidate_compile_system_error")
            continue
        if compile_result.get("timed_out") is True:
            rejected("SYSTEM_ERROR", 5, "candidate_compile_timeout")
            continue
        if compile_result.get("exit_code") != 0:
            rejected(
                classify_compile_failure(str(compile_result.get("output"))),
                5,
                "candidate_compile_rejection",
            )
            continue
        compile_output = str(compile_result.get("output"))
        if "sorryAx" in compile_output or "declaration uses 'sorry'" in compile_output:
            rejected("RULE_VIOLATION", 5, "candidate_compile_sorry_dependency")
            continue

        expected_result = validation.get("expected_statement_compile")
        if expected_result is None:
            rejected("SYSTEM_ERROR", 6, "expected_statement_compile")
            continue
        expected_result = command_result(
            expected_result, label=f"{label} expected-statement compile"
        )
        after_expected = validation.get("controlled_after_expected_compile")
        if after_expected is None:
            rejected("SYSTEM_ERROR", 7, "controlled_after_expected_compile")
            continue
        if not checkpoint(after_expected, label=label):
            rejected("RULE_VIOLATION", 7, "controlled_after_expected_compile")
            continue
        if (
            expected_result.get("system_error") is not None
            or expected_result.get("timed_out") is True
            or expected_result.get("exit_code") != 0
        ):
            rejected("SYSTEM_ERROR", 7, "expected_statement_compile")
            continue

        side_channel = validation.get("local_modules_side_channel")
        if side_channel is None:
            rejected("SYSTEM_ERROR", 8, "dependency_audit_setup")
            continue
        if (
            not isinstance(side_channel, Mapping)
            or set(side_channel)
            != {
                "created_after_candidate_compilation",
                "candidate_recompiled_during_audit",
                "unchanged_after_audit",
            }
            or side_channel.get("created_after_candidate_compilation") is not True
            or side_channel.get("candidate_recompiled_during_audit") is not False
        ):
            raise MeasurementError(f"{label} audit side-channel evidence is malformed")
        if side_channel.get("unchanged_after_audit") is not True:
            rejected("RULE_VIOLATION", 8, "local_modules_side_channel")
            continue

        after_audit = validation.get("controlled_after_audit")
        if after_audit is None:
            rejected("SYSTEM_ERROR", 9, "controlled_after_audit")
            continue
        if not checkpoint(after_audit, label=label):
            rejected("RULE_VIOLATION", 9, "controlled_after_audit")
            continue

        audit = validation.get("dependency_audit")
        if audit is None:
            rejected("SYSTEM_ERROR", 10, "dependency_audit")
            continue
        audit = command_result(audit, label=f"{label} dependency audit")
        parsed = audit.get("parsed")
        raw_parsed, target_names = parse_audit(str(audit.get("output")))
        local_modules = inventory.get("local_modules")
        if not all(isinstance(module, str) and module for module in local_modules):
            raise MeasurementError(f"{label} candidate module inventory is malformed")
        expected_helpers = sorted(set(local_modules) - {"candidate"})
        raw_parsed["expected_helper_modules"] = expected_helpers
        raw_parsed["missing_helper_modules"] = sorted(
            set(expected_helpers) - set(raw_parsed["local_modules"])
        )
        if not isinstance(parsed, Mapping) or dict(parsed) != raw_parsed:
            raise MeasurementError(
                f"{label} parsed dependency audit disagrees with its output"
            )
        semantic = validation.get("semantic_statement_check")
        if semantic != raw_parsed["type_check"]:
            raise MeasurementError(
                f"{label} semantic statement check disagrees with dependency audit"
            )
        audit_options = _strict_command_options(
            audit["command"], label=f"{label} dependency audit command"
        )
        expected_theorem = audit_options.get("--expected-theorem")
        if raw_parsed["target_seen"] and target_theorem not in target_names:
            raise MeasurementError(f"{label} dependency audit targeted another theorem")
        if isinstance(semantic, Mapping) and semantic.get("equal") is False:
            rejected("RULE_VIOLATION", 11, "semantic_statement_check")
            continue
        if (
            not isinstance(semantic, Mapping)
            or semantic.get("candidate") != target_theorem
            or semantic.get("expected") != expected_theorem
            or semantic.get("equal") is not True
        ):
            rejected("SYSTEM_ERROR", 11, "semantic_statement_check")
            continue
        if raw_parsed["forbidden_dependencies"]:
            rejected("RULE_VIOLATION", 11, "forbidden_dependency_audit")
            continue
        if (
            raw_parsed["format_version"] != 2
            or raw_parsed["missing_helper_modules"]
        ):
            rejected("SYSTEM_ERROR", 11, "helper_dependency_coverage")
            continue
        if (
            audit.get("system_error") is not None
            or audit.get("timed_out") is True
            or audit.get("exit_code") != 0
            or raw_parsed["ok"] is not True
            or raw_parsed["target_seen"] is not True
            or raw_parsed["malformed_lines"]
        ):
            rejected("SYSTEM_ERROR", 11, "dependency_audit")
            continue

        declarations_by_identity: dict[tuple[str, str], dict[str, Any]] = {}
        for declaration in raw_parsed["library_declarations"]:
            identity = (declaration["name"], declaration["module"])
            previous = declarations_by_identity.get(identity)
            if previous is None or declaration["distance"] < previous["distance"]:
                declarations_by_identity[identity] = declaration
        declarations = sorted(
            declarations_by_identity.values(),
            key=lambda item: (item["distance"], item["name"], item["module"]),
        )
        if (
            validation.get("library_audit_complete") is not True
            or validation.get("library_declarations") != declarations
            or validation.get("library_use") is not bool(declarations)
        ):
            raise MeasurementError(f"{label} library audit summary is inconsistent")
        if condition == "N" and declarations:
            rejected("RULE_VIOLATION", 11, "condition_n_library_dependency")
            continue
        if (
            validation.get("pass") is not True
            or validation.get("failure_code") is not None
            or validation.get("note") != "accepted by hidden Lean validation"
        ):
            raise MeasurementError(
                f"{label} rejected validation has no derived failed validator stage"
            )
    if (
        expected_final_candidate_sha256 is not None
        and validation_records
        and validation_records[-1].get("candidate_sha256")
        != expected_final_candidate_sha256
    ):
        raise MeasurementError(
            f"condition {condition} final validation hash differs from final candidate"
        )


def _verify_one_resource(
    pair_root: Path,
    pair: Mapping[str, Any],
    expected_pair: Mapping[str, Any],
    campaign: Mapping[str, Any],
    *,
    condition: str | None,
) -> dict[str, Any]:
    if (
        pair.get("hardware_verification_before")
        != campaign.get("hardware_identity")
        or pair.get("hardware_verification_after")
        != campaign.get("hardware_identity")
    ):
        raise MeasurementError(
            "pair lacks matching before/after hardware-identity verification"
        )
    descriptor = pair.get("resource")
    proof_descriptor = pair.get("resource_proof")
    worker_proof_descriptor = pair.get("resource_worker_proof")
    if not isinstance(descriptor, Mapping) or not isinstance(
        proof_descriptor, Mapping
    ) or not isinstance(worker_proof_descriptor, Mapping):
        raise MeasurementError(f"attempt {pair.get('pair_id')} lacks resource evidence")
    path = _resolve_artifact(pair_root, descriptor, "attempt resource record")
    proof_path = _resolve_artifact(
        pair_root, proof_descriptor, "attempt kernel resource proof"
    )
    worker_proof_path = _resolve_artifact(
        pair_root, worker_proof_descriptor, "attempt worker kernel resource proof"
    )
    value = read_object(path)
    legacy_pair_resource = value.get("kind") == "highambench-pair-resource"
    if value.get("kind") not in (
        "highambench-pair-resource",
        "highambench-attempt-resource",
    ):
        raise MeasurementError("resource record has an invalid kind")
    _verify_self_hash(value, "resource record")
    slot = value.get("slot")
    if not isinstance(slot, Mapping):
        raise MeasurementError("attempt resource record has no slot")
    cores = slot.get("cores")
    logical = slot.get("logical_cpus")
    if (
        value.get("pair_id") != expected_pair.get("pair_id")
        or (
            not legacy_pair_resource
            and value.get("condition") != condition
        )
        or value.get("campaign_hardware_identity")
        != campaign.get("hardware_identity")
        or slot.get("physical_core_count") != 4
        or not isinstance(cores, list)
        or len(cores) != 4
        or not isinstance(logical, list)
        or len(set(logical)) != len(logical)
        or slot.get("memory_max_bytes") != 16 * 1024**3
        or slot.get("memory_swap_max_bytes") != 0
    ):
        raise MeasurementError("attempt resource slot violates the 4-core/16-GiB policy")
    locked_slots = campaign.get("resource_slots")
    if not isinstance(locked_slots, list) or slot not in locked_slots:
        raise MeasurementError("attempt resource slot was not authorized by the campaign")
    type_keys = {core.get("type_key") for core in cores if isinstance(core, Mapping)}
    if type_keys != {slot.get("type_key")}:
        raise MeasurementError("attempt resource slot mixes physical core types")
    core_identities = {
        (core.get("package_id"), core.get("die_id"), core.get("core_id"))
        for core in cores
        if isinstance(core, Mapping)
    }
    sibling_cpus = [
        cpu
        for core in cores
        if isinstance(core, Mapping) and isinstance(core.get("logical_cpus"), list)
        for cpu in core["logical_cpus"]
    ]
    if (
        len(core_identities) != 4
        or len(sibling_cpus) != len(set(sibling_cpus))
        or sorted(sibling_cpus) != logical
    ):
        raise MeasurementError("attempt resource slot has invalid physical-core siblings")
    if any(type(cpu) is not int or cpu < 0 for cpu in logical):
        raise MeasurementError("attempt resource slot has invalid logical CPUs")
    campaign_logical: set[int] = set()
    for campaign_slot in locked_slots:
        campaign_slot_cpus = (
            campaign_slot.get("logical_cpus")
            if isinstance(campaign_slot, Mapping)
            else None
        )
        if (
            not isinstance(campaign_slot_cpus, list)
            or not campaign_slot_cpus
            or any(
                type(cpu) is not int or cpu < 0 for cpu in campaign_slot_cpus
            )
            or len(campaign_slot_cpus) != len(set(campaign_slot_cpus))
            or campaign_logical.intersection(campaign_slot_cpus)
        ):
            raise MeasurementError("campaign CPU slots are not exact and disjoint")
        campaign_logical.update(campaign_slot_cpus)
    expected_cpu_set = set(logical)
    expected_campaign_cpu_list = resources.format_cpu_list(campaign_logical)
    proof = read_object(proof_path)
    worker_proof = read_object(worker_proof_path)

    def verify_cpu_partition_evidence(
        *,
        expected_contract: Mapping[str, Any],
        observed_contract: Mapping[str, Any],
        cgroup: Mapping[str, Any],
        files: Mapping[str, Any],
        pair_parent: Mapping[str, Any],
    ) -> None:
        expected_cpu_list = resources.format_cpu_list(expected_cpu_set)
        partition = observed_contract.get("cpu_partition")
        if not isinstance(partition, Mapping):
            raise MeasurementError("kernel CPU partition evidence is missing")
        if set(partition) != {
            "verified",
            "mode",
            "campaign_partition",
            "slot_partition",
            "service_cgroup",
            "worker_cgroup",
            "service_cpuset_cpus_effective",
            "service_cpuset_cpus_effective_parsed",
        }:
            raise MeasurementError("kernel CPU partition evidence is malformed")

        campaign_partition = partition.get("campaign_partition")
        slot_partition = partition.get("slot_partition")
        service_cgroup = partition.get("service_cgroup")
        worker_cgroup = partition.get("worker_cgroup")
        if not all(
            isinstance(item, Mapping)
            for item in (
                campaign_partition,
                slot_partition,
                service_cgroup,
                worker_cgroup,
            )
        ):
            raise MeasurementError("kernel CPU partition evidence is incomplete")

        cgroup_directory = Path(str(cgroup.get("directory")))
        mount_point = Path(str(cgroup.get("mount_point")))
        try:
            relative = cgroup_directory.relative_to(mount_point)
        except ValueError as error:
            raise MeasurementError(
                "kernel CPU partition ancestry escapes the cgroup-v2 mount"
            ) from error
        parts = relative.parts
        if (
            len(parts) != 4
            or parts[0] != "highambench.slice"
            or re.fullmatch(r"highambench-slot[0-9]+[.]slice", parts[1]) is None
            or re.fullmatch(
                r"highambench-[A-Za-z0-9_.:@-]+[.]service", parts[2]
            )
            is None
        ):
            raise MeasurementError(
                "kernel CPU partition ancestry is outside the reserved VSCLReuse slot"
            )
        campaign_directory = mount_point / parts[0]
        slot_directory = campaign_directory / parts[1]
        service_directory = slot_directory / parts[2]

        def verify_directory_identity(
            value: Mapping[str, Any], expected_directory: Path, *, label: str
        ) -> dict[str, Any]:
            if (
                set(value) != {"directory", "device", "inode"}
                or value.get("directory") != str(expected_directory)
                or type(value.get("device")) is not int
                or value["device"] < 0
                or type(value.get("inode")) is not int
                or value["inode"] <= 0
            ):
                raise MeasurementError(
                    f"kernel CPU partition {label} identity is invalid"
                )
            return dict(value)

        def verify_cpuset_record(
            value: Mapping[str, Any],
            expected_directory: Path,
            *,
            label: str,
            expected_effective: set[int],
        ) -> tuple[set[int], set[int]]:
            required = {
                "directory",
                "device",
                "inode",
                "cpuset_cpus",
                "cpuset_cpus_parsed",
                "cpuset_cpus_effective",
                "cpuset_cpus_effective_parsed",
                "cpuset_cpus_partition",
            }
            requested = value.get("cpuset_cpus_parsed")
            effective = value.get("cpuset_cpus_effective_parsed")
            if (
                set(value) != required
                or value.get("directory") != str(expected_directory)
                or type(value.get("device")) is not int
                or value["device"] < 0
                or type(value.get("inode")) is not int
                or value["inode"] <= 0
                or not isinstance(value.get("cpuset_cpus"), str)
                or not isinstance(value.get("cpuset_cpus_effective"), str)
                or not isinstance(requested, list)
                or not requested
                or not isinstance(effective, list)
                or any(type(cpu) is not int or cpu < 0 for cpu in requested)
                or any(type(cpu) is not int or cpu < 0 for cpu in effective)
                or requested != sorted(set(requested))
                or effective != sorted(set(effective))
                or value.get("cpuset_cpus")
                != resources.format_cpu_list(requested)
                or value.get("cpuset_cpus_effective")
                != (
                    resources.format_cpu_list(effective)
                    if effective
                    else ""
                )
                or set(effective) != expected_effective
            ):
                raise MeasurementError(
                    f"kernel CPU partition {label} cpuset record is invalid"
                )
            return set(requested), set(effective)

        campaign_requested, campaign_effective = verify_cpuset_record(
            campaign_partition,
            campaign_directory,
            label="campaign",
            expected_effective=set(),
        )
        slot_requested, slot_effective = verify_cpuset_record(
            slot_partition,
            slot_directory,
            label="slot",
            expected_effective=expected_cpu_set,
        )
        service_identity = verify_directory_identity(
            service_cgroup,
            service_directory,
            label="service",
        )
        verify_directory_identity(
            worker_cgroup,
            cgroup_directory,
            label="worker",
        )
        service_effective = partition.get("service_cpuset_cpus_effective_parsed")
        if (
            partition.get("verified") is not True
            or partition.get("mode") != "root"
            or campaign_partition.get("cpuset_cpus_partition") != "root"
            or slot_partition.get("cpuset_cpus_partition") != "root"
            or campaign_requested != campaign_logical
            or campaign_effective
            or campaign_partition.get("cpuset_cpus")
            != expected_campaign_cpu_list
            or slot_requested != expected_cpu_set
            or slot_effective != expected_cpu_set
            or not isinstance(service_effective, list)
            or service_effective != sorted(expected_cpu_set)
            or partition.get("service_cpuset_cpus_effective")
            != expected_cpu_list
            or expected_contract.get("cpuset_effective_cpu_list")
            != expected_cpu_list
            or expected_contract.get("cpuset_partition_mode") != "root"
            or dict(pair_parent) != service_identity
        ):
            raise MeasurementError(
                "kernel CPU partition evidence does not match the exact campaign slot"
            )

    def verify_contract(
        candidate: Mapping[str, Any],
        *,
        expected_memory_bytes: int,
        expected_directory: str | None = None,
    ) -> dict[str, Any]:
        expected_contract = candidate.get("expected")
        observed_contract = candidate.get("observed")
        if not isinstance(expected_contract, Mapping) or not isinstance(
            observed_contract, Mapping
        ):
            raise MeasurementError("kernel resource proof is incomplete")
        files = observed_contract.get("cgroup_files")
        ancestors = observed_contract.get("ancestor_memory_limits")
        cgroup = observed_contract.get("cgroup")
        pair_parent = observed_contract.get("pair_parent_cgroup")
        pair_parent_controls = observed_contract.get(
            "pair_parent_memory_controls"
        )
        affinity_probe = observed_contract.get("sched_setaffinity_probe")
        expected_cpu_list = resources.format_cpu_list(logical)
        if (
            candidate.get("schema_version") != resources.SCHEMA_VERSION
            or candidate.get("kind") != "highambench-resource-proof"
            or candidate.get("verified") is not True
            or not isinstance(files, Mapping)
            or not isinstance(ancestors, list)
            or not isinstance(cgroup, Mapping)
            or not isinstance(pair_parent, Mapping)
            or not isinstance(pair_parent_controls, Mapping)
            or not isinstance(affinity_probe, Mapping)
            or not all(
                isinstance(cgroup.get(key), str)
                for key in (
                    "membership_path",
                    "mount_root",
                    "mount_point",
                    "directory",
                )
            )
            or not Path(str(cgroup.get("directory"))).is_absolute()
            or not str(cgroup.get("membership_path", "")).startswith("/")
            or not Path(str(cgroup.get("mount_point"))).is_absolute()
            or pair_parent.get("directory")
            != str(Path(str(cgroup.get("directory"))).parent)
            or not isinstance(pair_parent.get("device"), int)
            or not isinstance(pair_parent.get("inode"), int)
            or pair_parent_controls
            != {
                "memory.max": "max",
                "memory.high": "max",
                "memory.swap.max": "0",
                "memory.oom.group": "1",
            }
            or expected_contract.get("logical_cpus") != logical
            or expected_contract.get("cpu_list") != expected_cpu_list
            or expected_contract.get("physical_cores_per_slot") != 4
            or expected_contract.get("memory_max_bytes")
            != expected_memory_bytes
            or expected_contract.get("memory_swap_max_bytes") != 0
            or expected_contract.get("memory_oom_group") is not True
            or expected_contract.get("affinity_change_errno") != "EPERM"
            or observed_contract.get("sched_getaffinity") != logical
            or affinity_probe.get("blocked") is not True
            or affinity_probe.get("attempted_cpu_list") != expected_cpu_list
            or affinity_probe.get("errno") != 1
            or affinity_probe.get("errno_name") != "EPERM"
            or files.get("memory.max") != str(expected_memory_bytes)
            or files.get("memory.high") != "max"
            or files.get("memory.swap.max") != "0"
            or files.get("memory.oom.group") != "1"
            or (
                expected_directory is not None
                and cgroup.get("directory") != expected_directory
            )
        ):
            raise MeasurementError("kernel resource proof does not match the pair slot")

        cgroup_directory = Path(str(cgroup["directory"]))
        mount_point = Path(str(cgroup["mount_point"]))
        membership_path = Path(str(cgroup["membership_path"]))
        mount_root = Path(str(cgroup["mount_root"]))
        try:
            membership_relative = membership_path.relative_to(mount_root)
            cgroup_relative = cgroup_directory.relative_to(mount_point)
        except ValueError as error:
            raise MeasurementError(
                "kernel cgroup path is outside its recorded mount"
            ) from error
        if cgroup_relative != membership_relative:
            raise MeasurementError(
                "kernel cgroup directory does not match its membership/mount mapping"
            )
        verify_cpu_partition_evidence(
            expected_contract=expected_contract,
            observed_contract=observed_contract,
            cgroup=cgroup,
            files=files,
            pair_parent=pair_parent,
        )

        expected_ancestor_directories: list[str] = []
        cursor = cgroup_directory
        while cursor != mount_point:
            expected_ancestor_directories.append(str(cursor))
            parent = cursor.parent
            if parent == cursor:
                raise MeasurementError(
                    "kernel ancestor memory proof does not reach its mount point"
                )
            cursor = parent
        if (
            not expected_ancestor_directories
            or Path(expected_ancestor_directories[-1]).parent != mount_point
        ):
            raise MeasurementError(
                "kernel ancestor memory proof does not reach the mount's direct child"
            )
        if len(expected_ancestor_directories) < 2:
            raise MeasurementError(
                "kernel worker cgroup lacks its delegated coordinator parent"
            )
        recorded_ancestor_directories = [
            ancestor.get("directory") if isinstance(ancestor, Mapping) else None
            for ancestor in ancestors
        ]
        if (
            recorded_ancestor_directories != expected_ancestor_directories
            or len(set(recorded_ancestor_directories)) != len(ancestors)
        ):
            raise MeasurementError(
                "kernel ancestor memory proof is not the exact continuous parent "
                "chain to the mount's direct child"
            )

        def verify_limit_encoding(
            raw: object, parsed: object, *, label: str
        ) -> None:
            if not isinstance(raw, str):
                raise MeasurementError(f"kernel {label} raw limit is invalid")
            if raw == "max":
                if parsed is not None:
                    raise MeasurementError(
                        f"kernel {label} raw/parsed limits disagree"
                    )
                return
            if re.fullmatch(r"0|[1-9][0-9]*", raw) is None:
                raise MeasurementError(f"kernel {label} raw limit is invalid")
            if type(parsed) is not int or parsed != int(raw):
                raise MeasurementError(
                    f"kernel {label} raw/parsed limits disagree"
                )

        for index, ancestor in enumerate(ancestors):
            if not isinstance(ancestor, Mapping):
                raise MeasurementError("kernel ancestor memory proof is invalid")
            if set(ancestor) != {
                "directory",
                "memory_max_raw",
                "memory_max_bytes",
                "memory_high_raw",
                "memory_high_bytes",
            }:
                raise MeasurementError("kernel ancestor memory proof is invalid")
            verify_limit_encoding(
                ancestor.get("memory_max_raw"),
                ancestor.get("memory_max_bytes"),
                label="memory.max",
            )
            verify_limit_encoding(
                ancestor.get("memory_high_raw"),
                ancestor.get("memory_high_bytes"),
                label="memory.high",
            )
            if (
                not isinstance(ancestor.get("directory"), str)
                or (
                    index == 0
                    and (
                        ancestor.get("directory") != cgroup.get("directory")
                        or ancestor.get("memory_max_raw")
                        != str(expected_memory_bytes)
                        or ancestor.get("memory_max_bytes")
                        != expected_memory_bytes
                        or ancestor.get("memory_high_raw") != "max"
                        or ancestor.get("memory_high_bytes") is not None
                    )
                )
            ):
                raise MeasurementError("kernel ancestor memory proof is invalid")
            if index > 0 and (
                ancestor.get("memory_max_raw") != "max"
                or ancestor.get("memory_max_bytes") is not None
                or ancestor.get("memory_high_raw") != "max"
                or ancestor.get("memory_high_bytes") is not None
            ):
                raise MeasurementError(
                    "condition ancestor has a binding memory control"
                )
        if (
            ancestors[1].get("directory")
            != str(Path(str(cgroup.get("directory"))).parent)
            or ancestors[1].get("memory_max_raw") != "max"
            or ancestors[1].get("memory_max_bytes") is not None
            or ancestors[1].get("memory_high_raw") != "max"
            or ancestors[1].get("memory_high_bytes") is not None
        ):
            raise MeasurementError(
                "condition coordinator cgroup is not nonbinding"
            )
        return {
            "expected": dict(expected_contract),
            "observed": dict(observed_contract),
        }

    if (
        value.get("schema_version") != 2
        or value.get("kernel_proof_before_exec") != proof
        or value.get(
            "kernel_proof_at_pair_start"
            if legacy_pair_resource
            else "kernel_proof_at_attempt_worker_start"
        )
        != worker_proof
    ):
        raise MeasurementError("resource record embedded proofs differ from artifacts")
    verify_contract(
        proof, expected_memory_bytes=resources.MANAGER_MEMORY_MAX_BYTES
    )
    verify_contract(
        worker_proof, expected_memory_bytes=resources.MANAGER_MEMORY_MAX_BYTES
    )
    if _resource_contract_identity(proof) != _resource_contract_identity(worker_proof):
        raise MeasurementError("wrapper and worker resource contracts differ")
    observed = proof["observed"]
    delegated_layout = proof.get("delegated_memory_layout")
    delegated_root = (
        delegated_layout.get("root")
        if isinstance(delegated_layout, Mapping)
        else None
    )
    delegated_manager = (
        delegated_layout.get("manager")
        if isinstance(delegated_layout, Mapping)
        else None
    )
    proof_cpu_partition = observed.get("cpu_partition")
    proof_service_cgroup = (
        proof_cpu_partition.get("service_cgroup")
        if isinstance(proof_cpu_partition, Mapping)
        else None
    )
    proof_worker_cgroup = (
        proof_cpu_partition.get("worker_cgroup")
        if isinstance(proof_cpu_partition, Mapping)
        else None
    )
    if (
        not isinstance(delegated_layout, Mapping)
        or delegated_layout.get("schema_version") != resources.SCHEMA_VERSION
        or delegated_layout.get("kind")
        != "highambench-delegated-memory-layout"
        or delegated_layout.get("verified") is not True
        or delegated_layout.get("required_controllers") != ["memory"]
        or not isinstance(delegated_layout.get("root_controllers"), list)
        or not all(
            isinstance(item, str)
            for item in delegated_layout.get("root_controllers", [])
        )
        or "memory" not in set(delegated_layout["root_controllers"])
        or not isinstance(delegated_layout.get("root_subtree_control"), list)
        or not all(
            isinstance(item, str)
            for item in delegated_layout.get("root_subtree_control", [])
        )
        or set(delegated_layout["root_subtree_control"]) != {"memory"}
        or not isinstance(delegated_root, Mapping)
        or not isinstance(delegated_manager, Mapping)
        or not isinstance(proof_service_cgroup, Mapping)
        or not isinstance(proof_worker_cgroup, Mapping)
        or not all(
            isinstance(item.get("directory"), str)
            and isinstance(item.get("device"), int)
            and isinstance(item.get("inode"), int)
            for item in (delegated_root, delegated_manager)
        )
        or delegated_manager.get("directory")
        != proof["observed"]["cgroup"].get("directory")
        or Path(str(delegated_manager.get("directory"))).parent
        != Path(str(delegated_root.get("directory")))
        or delegated_manager.get("device") != delegated_root.get("device")
        or dict(delegated_root) != dict(proof_service_cgroup)
        or dict(delegated_manager) != dict(proof_worker_cgroup)
        or delegated_layout.get("root_memory_controls")
        != {
            "memory.max": "max",
            "memory.high": "max",
            "memory.swap.max": "0",
            "memory.oom.group": "1",
        }
        or delegated_layout.get("manager_memory_controls")
        != {
            "memory.max": str(resources.MANAGER_MEMORY_MAX_BYTES),
            "memory.high": "max",
            "memory.swap.max": "0",
            "memory.oom.group": "1",
        }
    ):
        raise MeasurementError("pair proof lacks delegated memory-root evidence")
    shared_parent = delegated_root
    samples = pair.get("resource_samples")
    if (
        not isinstance(samples, list)
        or len(samples) != (2 if legacy_pair_resource else 1)
        or [sample.get("after_condition") for sample in samples if isinstance(sample, Mapping)]
        != (pair.get("condition_order") if legacy_pair_resource else [condition])
    ):
        raise MeasurementError("pair lacks post-condition cgroup telemetry")
    sample_summaries: list[dict[str, Any]] = []
    seen_scope_ids: set[str] = set()
    seen_cgroups: set[tuple[str, int, int]] = set()
    seen_scope_artifacts: set[Path] = set()
    condition_resources: dict[str, dict[str, Any]] = {}
    for sample in samples:
        if not isinstance(sample, Mapping) or sample.get("after_condition") not in ("N", "L"):
            raise MeasurementError("pair has an invalid cgroup telemetry sample")
        manager_descriptor = sample.get("manager_after_condition")
        begin_descriptor = sample.get("condition_cgroup_begin")
        entry_descriptor = sample.get("condition_cgroup_entry_proof")
        finish_descriptor = sample.get("condition_cgroup_finish")
        if (
            set(sample)
            != {
                "after_condition",
                "manager_after_condition",
                "condition_cgroup_begin",
                "condition_cgroup_entry_proof",
                "condition_cgroup_finish",
            }
            or not isinstance(manager_descriptor, Mapping)
            or not isinstance(begin_descriptor, Mapping)
            or not isinstance(entry_descriptor, Mapping)
            or not isinstance(finish_descriptor, Mapping)
        ):
            raise MeasurementError("pair cgroup telemetry sample is incomplete")
        begin_path = _resolve_artifact(
            pair_root, begin_descriptor, "fresh condition cgroup begin"
        )
        entry_path = _resolve_artifact(
            pair_root, entry_descriptor, "condition cgroup entry proof"
        )
        finish_path = _resolve_artifact(
            pair_root, finish_descriptor, "fresh condition cgroup finish"
        )
        if (
            begin_path == finish_path
            or entry_path in (begin_path, finish_path)
            or any(
                path in seen_scope_artifacts
                for path in (begin_path, entry_path, finish_path)
            )
        ):
            raise MeasurementError("condition cgroup artifacts are not distinct")
        seen_scope_artifacts.update((begin_path, entry_path, finish_path))
        begin = read_object(
            begin_path, kind="highambench-fresh-condition-cgroup-begin"
        )
        entry_proof = read_object(entry_path)
        finish = read_object(
            finish_path, kind="highambench-fresh-condition-cgroup-finish"
        )
        begin_contract = begin.get("manager_resource_contract")
        begin_cgroup = begin.get("cgroup")
        finish_cgroup = finish.get("cgroup")
        parent_cgroup = begin.get("parent_cgroup")
        initial = begin.get("initial")
        condition = str(sample["after_condition"])
        if (
            begin.get("schema_version") != resources.SCHEMA_VERSION
            or begin.get("verified") is not True
            or not isinstance(begin.get("verified_at"), str)
            or begin.get("condition_id") != condition
            or begin.get("measurement_scope")
            != "fresh_condition_cgroup_lifetime"
            or begin.get("memory_peak_reset_used") is not False
            or begin.get("expected_logical_cpus") != logical
            or not isinstance(begin.get("scope_id"), str)
            or re.fullmatch(r"[0-9a-f]{32}", str(begin["scope_id"])) is None
            or not isinstance(begin_contract, Mapping)
            or _resource_contract_identity(begin_contract)
            != _resource_contract_identity(proof)
            or not isinstance(parent_cgroup, Mapping)
            or parent_cgroup != shared_parent
            or not isinstance(begin_cgroup, Mapping)
            or not isinstance(initial, Mapping)
            or initial.get("cgroup_procs") != ""
            or "populated 0"
            not in str(initial.get("cgroup_events", "")).splitlines()
            or initial.get("memory_current_bytes") != 0
            or initial.get("memory_peak_bytes") != 0
            or initial.get("memory_max") != str(16 * 1024**3)
            or initial.get("memory_high") != "max"
            or initial.get("memory_swap_max") != "0"
            or initial.get("memory_oom_group") != "1"
        ):
            raise MeasurementError("fresh condition cgroup begin is invalid")
        directory = begin_cgroup.get("directory")
        device = begin_cgroup.get("device")
        inode = begin_cgroup.get("inode")
        if (
            not isinstance(directory, str)
            or not isinstance(device, int)
            or not isinstance(inode, int)
            or Path(directory).parent != Path(str(parent_cgroup.get("directory")))
        ):
            raise MeasurementError("fresh condition cgroup identity is invalid")
        cgroup_identity = (directory, device, inode)
        scope_id = str(begin["scope_id"])
        if scope_id in seen_scope_ids or cgroup_identity in seen_cgroups:
            raise MeasurementError("condition cgroups are not fresh and distinct")
        seen_scope_ids.add(scope_id)
        seen_cgroups.add(cgroup_identity)
        entry_contract = verify_contract(
            entry_proof,
            expected_memory_bytes=resources.MEMORY_MAX_BYTES,
            expected_directory=directory,
        )
        entry_partition = entry_contract["observed"].get("cpu_partition")
        entry_worker_cgroup = (
            entry_partition.get("worker_cgroup")
            if isinstance(entry_partition, Mapping)
            else None
        )
        if (
            not isinstance(entry_worker_cgroup, Mapping)
            or dict(entry_worker_cgroup) != dict(begin_cgroup)
        ):
            raise MeasurementError(
                "condition CPU partition evidence names another worker cgroup"
            )
        begin_digest = hashlib.sha256(
            json.dumps(begin, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()
        if (
            finish.get("schema_version") != resources.SCHEMA_VERSION
            or finish.get("verified") is not True
            or not isinstance(finish.get("verified_at"), str)
            or finish.get("scope_id") != begin.get("scope_id")
            or finish.get("condition_id") != condition
            or finish.get("begin_evidence_sha256") != begin_digest
            or finish.get("measurement_scope")
            != "fresh_condition_cgroup_lifetime"
            or finish.get("memory_peak_reset_used") is not False
            or finish.get("same_cgroup_device_inode") is not True
            or finish.get("parent_cgroup") != parent_cgroup
            or finish_cgroup != begin_cgroup
            or type(finish.get("memory_current_end_bytes")) is not int
            or type(finish.get("memory_peak_lifetime_bytes")) is not int
            or finish["memory_current_end_bytes"] < 0
            or finish["memory_peak_lifetime_bytes"]
            < finish["memory_current_end_bytes"]
            or finish.get("condition_memory_controls_at_finish")
            != {
                "memory.max": str(16 * 1024**3),
                "memory.high": "max",
                "memory.swap.max": "0",
                "memory.oom.group": "1",
            }
            or finish.get("pair_parent_memory_controls_at_finish")
            != {
                "memory.max": "max",
                "memory.high": "max",
                "memory.swap.max": "0",
                "memory.oom.group": "1",
            }
            or "populated 0" not in str(finish.get("cgroup_events", "")).splitlines()
            or not isinstance(finish.get("memory_events"), str)
            or not isinstance(finish.get("memory_events_local"), str)
            or finish.get("cleanup")
            != {"cgroup_kill_used": False, "removed": True}
        ):
            raise MeasurementError("fresh condition cgroup finish is invalid")
        reclaim = finish.get("post_measurement_reclaim")
        reclaim_before = (
            reclaim.get("reclaimable_before_bytes")
            if isinstance(reclaim, Mapping)
            else None
        )
        reclaim_after = (
            reclaim.get("reclaimable_after_bytes")
            if isinstance(reclaim, Mapping)
            else None
        )
        reclaim_keys = {"anon", "file", "shmem"}
        if (
            not isinstance(reclaim, Mapping)
            or set(reclaim)
            != {
                "method",
                "exact_zero_required",
                "eagain_is_partial_success",
                "attempt_count",
                "eagain_count",
                "memory_current_before_bytes",
                "memory_current_after_bytes",
                "reclaimable_before_bytes",
                "reclaimable_after_bytes",
                "reclaimable_zero_after",
            }
            or reclaim.get("method") != "numeric-memory.reclaim"
            or reclaim.get("exact_zero_required") is not False
            or reclaim.get("eagain_is_partial_success") is not True
            or type(reclaim.get("attempt_count")) is not int
            or type(reclaim.get("eagain_count")) is not int
            or reclaim["attempt_count"] < 0
            or not 0 <= reclaim["eagain_count"] <= reclaim["attempt_count"]
            or type(reclaim.get("memory_current_before_bytes")) is not int
            or type(reclaim.get("memory_current_after_bytes")) is not int
            or reclaim["memory_current_before_bytes"] < 0
            or reclaim["memory_current_after_bytes"] < 0
            or not isinstance(reclaim_before, Mapping)
            or not isinstance(reclaim_after, Mapping)
            or set(reclaim_before) != reclaim_keys
            or set(reclaim_after) != reclaim_keys
            or any(type(value) is not int or value < 0 for value in reclaim_before.values())
            or any(type(value) is not int or value < 0 for value in reclaim_after.values())
            or reclaim.get("reclaimable_zero_after")
            is not (not any(reclaim_after.values()))
        ):
            raise MeasurementError(
                "fresh condition post-measurement reclaim is invalid"
            )
        residue = finish.get("pair_parent_residue_diagnostics")
        if (
            not isinstance(residue, Mapping)
            or set(residue)
            != {
                "diagnostic_only",
                "exact_zero_required",
                "before_condition_cgroup_removal",
                "after_condition_cgroup_removal",
            }
            or residue.get("diagnostic_only") is not True
            or residue.get("exact_zero_required") is not False
        ):
            raise MeasurementError(
                "fresh condition parent-residue diagnostics are invalid"
            )

        def verify_residue_snapshot(
            candidate: object, *, before: bool
        ) -> Mapping[str, Any]:
            if not isinstance(candidate, Mapping) or set(candidate) != {
                "memory_current_bytes",
                "reclaimable_memory_stat_bytes",
                "cgroup_stat",
            }:
                raise MeasurementError(
                    "fresh condition parent-residue snapshot is invalid"
                )
            reclaimable = candidate.get("reclaimable_memory_stat_bytes")
            cgroup_stat = candidate.get("cgroup_stat")
            if (
                type(candidate.get("memory_current_bytes")) is not int
                or candidate["memory_current_bytes"] < 0
                or not isinstance(reclaimable, Mapping)
                or set(reclaimable) != {"anon", "file", "shmem"}
                or any(
                    type(value) is not int or value < 0
                    for value in reclaimable.values()
                )
                or not isinstance(cgroup_stat, Mapping)
                or any(
                    not isinstance(key, str)
                    or type(value) is not int
                    or value < 0
                    for key, value in cgroup_stat.items()
                )
                or type(cgroup_stat.get("nr_descendants")) is not int
                or type(cgroup_stat.get("nr_dying_descendants")) is not int
                or (before and cgroup_stat["nr_descendants"] < 2)
            ):
                raise MeasurementError(
                    "fresh condition parent-residue snapshot is invalid"
                )
            return candidate

        residue_before = verify_residue_snapshot(
            residue.get("before_condition_cgroup_removal"), before=True
        )
        residue_after = verify_residue_snapshot(
            residue.get("after_condition_cgroup_removal"), before=False
        )
        before_stat = residue_before["cgroup_stat"]
        after_stat = residue_after["cgroup_stat"]
        if (
            after_stat["nr_descendants"]
            != before_stat["nr_descendants"] - 1
        ):
            raise MeasurementError(
                "fresh condition parent-residue descendant transition is invalid"
            )
        cgroup_events = _cgroup_integer_map(
            finish["cgroup_events"], label="condition cgroup.events"
        )
        if cgroup_events.get("populated") != 0:
            raise MeasurementError("fresh condition cgroup finish is populated")
        _cgroup_integer_map(
            finish["memory_events"], label="condition memory.events"
        )
        _cgroup_integer_map(
            finish["memory_events_local"],
            label="condition memory.events.local",
        )
        manager_path = _resolve_artifact(
            pair_root, manager_descriptor, "post-condition manager telemetry"
        )
        manager_sample = read_object(manager_path)
        verify_contract(
            manager_sample,
            expected_memory_bytes=resources.MANAGER_MEMORY_MAX_BYTES,
        )
        if _resource_contract_identity(manager_sample) != _resource_contract_identity(proof):
            raise MeasurementError("post-condition manager contract changed")
        condition_resources[condition] = {
            "begin_path": begin_path,
            "entry_path": entry_path,
            "begin": begin,
            "entry_proof": entry_proof,
        }
        sample_summaries.append(
            {
                "after_condition": condition,
                "scope_id": scope_id,
                "condition_cgroup": dict(begin_cgroup),
                "memory_current_end_bytes": finish[
                    "memory_current_end_bytes"
                ],
                "memory_peak_lifetime_bytes": finish[
                    "memory_peak_lifetime_bytes"
                ],
                "memory_events": finish.get("memory_events"),
                "memory_events_local": finish.get("memory_events_local"),
                "pair_parent_residue_diagnostics": dict(residue),
            }
        )
    return {
        "profile_id": slot.get("type_key"),
        "logical_cpus": logical,
        "physical_cores": 4,
        "memory_max_bytes": 16 * 1024**3,
        "samples": sample_summaries,
        "_record_path": str(path),
        "_slot": dict(slot),
        "_proof": proof,
        "_condition_resources": condition_resources,
    }


def _verify_resource(
    pair_root: Path,
    pair: Mapping[str, Any],
    expected_pair: Mapping[str, Any],
    campaign: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    entries = pair.get("condition_resources")
    if entries is None:
        return _verify_one_resource(  # type: ignore[return-value]
            pair_root,
            pair,
            expected_pair,
            campaign,
            condition=None,
        )
    if (
        not isinstance(entries, list)
        or len(entries) != 2
        or [entry.get("condition") for entry in entries] != ["N", "L"]
    ):
        raise MeasurementError("pair lacks separate N and L resource evidence")
    result: dict[str, dict[str, Any]] = {}
    for entry in entries:
        if not isinstance(entry, Mapping):
            raise MeasurementError("pair condition resource entry is malformed")
        condition = str(entry["condition"])
        sample = entry.get("resource_sample")
        if not isinstance(sample, Mapping):
            raise MeasurementError(
                f"condition {condition} lacks its resource sample"
            )
        synthetic_pair = {
            "pair_id": pair.get("pair_id"),
            "hardware_verification_before": pair.get(
                "hardware_verification_before"
            ),
            "hardware_verification_after": pair.get(
                "hardware_verification_after"
            ),
            "resource": entry.get("resource"),
            "resource_proof": entry.get("resource_proof"),
            "resource_worker_proof": entry.get("resource_worker_proof"),
            "resource_samples": [dict(sample)],
            "condition_order": [condition],
        }
        result[condition] = _verify_one_resource(
            pair_root,
            synthetic_pair,
            expected_pair,
            campaign,
            condition=condition,
        )
    return result


def _verify_attempt(
    pair_root: Path,
    expected_pair: Mapping[str, Any],
    descriptor: Mapping[str, Any],
    *,
    benchmark_root: Path,
    results_root: Path,
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
    resource_path: Path,
    resource_proof: Mapping[str, Any],
    condition_resource: Mapping[str, Any],
) -> dict[str, Any]:
    condition = descriptor.get("condition")
    if condition not in ("N", "L"):
        raise MeasurementError("pair attempt has an invalid condition")
    record_descriptor = descriptor.get("record")
    if not isinstance(record_descriptor, Mapping):
        raise MeasurementError(f"pair attempt {condition} has no terminal record")
    record_path = _resolve_artifact(
        pair_root, record_descriptor, f"condition {condition} attempt"
    )
    attempt_root = record_path.parent
    record = read_object(record_path, kind="highambench-measured-attempt")
    _verify_self_hash(record, f"condition {condition} attempt")
    order = expected_pair["condition_order"]
    run_ids = expected_pair["run_ids"]
    if (
        record.get("schema_version") != 3
        or record.get("pair_id") != expected_pair["pair_id"]
        or record.get("task_id") != expected_pair["task_id"]
        or record.get("condition") != condition
        or record.get("run_id") != run_ids[order.index(condition)]
        or record.get("campaign_id") != campaign.get("campaign_id")
        or record.get("campaign_lock_sha256") != campaign.get("record_sha256")
    ):
        raise MeasurementError(f"condition {condition} attempt identity is wrong")
    process_descriptor = descriptor.get("process_log")
    command_descriptor = descriptor.get("command")
    condition_descriptor = descriptor.get("condition_resource")
    entry_descriptor = descriptor.get("condition_entry_proof")
    if (
        not isinstance(descriptor.get("returncode"), int)
        or not isinstance(process_descriptor, Mapping)
        or not isinstance(command_descriptor, Mapping)
        or not isinstance(condition_descriptor, Mapping)
        or not isinstance(entry_descriptor, Mapping)
    ):
        raise MeasurementError(f"condition {condition} lacks outer process evidence")
    _resolve_artifact(
        pair_root, process_descriptor, f"condition {condition} outer process log"
    )
    command_path = _resolve_artifact(
        pair_root, command_descriptor, f"condition {condition} outer command"
    )
    command_record = read_object(command_path, kind="highambench-condition-command")
    begin_path = Path(str(condition_resource["begin_path"]))
    entry_path = Path(str(condition_resource["entry_path"]))
    if (
        _resolve_artifact(
            pair_root, condition_descriptor, "attempt condition resource"
        )
        != begin_path
        or _resolve_artifact(
            pair_root, entry_descriptor, "attempt condition entry proof"
        )
        != entry_path
    ):
        raise MeasurementError(f"condition {condition} outer resource binding changed")
    expected_command = _condition_attempt_command(
        benchmark_root,
        results_root,
        campaign,
        expected_pair,
        str(condition),
        attempt_root,
        resource_path,
        begin_path,
    )
    begin = condition_resource["begin"]
    cgroup = begin.get("cgroup") if isinstance(begin, Mapping) else None
    if not isinstance(cgroup, Mapping):
        raise MeasurementError(f"condition {condition} cgroup identity is missing")
    expected_entry_command = [
        sys.executable,
        str((benchmark_root / "scripts/resources.py").resolve()),
        "_enter-condition-cgroup-and-exec",
        "--cgroup-directory",
        str(cgroup.get("directory")),
        "--expected-device",
        str(cgroup.get("device")),
        "--expected-inode",
        str(cgroup.get("inode")),
        "--expected-cpus",
        resources.format_cpu_list(begin.get("expected_logical_cpus", [])),
        "--proof-file",
        str(entry_path.resolve()),
        "--",
        *expected_command,
    ]
    if (
        command_record.get("condition") != condition
        or command_record.get("condition_argv") != expected_command
        or command_record.get("cgroup_entry_argv") != expected_entry_command
    ):
        raise MeasurementError(f"condition {condition} outer command changed")
    limits = record.get("limits")
    if not isinstance(limits, Mapping) or (
        limits.get("wall_clock_seconds") != 7200
        or limits.get("token_limit") is not None
        or limits.get("token_usage_recorded") is not True
    ):
        raise MeasurementError(f"condition {condition} attempt used the wrong limits")
    if (
        record.get("model") != "gpt-6-sol"
        or record.get("reasoning_effort") != "xhigh"
        or record.get("hidden_chain_of_thought_available") is not False
    ):
        raise MeasurementError(f"condition {condition} agent configuration is wrong")
    runtime_descriptor = record.get("runtime_snapshot")
    resource_descriptor = record.get("resource_record")
    condition_record_descriptor = record.get("condition_resource_record")
    condition_entry_descriptor = record.get("condition_cgroup_entry_proof")
    if not isinstance(runtime_descriptor, Mapping) or not isinstance(
        resource_descriptor, Mapping
    ) or not isinstance(condition_record_descriptor, Mapping) or not isinstance(
        condition_entry_descriptor, Mapping
    ):
        raise MeasurementError(f"condition {condition} lacks runtime/resource binding")
    expected_runtime = _artifact_path(results_root, campaign["runtime_snapshot"])
    runtime_label = runtime_descriptor.get("path")
    if not isinstance(runtime_label, str) or Path(runtime_label).resolve() != expected_runtime:
        raise MeasurementError(f"condition {condition} names the wrong runtime snapshot")
    if (
        runtime_descriptor.get("bytes") != expected_runtime.stat().st_size
        or runtime_descriptor.get("sha256") != sha256_file(expected_runtime)
    ):
        raise MeasurementError(f"condition {condition} runtime descriptor changed")
    if (
        _resolve_artifact(pair_root, resource_descriptor, "attempt resource record")
        != resource_path
    ):
        raise MeasurementError(f"condition {condition} names the wrong resource record")
    if (
        _resolve_artifact(
            pair_root,
            condition_record_descriptor,
            "attempt condition resource record",
        )
        != begin_path
        or _resolve_artifact(
            pair_root,
            condition_entry_descriptor,
            "attempt condition entry proof",
        )
        != entry_path
    ):
        raise MeasurementError(
            f"condition {condition} names the wrong condition resource"
        )
    attempt_resource_proof = record.get("resource_kernel_proof_at_attempt_start")
    if (
        not isinstance(attempt_resource_proof, Mapping)
        or attempt_resource_proof.get("schema_version")
        != resources.SCHEMA_VERSION
        or attempt_resource_proof.get("kind") != "highambench-resource-proof"
        or attempt_resource_proof.get("verified") is not True
        or _resource_contract_identity(attempt_resource_proof)
        != _resource_contract_identity(condition_resource["entry_proof"])
    ):
        raise MeasurementError(f"condition {condition} resource contract changed")
    artifacts = record.get("artifacts")
    if not isinstance(artifacts, Mapping):
        raise MeasurementError(f"condition {condition} has no artifact inventory")
    required_artifacts = {
        "effective_prompt",
        "adapter_process_log",
        "protocol",
        "diagnostics",
        "agent_summary",
        "prompt_start",
        "stop_reason",
        "commands",
        "validations",
        "final_candidate",
    }
    missing = required_artifacts - set(artifacts)
    if missing:
        raise MeasurementError(
            f"condition {condition} lacks telemetry artifacts: {sorted(missing)}"
        )
    malformed = sorted(
        name
        for name in required_artifacts
        if not isinstance(artifacts.get(name), Mapping)
    )
    if malformed:
        raise MeasurementError(
            f"condition {condition} has malformed telemetry descriptors: {malformed}"
        )
    resolved_artifacts = {
        name: _resolve_artifact(attempt_root, value, f"{condition} {name}")
        for name, value in artifacts.items()
        if isinstance(value, Mapping)
    }
    prompt = resolved_artifacts["effective_prompt"].read_bytes()
    task_info = _task_metadata(benchmark_root, str(expected_pair["task_id"]))
    numstability = campaign.get("numstability")
    commit = numstability.get("commit") if isinstance(numstability, Mapping) else None
    expected_prompt = render_effective_prompt(
        benchmark_root,
        task_info,
        str(condition),
        str(commit) if condition == "L" else None,
    )
    if (
        prompt != expected_prompt
        or record.get("prompt_sha256") != sha256_file(resolved_artifacts["effective_prompt"])
        or record.get("prompt_bytes") != len(prompt)
    ):
        raise MeasurementError(f"condition {condition} effective prompt changed")
    if condition == "L":
        if b"/library/docs/LIBRARY_LOOKUP.md" not in prompt:
            raise MeasurementError("condition L prompt omits the library lookup guide")
        dependency = record.get("numstability")
        if (
            not isinstance(dependency, Mapping)
            or dependency.get("access") != "external_read_only"
            or dependency.get("commit") != commit
        ):
            raise MeasurementError("condition L lacks external read-only provenance")
    elif b"LIBRARY_LOOKUP.md" in prompt or record.get("numstability") != {"access": "absent"}:
        raise MeasurementError("condition N leaks NumStability prompt/provenance")

    final_candidate = resolved_artifacts["final_candidate"].read_bytes()
    if record.get("final_candidate_loc") != candidate_loc(final_candidate, str(task_info["target_theorem"])):
        raise MeasurementError(f"condition {condition} final candidate LOC is stale")
    final_candidate_source = record.get("final_candidate_source")
    if (
        final_candidate_source
        not in {"none_observed", "last_observed", "final_on_disk"}
        or (final_candidate_source == "none_observed" and final_candidate != b"")
    ):
        raise MeasurementError(
            f"condition {condition} final candidate provenance is inconsistent"
        )
    agent_summary = read_object(resolved_artifacts["agent_summary"])
    if record.get("agent_summary") != agent_summary:
        raise MeasurementError(f"condition {condition} embedded agent summary changed")
    expected_library = _expected_library_record(runtime, str(condition))
    if (
        agent_summary.get("condition") != condition
        or agent_summary.get("library_runtime") != expected_library
        or agent_summary.get("hidden_chain_of_thought_available") is not False
    ):
        raise MeasurementError(f"condition {condition} adapter provenance is wrong")
    network_audit = agent_summary.get("network_isolation_audit")
    violation_count = (
        network_audit.get("violation_count")
        if isinstance(network_audit, Mapping)
        else None
    )
    if not isinstance(violation_count, int) or violation_count < 0:
        raise MeasurementError(f"condition {condition} has invalid network telemetry")
    if (
        record.get("network_violation_count") != violation_count
        or record.get("rule_violation") is not (violation_count > 0)
    ):
        raise MeasurementError(f"condition {condition} rule telemetry is inconsistent")
    if record.get("infrastructure_failure") is not False:
        raise MeasurementError(f"condition {condition} is an infrastructure failure")
    if agent_summary.get("error") is not None:
        raise MeasurementError(f"condition {condition} adapter reported an error")
    if record.get("token_usage") != agent_summary.get("raw_response_usage"):
        raise MeasurementError(f"condition {condition} token telemetry is inconsistent")
    raw_usage = agent_summary.get("raw_response_usage")
    if not isinstance(raw_usage, Mapping) or raw_usage.get("limit_enforced") is not False:
        raise MeasurementError(f"condition {condition} token limit telemetry is invalid")

    protocol_records = _jsonl_records(
        resolved_artifacts["protocol"], f"condition {condition} protocol", require_nonempty=True
    )
    sequences = [record.get("sequence") for record in protocol_records]
    if sequences != list(range(1, len(protocol_records) + 1)):
        raise MeasurementError(f"condition {condition} protocol sequence is invalid")
    protocol_monotonic = [item.get("monotonic_ns") for item in protocol_records]
    if (
        any(
            not isinstance(value, int) or isinstance(value, bool) or value <= 0
            for value in protocol_monotonic
        )
        or protocol_monotonic != sorted(protocol_monotonic)
    ):
        raise MeasurementError(
            f"condition {condition} protocol monotonic order is invalid"
        )
    forbidden_audit_types = {
        "adapter_error",
        "app_server_protocol_error",
    }
    if any(
        item.get("record_type") == "app_server_protocol"
        and item.get("direction") == "app_server_to_adapter"
        and code_mode_host_launch_failure(item.get("message"))
        for item in protocol_records
    ):
        raise MeasurementError(
            f"condition {condition} contains a Codex code-mode host launch failure"
        )
    if any(
        item.get("record_type") in forbidden_audit_types
        for item in protocol_records
    ):
        raise MeasurementError(
            f"condition {condition} protocol contains an adapter/protocol error"
        )
    host_developer_content: list[Any] = []
    for protocol_record in protocol_records:
        message = protocol_record.get("message")
        if (
            not isinstance(message, Mapping)
            or message.get("method") != "rawResponseItem/completed"
        ):
            continue
        params = message.get("params")
        item = params.get("item") if isinstance(params, Mapping) else None
        if not isinstance(item, Mapping) or item.get("type") != "message":
            continue
        role = item.get("role")
        if role == "assistant":
            break
        if role == "developer":
            host_developer_content.append(item.get("content"))
    if not host_developer_content:
        raise MeasurementError(
            f"condition {condition} exposes no model-visible host developer context"
        )
    host_developer_context_sha256 = hashlib.sha256(
        json.dumps(
            host_developer_content,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
    ).hexdigest()
    adapter_terminal_records = [
        item
        for item in protocol_records
        if item.get("record_type") == "adapter_terminal"
    ]
    adapter_stop_records = [
        item
        for item in protocol_records
        if item.get("record_type") == "adapter_stop_requested"
    ]
    terminal_summary = dict(agent_summary)
    terminal_summary.pop("audit", None)
    terminal_summary.pop("diagnostics", None)
    if (
        len(adapter_terminal_records) != 1
        or protocol_records[-1] != adapter_terminal_records[0]
        or adapter_terminal_records[0].get("summary") != terminal_summary
    ):
        raise MeasurementError(
            f"condition {condition} adapter terminal audit is inconsistent"
        )
    for protocol_record in protocol_records:
        if protocol_record.get("record_type") != "app_server_protocol":
            continue
        raw_json = protocol_record.get("raw_json")
        message = protocol_record.get("message")
        if not isinstance(raw_json, str) or not isinstance(message, Mapping):
            raise MeasurementError(f"condition {condition} protocol wire record is incomplete")
        try:
            parsed_wire = json.loads(raw_json)
        except json.JSONDecodeError as error:
            raise MeasurementError(
                f"condition {condition} protocol raw JSON is invalid"
            ) from error
        if parsed_wire != message:
            raise MeasurementError(
                f"condition {condition} protocol raw JSON differs from parsed message"
            )
    root_lifecycle = _reconstruct_root_lifecycle(protocol_records)
    _verify_single_agent_trace(
        protocol_records, str(root_lifecycle["root_thread_id"])
    )
    adapter_start_records = [
        item
        for item in protocol_records
        if item.get("record_type") == "adapter_start"
    ]
    adapter_start = adapter_start_records[0] if adapter_start_records else None
    if (
        len(adapter_start_records) != 1
        or protocol_records[0] != adapter_start
        or not isinstance(adapter_start, Mapping)
        or adapter_start.get("prompt_sha256") != record.get("prompt_sha256")
        or adapter_start.get("prompt") != prompt.decode("utf-8")
        or adapter_start.get("condition") != condition
        or adapter_start.get("library_runtime") != expected_library
        or adapter_start.get("hidden_chain_of_thought_available") is not False
    ):
        raise MeasurementError(f"condition {condition} protocol prompt is inconsistent")
    provenance = adapter_start.get("provenance")
    if not isinstance(provenance, Mapping) or agent_summary.get("provenance") != provenance:
        raise MeasurementError(f"condition {condition} adapter provenance changed")
    directions = {
        item.get("direction")
        for item in protocol_records
        if item.get("record_type") == "app_server_protocol"
    }
    if directions != {"adapter_to_app_server", "app_server_to_adapter"}:
        raise MeasurementError(f"condition {condition} protocol is not bidirectional")
    turn_start_record = root_lifecycle["turn_start_record"]
    turn_start = turn_start_record["message"]
    turn_params = turn_start.get("params")
    if (
        not isinstance(turn_params, Mapping)
        or turn_params.get("model") != "gpt-6-sol"
        or turn_params.get("effort") != "xhigh"
        or turn_params.get("input") != [{"type": "text", "text": prompt.decode("utf-8")}]
        or turn_params.get("approvalPolicy") != "never"
        or turn_params.get("cwd") != "/workspace"
        or turn_params.get("sandboxPolicy") != {"type": "dangerFullAccess"}
        or turn_params.get("threadId") != root_lifecycle["root_thread_id"]
    ):
        raise MeasurementError(f"condition {condition} turn configuration is wrong")
    recomputed_usage = _recompute_raw_usage(protocol_records)
    if raw_usage != recomputed_usage or record.get("token_usage") != recomputed_usage:
        raise MeasurementError(f"condition {condition} token usage is not protocol-derived")
    termination = agent_summary.get("termination")
    termination_kind = (
        termination.get("kind") if isinstance(termination, Mapping) else None
    )
    base_termination: Mapping[str, Any] | None = (
        termination if isinstance(termination, Mapping) else None
    )
    if termination_kind == "network_violation":
        prior = termination.get("prior")
        base_termination = prior if isinstance(prior, Mapping) else None
    base_kind = (
        base_termination.get("kind")
        if isinstance(base_termination, Mapping)
        else None
    )
    base_control_reason = (
        base_termination.get("control_reason")
        if isinstance(base_termination, Mapping)
        else None
    )
    reported_turn_id = agent_summary.get("turn_id")
    reported_turn_status = agent_summary.get("turn_status")
    if (
        agent_summary.get("thread_id") != root_lifecycle["root_thread_id"]
        or reported_turn_id not in (None, root_lifecycle["root_turn_id"])
        or reported_turn_status not in (None, "completed", "failed", "interrupted")
        or (reported_turn_status is not None and reported_turn_id is None)
    ):
        raise MeasurementError(f"condition {condition} root lifecycle identity is inconsistent")

    natural_termination = termination if isinstance(termination, Mapping) else None
    while (
        isinstance(natural_termination, Mapping)
        and natural_termination.get("kind")
        in ("network_violation", "candidate_missing_or_invalid")
    ):
        prior = natural_termination.get("prior")
        natural_termination = prior if isinstance(prior, Mapping) else None
    if (
        isinstance(natural_termination, Mapping)
        and natural_termination.get("kind") == "natural"
    ):
        if (
            root_lifecycle["turn_response_seen"] is not True
            or root_lifecycle["root_turn_started_seen"] is not True
            or root_lifecycle["root_turn_completed_seen"] is not True
            or reported_turn_id != root_lifecycle["root_turn_id"]
            or reported_turn_status != root_lifecycle["root_terminal_status"]
            or natural_termination.get("turn_status") != reported_turn_status
        ):
            raise MeasurementError(
                f"condition {condition} natural root lifecycle is inconsistent"
            )
    elif not any(
        turn_id == reported_turn_id and status == reported_turn_status
        for turn_id, status, _response_seen in root_lifecycle[
            "reachable_root_states"
        ]
    ):
        raise MeasurementError(
            f"condition {condition} controlled-stop root lifecycle is unreachable"
        )
    natural_complete = bool(
        termination_kind == "natural"
        and reported_turn_status == "completed"
        and agent_summary.get("error") is None
    )
    completion_record = root_lifecycle.get("root_turn_completed_record")
    completion_monotonic_ns = (
        completion_record.get("monotonic_ns")
        if isinstance(completion_record, Mapping)
        else None
    )
    summary_turn_completed = agent_summary.get("turn_completed")
    submission_observed_ns = record.get("submission_observed_monotonic_ns")
    if natural_complete:
        if (
            not isinstance(completion_monotonic_ns, int)
            or isinstance(completion_monotonic_ns, bool)
            or submission_observed_ns != completion_monotonic_ns
            or not isinstance(summary_turn_completed, Mapping)
            or set(summary_turn_completed) != {"unix_ns", "monotonic_ns"}
            or not isinstance(summary_turn_completed.get("unix_ns"), int)
            or not isinstance(summary_turn_completed.get("monotonic_ns"), int)
            or summary_turn_completed["monotonic_ns"] < completion_monotonic_ns
        ):
            raise MeasurementError(
                f"condition {condition} final-submission boundary is inconsistent"
            )
    elif submission_observed_ns is not None:
        raise MeasurementError(
            f"condition {condition} records a submission without natural completion"
        )
    if natural_complete and recomputed_usage["response_count"] < 1:
        raise MeasurementError(
            f"condition {condition} completed naturally without raw token usage"
        )
    if record.get("token_usage_complete") is not natural_complete:
        raise MeasurementError(f"condition {condition} token completeness is wrong")
    _jsonl_records(
        resolved_artifacts["diagnostics"],
        f"condition {condition} diagnostics",
        require_nonempty=False,
    )
    command_records = _jsonl_records(
        resolved_artifacts["commands"],
        f"condition {condition} commands",
        require_nonempty=True,
    )
    expected_adapter_command = _expected_adapter_command(
        benchmark_root,
        results_root,
        attempt_root,
        str(condition),
        campaign,
        runtime,
        resolved_artifacts,
    )
    recorded_adapter_command = (
        command_records[0].get("argv") if len(command_records) == 1 else None
    )
    if (
        len(command_records) != 1
        or command_records[0].get("kind") != "host-command"
        or command_records[0].get("role") != "observed_codex_adapter"
        or not isinstance(recorded_adapter_command, list)
        or len(recorded_adapter_command) != len(expected_adapter_command)
        or recorded_adapter_command[1:] != expected_adapter_command[1:]
        or not _same_executable_target(
            recorded_adapter_command[0], expected_adapter_command[0]
        )
    ):
        raise MeasurementError(f"condition {condition} adapter command changed")
    bubblewrap_argv = provenance.get("bubblewrap_argv")
    if (
        provenance.get("adapter_argv") != expected_adapter_command[1:]
        or provenance.get("model") != "gpt-6-sol"
        or provenance.get("root_reasoning_effort") != "xhigh"
        or provenance.get("subagents_enabled") is not False
        or provenance.get("max_concurrent_threads_per_session") != 1
        or provenance.get("parallel_subagents_enabled") is not False
        or provenance.get("rollout_budget_configured") is not False
        or provenance.get("token_limit_configured") is not False
        or provenance.get("provider_token_gate_configured") is not False
        or provenance.get("codex_config_overrides")
        != list(PROVIDER_CONFIG_OVERRIDES)
        or provenance.get("disabled_features")
        != list(PROVIDER_DISABLED_FEATURES)
        or provenance.get("enabled_features") != []
        or not isinstance(bubblewrap_argv, list)
    ):
        raise MeasurementError(f"condition {condition} adapter configuration changed")
    adapter_path = benchmark_root / "scripts/observed_codex.py"
    codex_identity = campaign["agent"]
    code_mode_host_path, code_mode_host_identity = _authenticated_code_mode_host(
        campaign
    )
    offline_shell_path = _artifact_path(results_root, campaign["offline_shell"])
    if (
        provenance.get("adapter_path") != str(adapter_path.resolve())
        or provenance.get("adapter_sha256") != sha256_file(adapter_path)
        or provenance.get("codex_path") != str(Path(str(codex_identity["path"])).resolve())
        or provenance.get("codex_sha256") != codex_identity.get("sha256")
        or provenance.get("code_mode_host_path") != str(code_mode_host_path)
        or provenance.get("code_mode_host_sha256")
        != code_mode_host_identity.get("sha256")
        or provenance.get("offline_shell_path") != str(offline_shell_path)
        or provenance.get("offline_shell_sha256") != sha256_file(offline_shell_path)
    ):
        raise MeasurementError(f"condition {condition} adapter binary provenance changed")
    expected_bwrap = str(
        Path(str(campaign["runtime_tools"]["bubblewrap"]["path"])).resolve()
    )
    if (
        not bubblewrap_argv
        or bubblewrap_argv[0] != expected_bwrap
        or "--unshare-all" not in bubblewrap_argv
        or "--share-net" not in bubblewrap_argv
    ):
        raise MeasurementError(f"condition {condition} bubblewrap command is wrong")
    mounts = _mount_table(bubblewrap_argv)
    if condition == "N":
        if any(
            isinstance(value, str) and value.startswith("/library")
            for value in bubblewrap_argv
        ):
            raise MeasurementError("condition N received a library mount or path")
    expected_mounts = _expected_provider_mounts(
        attempt_root=attempt_root,
        results_root=results_root,
        campaign=campaign,
        runtime=runtime,
        condition=str(condition),
        actual=mounts,
    )
    if mounts != expected_mounts:
        missing_mounts = sorted(set(expected_mounts) - set(mounts))
        unexpected_mounts = sorted(set(mounts) - set(expected_mounts))
        changed_mounts = sorted(
            destination
            for destination in set(mounts) & set(expected_mounts)
            if mounts[destination] != expected_mounts[destination]
        )
        raise MeasurementError(
            f"condition {condition} provider mount table differs from campaign: "
            f"missing={missing_mounts}, unexpected={unexpected_mounts}, "
            f"changed={changed_mounts}"
        )
    expected_bubblewrap_argv = _expected_provider_bubblewrap_argv(
        attempt_root=attempt_root,
        results_root=results_root,
        campaign=campaign,
        runtime=runtime,
        condition=str(condition),
        actual=bubblewrap_argv,
    )
    if bubblewrap_argv != expected_bubblewrap_argv:
        raise MeasurementError(
            f"condition {condition} provider Bubblewrap argv differs from "
            "the exact ordered runner command"
        )
    validation_records = _jsonl_records(
        resolved_artifacts["validations"],
        f"condition {condition} validations",
        require_nonempty=False,
    )
    if validation_records and record.get("validation") != validation_records[-1]:
        raise MeasurementError(f"condition {condition} final validation log is inconsistent")
    if not validation_records and record.get("validation") is not None:
        raise MeasurementError(
            f"condition {condition} embeds validation absent from its log"
        )
    _verify_validation_commands(
        benchmark_root,
        attempt_root,
        task_info,
        str(condition),
        campaign,
        runtime,
        validation_records,
    )
    _verify_validation_result_semantics(
        benchmark_root,
        task_info,
        str(condition),
        validation_records,
        expected_final_candidate_sha256=(
            hashlib.sha256(final_candidate).hexdigest()
            if record.get("pass") is not True
            and record.get("failure_code") != "TIME_LIMIT"
            and record.get("rule_violation") is False
            else None
        ),
    )
    prompt_start = read_object(resolved_artifacts["prompt_start"])
    prompt_start_ns = prompt_start.get("monotonic_ns")
    deadline_ns = record.get("deadline_monotonic_ns")
    finished_ns = record.get("attempt_finished_monotonic_ns")
    turn_raw = turn_start_record.get("raw_json")
    if (
        prompt_start.get("schema_version") != 1
        or prompt_start.get("kind") != "highambench_prompt_started"
        or prompt_start.get("model") != "gpt-6-sol"
        or prompt_start.get("reasoning_effort") != "xhigh"
        or prompt_start.get("prompt_sha256") != record.get("prompt_sha256")
        or prompt_start.get("thread_id") != root_lifecycle["root_thread_id"]
        or prompt_start_ns != record.get("prompt_started_monotonic_ns")
        or prompt_start.get("temporary_auth_removed") is not True
        or prompt_start.get("turn_start_flushed") is not True
        or not isinstance(turn_raw, str)
        or prompt_start.get("turn_start_wire_sha256")
        != hashlib.sha256((turn_raw + "\n").encode("utf-8")).hexdigest()
        or not isinstance(prompt_start_ns, int)
        or not isinstance(deadline_ns, int)
        or deadline_ns != prompt_start_ns + 7_200_000_000_000
        or not isinstance(finished_ns, int)
        or finished_ns < prompt_start_ns
    ):
        raise MeasurementError(f"condition {condition} prompt-start marker is inconsistent")
    marker_records = [
        item
        for item in protocol_records
        if item.get("record_type") == "prompt_start_marker_written"
    ]
    if len(marker_records) != 1 or marker_records[0].get("marker") != prompt_start:
        raise MeasurementError(f"condition {condition} prompt-start audit is inconsistent")
    if (
        not isinstance(adapter_start.get("monotonic_ns"), int)
        or not isinstance(turn_start_record.get("monotonic_ns"), int)
        or not isinstance(marker_records[0].get("monotonic_ns"), int)
        or adapter_start["monotonic_ns"] > turn_start_record["monotonic_ns"]
        or turn_start_record["monotonic_ns"] > prompt_start_ns
        or prompt_start_ns > marker_records[0]["monotonic_ns"]
    ):
        raise MeasurementError(f"condition {condition} prompt chronology is invalid")
    stop_reason = read_object(resolved_artifacts["stop_reason"])
    teardown = record.get("teardown")
    stop_requested_ns = stop_reason.get("requested_monotonic_ns")
    teardown_requested_ns = (
        teardown.get("requested_monotonic_ns")
        if isinstance(teardown, Mapping)
        else None
    )
    teardown_completed_ns = (
        teardown.get("completed_monotonic_ns")
        if isinstance(teardown, Mapping)
        else None
    )
    stop_kind = stop_reason.get("reason")
    terminal_monotonic_ns = adapter_terminal_records[0].get("monotonic_ns")
    natural_outer_stop = stop_kind == "agent_turn_completed"
    expected_stop_keys = {
        "reason",
        "requested_at_utc",
        "requested_monotonic_ns",
        "pid",
    }
    if natural_outer_stop:
        expected_stop_keys.add("signal_sent")
    expected_teardown_keys = {
        "reason",
        "signal",
        "returncode",
        "requested_monotonic_ns",
        "completed_monotonic_ns",
        "completed_at_utc",
    }
    if (
        not isinstance(teardown, Mapping)
        or set(stop_reason) != expected_stop_keys
        or set(teardown) != expected_teardown_keys
        or stop_kind != teardown.get("reason")
        or stop_kind not in {"agent_turn_completed", "time_limit"}
        or not isinstance(stop_reason.get("pid"), int)
        or isinstance(stop_reason.get("pid"), bool)
        or stop_reason["pid"] <= 0
        or not isinstance(stop_reason.get("requested_at_utc"), str)
        or not stop_reason["requested_at_utc"]
        or not isinstance(stop_requested_ns, int)
        or isinstance(stop_requested_ns, bool)
        or teardown_requested_ns != stop_requested_ns
        or not isinstance(teardown_completed_ns, int)
        or isinstance(teardown_completed_ns, bool)
        or teardown_completed_ns < stop_requested_ns
        or teardown_completed_ns
        > stop_requested_ns + PROCESS_TEARDOWN_GRACE_NS
        or not isinstance(teardown.get("completed_at_utc"), str)
        or not teardown["completed_at_utc"]
        or finished_ns < teardown_completed_ns
        or finished_ns
        > teardown_completed_ns + ATTEMPT_FINALIZATION_GRACE_NS
        or not isinstance(terminal_monotonic_ns, int)
        or terminal_monotonic_ns > teardown_completed_ns
    ):
        raise MeasurementError(f"condition {condition} stop reason is inconsistent")
    if natural_outer_stop:
        if (
            stop_reason.get("signal_sent") is not False
            or teardown.get("signal") is not None
            or terminal_monotonic_ns > stop_requested_ns
            or adapter_stop_records
        ):
            raise MeasurementError(
                f"condition {condition} natural termination evidence is inconsistent"
            )
    else:
        if (
            teardown.get("signal") != "SIGTERM"
            or len(adapter_stop_records) != 1
            or adapter_stop_records[0].get("stop") != base_termination
            or not isinstance(adapter_stop_records[0].get("monotonic_ns"), int)
            or adapter_stop_records[0]["monotonic_ns"] < stop_requested_ns
            or adapter_stop_records[0]["monotonic_ns"] > terminal_monotonic_ns
            or terminal_monotonic_ns < stop_requested_ns
        ):
            raise MeasurementError(
                f"condition {condition} controlled-stop audit is inconsistent"
            )

    if termination_kind == "network_violation":
        expected_adapter_returncode = 1
    elif base_kind == "interrupted_for_accepted_candidate":
        expected_adapter_returncode = 0
    elif base_kind == "control_stop":
        expected_adapter_returncode = 130
    elif base_kind == "natural":
        expected_adapter_returncode = (
            0 if agent_summary.get("turn_status") == "completed" else 1
        )
    elif base_kind == "candidate_missing_or_invalid":
        expected_adapter_returncode = 1
    else:
        expected_adapter_returncode = None
    if (
        expected_adapter_returncode is None
        or agent_summary.get("return_code") != expected_adapter_returncode
        or teardown.get("returncode") != expected_adapter_returncode
    ):
        raise MeasurementError(
            f"condition {condition} adapter/outer return codes are inconsistent"
        )

    process_teardown = agent_summary.get("process_teardown")
    inner_started = (
        process_teardown.get("started")
        if isinstance(process_teardown, Mapping)
        else None
    )
    inner_completed = (
        process_teardown.get("completed")
        if isinstance(process_teardown, Mapping)
        else None
    )
    timestamp_keys = {"unix_ns", "monotonic_ns"}
    if (
        not isinstance(process_teardown, Mapping)
        or set(process_teardown)
        != {"started", "completed", "signal_sent", "returncode"}
        or not isinstance(inner_started, Mapping)
        or not isinstance(inner_completed, Mapping)
        or set(inner_started) != timestamp_keys
        or set(inner_completed) != timestamp_keys
        or any(
            not isinstance(value, int)
            or isinstance(value, bool)
            or value <= 0
            for value in (*inner_started.values(), *inner_completed.values())
        )
        or inner_started["monotonic_ns"] < prompt_start_ns
        or inner_completed["monotonic_ns"] < inner_started["monotonic_ns"]
        or inner_completed["monotonic_ns"] > terminal_monotonic_ns
        or process_teardown.get("signal_sent") not in (None, "SIGTERM", "SIGKILL")
        or not isinstance(process_teardown.get("returncode"), int)
        or isinstance(process_teardown.get("returncode"), bool)
    ):
        raise MeasurementError(
            f"condition {condition} provider-process teardown is inconsistent"
        )
    if (
        not natural_outer_stop
        and inner_started["monotonic_ns"] < stop_requested_ns
    ):
        raise MeasurementError(
            f"condition {condition} provider teardown predates its stop request"
        )
    if stop_kind == "time_limit":
        if not (
            deadline_ns <= stop_requested_ns
            <= deadline_ns + STOP_DEADLINE_TOLERANCE_NS
        ):
            raise MeasurementError(
                f"condition {condition} time-limit teardown missed its deadline"
            )
    elif not (
        natural_complete
        and isinstance(submission_observed_ns, int)
        and not isinstance(submission_observed_ns, bool)
    ):
        raise MeasurementError(
            f"condition {condition} natural stop lacks a submission boundary"
        )
    for summary_key, artifact_key in (("audit", "protocol"), ("diagnostics", "diagnostics")):
        summary_descriptor = agent_summary.get(summary_key)
        if (
            not isinstance(summary_descriptor, Mapping)
            or summary_descriptor.get("sha256")
            != sha256_file(resolved_artifacts[artifact_key])
        ):
            raise MeasurementError(
                f"condition {condition} adapter {summary_key} digest is inconsistent"
            )

    passed = record.get("pass") is True
    final_validation = validation_records[-1] if validation_records else None
    if passed:
        status_consistent = bool(
            record.get("failure_code") is None
            and record.get("rule_violation") is False
            and stop_kind == "agent_turn_completed"
            and base_kind == "natural"
            and natural_complete
            and isinstance(final_validation, Mapping)
            and final_validation.get("pass") is True
        )
    elif record.get("rule_violation") is True:
        status_consistent = bool(
            record.get("failure_code") == "RULE_VIOLATION"
            and termination_kind == "network_violation"
        )
    elif record.get("failure_code") == "TIME_LIMIT":
        status_consistent = bool(
            (
                stop_kind == "time_limit"
                and base_kind == "control_stop"
                and base_control_reason == "time_limit"
            )
            or (
                stop_kind == "agent_turn_completed"
                and base_kind == "natural"
                and natural_complete
                and isinstance(submission_observed_ns, int)
                and submission_observed_ns >= deadline_ns
                and final_validation is None
            )
        )
    else:
        expected_failure = (
            final_validation.get("failure_code") or "PROOF_FAILURE"
            if isinstance(final_validation, Mapping)
            else "NO_SUBMISSION"
        )
        status_consistent = bool(
            stop_kind == "agent_turn_completed"
            and record.get("failure_code") == expected_failure
            and base_kind in {"natural", "candidate_missing_or_invalid"}
            and (
                not isinstance(final_validation, Mapping)
                or final_validation.get("pass") is not True
            )
        )
    if not status_consistent:
        raise MeasurementError(
            f"condition {condition} pass/failure/termination status is inconsistent"
        )
    expected_returncode = 0 if passed else 1
    if descriptor.get("returncode") != expected_returncode:
        raise MeasurementError(f"condition {condition} outer return code is inconsistent")
    if len(validation_records) > 1:
        raise MeasurementError(
            f"condition {condition} validated an intermediate candidate"
        )
    prior_validation_finish = (
        submission_observed_ns
        if isinstance(submission_observed_ns, int)
        else prompt_start_ns
    )
    for validation_record in validation_records:
        validation_start = validation_record.get("validation_started_monotonic_ns")
        validation_finish = validation_record.get("validation_finished_monotonic_ns")
        if (
            not isinstance(validation_start, int)
            or not isinstance(validation_finish, int)
            or validation_start < prior_validation_finish
            or validation_finish < validation_start
            or validation_finish > stop_requested_ns
            or not isinstance(validation_record.get("candidate_sha256"), str)
        ):
            raise MeasurementError(f"condition {condition} validation chronology is invalid")
        prior_validation_finish = validation_finish
    proof_lines = None
    if passed:
        proof_descriptor = artifacts.get("accepted_proof")
        if not isinstance(proof_descriptor, Mapping):
            raise MeasurementError(f"passing condition {condition} has no accepted proof")
        proof_path = _resolve_artifact(
            attempt_root, proof_descriptor, f"condition {condition} accepted proof"
        )
        observed_loc = proof_loc(proof_path.read_bytes(), str(task_info["target_theorem"]))
        if record.get("proof_loc") != observed_loc:
            raise MeasurementError(f"condition {condition} proof LOC is stale")
        validation = record.get("validation")
        if not isinstance(validation, Mapping) or validation.get("pass") is not True:
            raise MeasurementError(f"condition {condition} pass lacks validation evidence")
        if validation.get("candidate_sha256") != sha256_file(proof_path):
            raise MeasurementError(
                f"condition {condition} proof differs from validated candidate"
            )
        first_valid = record.get("first_valid_seconds")
        if (
            not isinstance(submission_observed_ns, int)
            or submission_observed_ns < prompt_start_ns
            or submission_observed_ns >= deadline_ns
            or not isinstance(first_valid, (int, float))
            or isinstance(first_valid, bool)
            or first_valid < 0
            or first_valid >= 7200
            or round(
                (submission_observed_ns - prompt_start_ns) / 1_000_000_000,
                6,
            )
            != first_valid
        ):
            raise MeasurementError(f"condition {condition} first-valid timing is invalid")
        if violation_count != 0:
            raise MeasurementError(
                f"passing condition {condition} made a denied network request"
            )
        proof_lines = observed_loc["proof_region_nonblank_non_line_comment_lines"]
    elif record.get("first_valid_seconds") is not None:
        validation = record.get("validation")
        first_valid = record.get("first_valid_seconds")
        if (
            record.get("rule_violation") is not True
            or not isinstance(validation, Mapping)
            or validation.get("pass") is not True
            or not isinstance(submission_observed_ns, int)
            or submission_observed_ns < prompt_start_ns
            or submission_observed_ns >= deadline_ns
            or not isinstance(first_valid, (int, float))
            or isinstance(first_valid, bool)
            or round(
                (submission_observed_ns - prompt_start_ns) / 1_000_000_000,
                6,
            )
            != first_valid
        ):
            raise MeasurementError(f"condition {condition} first-valid timing is invalid")
    expected_post_validation_seconds = (
        round(
            (
                final_validation["validation_finished_monotonic_ns"]
                - final_validation["validation_started_monotonic_ns"]
            )
            / 1_000_000_000,
            6,
        )
        if isinstance(final_validation, Mapping)
        and isinstance(final_validation.get("validation_started_monotonic_ns"), int)
        and isinstance(final_validation.get("validation_finished_monotonic_ns"), int)
        else None
    )
    if (
        record.get("post_submission_validation_seconds")
        != expected_post_validation_seconds
        or record.get("time_measurement")
        != (
            "authenticated CLOCK_MONOTONIC prompt release to root turn/completed; "
            "hidden validation begins after the submission boundary and is excluded"
        )
    ):
        raise MeasurementError(
            f"condition {condition} time-boundary accounting is inconsistent"
        )
    if record.get("token_usage") is None:
        raise MeasurementError(f"condition {condition} has no recorded token usage")
    wall_time_seconds = (
        round((submission_observed_ns - prompt_start_ns) / 1_000_000_000, 6)
        if isinstance(submission_observed_ns, int)
        and submission_observed_ns < deadline_ns
        else 7200.0
        if record.get("failure_code") == "TIME_LIMIT"
        else round((stop_requested_ns - prompt_start_ns) / 1_000_000_000, 6)
    )
    reported_loc = (
        record.get("proof_loc") if passed else record.get("final_candidate_loc")
    )
    library_declarations: list[str] = []
    if condition == "L" and isinstance(final_validation, Mapping):
        raw_declarations = final_validation.get("library_declarations")
        if isinstance(raw_declarations, list):
            library_declarations = sorted(
                {
                    str(declaration["name"])
                    for declaration in raw_declarations
                    if isinstance(declaration, Mapping)
                    and isinstance(declaration.get("name"), str)
                }
            )
    return {
        "condition": condition,
        "run_id": record.get("run_id"),
        "paper_id": record.get("paper_id"),
        "task_id": record.get("task_id"),
        "category": record.get("category"),
        "pass": passed,
        "failure_code": record.get("failure_code"),
        "first_valid_seconds": record.get("first_valid_seconds"),
        "wall_time_seconds": wall_time_seconds,
        "token_usage": record.get("token_usage"),
        "token_usage_complete": record.get("token_usage_complete"),
        "proof_loc": proof_lines,
        "final_loc": reported_loc,
        "loc_status": "accepted" if passed else "unaccepted_final_candidate",
        "numstability_declarations": library_declarations,
        "started_at_utc": record.get("started_at_utc"),
        "finished_at_utc": record.get("finished_at_utc"),
        "prompt_started_monotonic_ns": prompt_start_ns,
        "attempt_finished_monotonic_ns": finished_ns,
        "host_developer_context_sha256": host_developer_context_sha256,
    }


def _utc_timestamp(value: Any, label: str) -> float:
    if not isinstance(value, str) or not value.endswith("Z"):
        raise MeasurementError(f"{label} is not a UTC timestamp")
    try:
        return datetime.fromisoformat(value[:-1] + "+00:00").timestamp()
    except ValueError as error:
        raise MeasurementError(f"{label} is not a valid UTC timestamp") from error


def _verify_serial_provider_schedule(
    pairs: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Prove that one authentication never had two measured attempts active."""

    intervals: list[dict[str, Any]] = []
    for pair in pairs:
        pair_id = str(pair.get("pair_id"))
        order = pair.get("condition_order")
        attempts = pair.get("attempts")
        if order not in (["N", "L"], ["L", "N"]) or not isinstance(attempts, list):
            raise MeasurementError(f"pair {pair_id} lacks a serial condition order")
        by_condition = {
            str(attempt.get("condition")): attempt
            for attempt in attempts
            if isinstance(attempt, Mapping)
        }
        if set(by_condition) != {"N", "L"}:
            raise MeasurementError(f"pair {pair_id} lacks exact N/L timing records")
        pair_intervals: list[dict[str, Any]] = []
        for condition in order:
            attempt = by_condition[condition]
            start = _utc_timestamp(
                attempt.get("started_at_utc"), f"{pair_id}/{condition} start"
            )
            finish = _utc_timestamp(
                attempt.get("finished_at_utc"), f"{pair_id}/{condition} finish"
            )
            if finish < start:
                raise MeasurementError(f"{pair_id}/{condition} finishes before it starts")
            interval = {
                "pair_id": pair_id,
                "condition": condition,
                "started_at_utc": attempt["started_at_utc"],
                "finished_at_utc": attempt["finished_at_utc"],
                "_start": start,
                "_finish": finish,
            }
            pair_intervals.append(interval)
            intervals.append(interval)
        if pair_intervals[1]["_start"] < pair_intervals[0]["_finish"]:
            raise MeasurementError(
                f"pair {pair_id} overlaps conditions or violates its counterbalanced order"
            )

    chronological = sorted(intervals, key=lambda item: item["_start"])
    for previous, current in zip(chronological, chronological[1:]):
        if current["_start"] < previous["_finish"]:
            raise MeasurementError(
                "measured provider attempts overlap: "
                f"{previous['pair_id']}/{previous['condition']} and "
                f"{current['pair_id']}/{current['condition']}"
            )
    return {
        "provider_active_attempt_limit_per_authentication": 1,
        "verified_attempt_count": len(chronological),
        "overlap_count": 0,
        "condition_order_enforced": True,
    }


def _median(values: Sequence[int | float | None]) -> float | None:
    present = [
        float(value)
        for value in values
        if isinstance(value, (int, float)) and not isinstance(value, bool)
    ]
    return float(statistics.median(present)) if present else None


def _direct_performance_rows(
    attempts: Sequence[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Summarize N and L independently without computing condition differences."""

    scopes: list[tuple[str, str, list[Mapping[str, Any]]]] = [
        ("overall", "overall", list(attempts))
    ]
    scopes.extend(
        ("category", category, [attempt for attempt in attempts if attempt.get("category") == category])
        for category in ("C1", "C2", "C3")
    )
    task_ids = sorted(
        {
            str(attempt["task_id"])
            for attempt in attempts
            if isinstance(attempt.get("task_id"), str)
        }
    )
    scopes.extend(
        (
            "task",
            task_id,
            [attempt for attempt in attempts if attempt.get("task_id") == task_id],
        )
        for task_id in task_ids
    )
    rows: list[dict[str, Any]] = []
    for scope_type, scope, scoped in scopes:
        for condition in ("N", "L"):
            selected = [
                attempt
                for attempt in scoped
                if attempt.get("condition") == condition
            ]
            if not selected:
                continue
            token_values = [
                usage.get("total_tokens") if isinstance(usage, Mapping) else None
                for usage in (attempt.get("token_usage") for attempt in selected)
            ]
            physical_lines = [
                loc.get("physical_lines") if isinstance(loc, Mapping) else None
                for loc in (attempt.get("final_loc") for attempt in selected)
            ]
            proof_lines = [
                (
                    loc.get("proof_region_nonblank_non_line_comment_lines")
                    if isinstance(loc, Mapping)
                    else None
                )
                for loc in (attempt.get("final_loc") for attempt in selected)
            ]
            passes = sum(attempt.get("pass") is True for attempt in selected)
            rows.append(
                {
                    "scope_type": scope_type,
                    "scope": scope,
                    "condition": condition,
                    "attempts": len(selected),
                    "passes": passes,
                    "success_rate": passes / len(selected),
                    "median_wall_time_seconds": _median(
                        [attempt.get("wall_time_seconds") for attempt in selected]
                    ),
                    "median_total_tokens": _median(token_values),
                    "attempts_with_token_measurement": sum(
                        value is not None for value in token_values
                    ),
                    "median_final_physical_lines": _median(physical_lines),
                    "median_final_proof_loc": _median(proof_lines),
                    "attempts_with_final_loc": sum(
                        value is not None for value in physical_lines
                    ),
                }
            )
    return rows


def _verify_outer_terminal(
    benchmark_root: Path,
    results_root: Path,
    pair_root: Path,
    pair_path: Path,
    expected: Mapping[str, Any],
    campaign: Mapping[str, Any],
    slots_by_condition: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    terminal_path = resolved_regular_file(
        pair_root / "outer_terminal.json", label="pair outer terminal"
    )
    terminal = read_object(
        terminal_path, kind="highambench-pair-outer-terminal"
    )
    _verify_self_hash(terminal, "pair outer terminal")
    if (
        terminal.get("schema_version") != 2
        or terminal.get("pair_id") != expected.get("pair_id")
        or terminal.get("campaign_id") != campaign.get("campaign_id")
        or terminal.get("campaign_lock_sha256") != campaign.get("record_sha256")
        or terminal.get("returncode") != 0
        or terminal.get("complete") is not True
    ):
        raise MeasurementError("pair outer terminal identity/status is invalid")
    pair_descriptor = terminal.get("pair")
    condition_terminals = terminal.get("condition_terminals")
    if (
        not isinstance(pair_descriptor, Mapping)
        or not isinstance(condition_terminals, list)
        or len(condition_terminals) != 2
    ):
        raise MeasurementError("pair outer terminal lacks artifact bindings")
    if _resolve_artifact(pair_root, pair_descriptor, "outer pair artifact") != pair_path:
        raise MeasurementError("pair outer terminal points to a different pair record")
    launch_summaries: dict[str, Any] = {}
    seen: set[str] = set()
    for terminal_descriptor in condition_terminals:
        if not isinstance(terminal_descriptor, Mapping):
            raise MeasurementError("condition terminal descriptor is malformed")
        condition_terminal_path = _resolve_artifact(
            pair_root, terminal_descriptor, "condition outer terminal"
        )
        condition_terminal = read_object(
            condition_terminal_path, kind="highambench-condition-outer-terminal"
        )
        _verify_self_hash(condition_terminal, "condition outer terminal")
        condition = condition_terminal.get("condition")
        if (
            condition not in ("N", "L")
            or condition in seen
            or condition_terminal_path
            != pair_root / f"condition-{condition}.outer_terminal.json"
            or condition_terminal.get("pair_id") != expected.get("pair_id")
            or condition_terminal.get("campaign_id") != campaign.get("campaign_id")
            or condition_terminal.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
            or condition_terminal.get("returncode") != 0
            or condition_terminal.get("complete") is not True
        ):
            raise MeasurementError("condition outer terminal is invalid")
        seen.add(str(condition))
        slot = slots_by_condition.get(str(condition))
        launch_descriptor = condition_terminal.get("launch")
        if not isinstance(slot, Mapping) or not isinstance(
            launch_descriptor, Mapping
        ):
            raise MeasurementError("condition terminal lacks its slot or launch")
        launch_path = _resolve_artifact(
            pair_root, launch_descriptor, "condition launch record"
        )
        launch = read_object(launch_path, kind="highambench-condition-launch")
        _verify_self_hash(launch, "condition launch record")
        if (
            launch_path != pair_root / f"launch_{condition}.json"
            or launch.get("pair_id") != expected.get("pair_id")
            or launch.get("condition") != condition
            or launch.get("campaign_id") != campaign.get("campaign_id")
            or launch.get("campaign_lock_sha256") != campaign.get("record_sha256")
            or launch.get("slot") != slot
            or launch.get("returncode") != 0
            or launch.get("launcher") != "privileged-cpu-guard"
        ):
            raise MeasurementError("condition launch identity/status is invalid")
        lease_id = launch.get("cpu_guard_lease_id")
        if (
            not isinstance(lease_id, str)
            or _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None
        ):
            raise MeasurementError(
                "condition launch CPU-guard lease identity is invalid"
            )
        log_descriptor = launch.get("log")
        if not isinstance(log_descriptor, Mapping):
            raise MeasurementError("condition launch lacks its CPU-guard log")
        _resolve_artifact(pair_root, log_descriptor, "CPU-guard launch log")
        slot_path = resolved_regular_file(
            pair_root / f"resource_slot_{condition}.json",
            label="condition resource slot",
        )
        if read_object(slot_path) != slot:
            raise MeasurementError("condition resource slot file changed")
        unit = launch.get("unit")
        if not isinstance(unit, str):
            raise MeasurementError("condition launch unit is invalid")
        child = _condition_worker_command(
            benchmark_root, results_root, expected, str(condition), slot_path
        )
        expected_command = _cpu_guard_launch_command(
            lease_id,
            unit,
            slot,
            child,
            working_directory=_repository_root(benchmark_root),
            proof_file=pair_root / f"resource_kernel_proof_{condition}.json",
        )
        if launch.get("command") != expected_command:
            raise MeasurementError("condition CPU-guard launch command changed")
        launch_summaries[str(condition)] = {
            "unit": unit,
            "cpu_guard_lease_id": lease_id,
            "launch_sha256": sha256_file(launch_path),
            "terminal_sha256": sha256_file(condition_terminal_path),
        }
    if seen != {"N", "L"}:
        raise MeasurementError("pair outer terminal lacks N or L")
    return {
        "condition_launches": launch_summaries,
        "terminal_sha256": sha256_file(terminal_path),
    }


def _verify_campaign_events(
    results_root: Path,
    campaign: Mapping[str, Any],
    verified_pairs: Sequence[Mapping[str, Any]],
    input_verification: Mapping[str, Any],
    *,
    expected_pairs: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    event_path = results_root / "campaign_events.jsonl"
    if not verified_pairs and not event_path.exists():
        return {"event_count": 0, "pair_terminal_events": 0}
    event_path = resolved_regular_file(event_path, label="campaign event log")
    events = _jsonl_records(event_path, "campaign event log", require_nonempty=True)
    allowed_kinds = {
        "campaign-preflight",
        "host-core-locks-acquired",
        "pair-terminal",
        "campaign-terminal",
        "campaign-recovery-terminal",
    }
    expected_slots = campaign.get("resource_slots")
    if not isinstance(expected_slots, list) or not expected_slots:
        raise MeasurementError("campaign has no locked resource slots")
    expected_pair_by_id = (
        {
            str(pair.get("pair_id")): pair
            for pair in expected_pairs
            if isinstance(pair.get("pair_id"), str)
        }
        if expected_pairs is not None
        else None
    )

    def expected_pair(pair_id: str) -> Mapping[str, Any]:
        if expected_pair_by_id is None:
            return {"pair_id": pair_id}
        expected = expected_pair_by_id.get(pair_id)
        if expected is None:
            raise MeasurementError(
                f"campaign terminal names unknown pair {pair_id}"
            )
        return expected
    expected_cores: list[tuple[int, int, int]] = []

    def core_identity(value: object, label: str) -> tuple[int, int, int]:
        if not isinstance(value, Mapping):
            raise MeasurementError(f"{label} is not an object")
        try:
            identity = (
                int(value["package_id"]),
                int(value["die_id"]),
                int(value["core_id"]),
            )
        except (KeyError, TypeError, ValueError) as error:
            raise MeasurementError(f"{label} is invalid") from error
        return identity

    for slot in expected_slots:
        cores = slot.get("cores") if isinstance(slot, Mapping) else None
        if not isinstance(cores, list):
            raise MeasurementError("campaign resource slot has no core identities")
        for core in cores:
            if not isinstance(core, Mapping):
                raise MeasurementError("campaign resource slot has an invalid core")
            expected_cores.append(core_identity(core, "campaign physical core"))
    if len(expected_cores) != len(set(expected_cores)):
        raise MeasurementError("campaign resource slots overlap physical cores")
    expected_slot_lists: list[str] = []
    expected_slot_core_lists: list[list[str]] = []
    expected_reserved_cpus: set[int] = set()
    for slot in expected_slots:
        cpus = slot.get("logical_cpus") if isinstance(slot, Mapping) else None
        if (
            not isinstance(cpus, list)
            or not cpus
            or any(isinstance(cpu, bool) or not isinstance(cpu, int) for cpu in cpus)
        ):
            raise MeasurementError("campaign CPU-guard slot is malformed")
        if expected_reserved_cpus.intersection(cpus):
            raise MeasurementError("campaign CPU-guard slots overlap")
        expected_reserved_cpus.update(cpus)
        expected_slot_lists.append(resources.format_cpu_list(cpus))
        cores = slot.get("cores") if isinstance(slot, Mapping) else None
        if not isinstance(cores, list) or len(cores) != 4:
            raise MeasurementError(
                "campaign CPU-guard slot does not contain four physical cores"
            )
        core_lists: list[str] = []
        core_union: set[int] = set()
        for core in cores:
            logical = core.get("logical_cpus") if isinstance(core, Mapping) else None
            if (
                not isinstance(logical, list)
                or not logical
                or any(
                    isinstance(cpu, bool) or not isinstance(cpu, int)
                    for cpu in logical
                )
                or len(logical) != len(set(logical))
                or core_union.intersection(logical)
            ):
                raise MeasurementError(
                    "campaign CPU-guard physical-core CPU list is malformed"
                )
            core_union.update(logical)
            core_lists.append(resources.format_cpu_list(logical))
        if core_union != set(cpus):
            raise MeasurementError(
                "campaign CPU-guard physical cores do not form their slot"
            )
        expected_slot_core_lists.append(
            sorted(
                core_lists,
                key=lambda raw: min(resources.parse_cpu_list(raw)),
            )
        )
    expected_reserved_list = resources.format_cpu_list(expected_reserved_cpus)

    execution_descriptor = campaign.get("execution")
    if not isinstance(execution_descriptor, Mapping):
        raise MeasurementError("campaign lacks its locked execution manifest")
    execution_path = _resolve_artifact(
        results_root,
        execution_descriptor,
        "campaign execution manifest",
    )
    execution_manifest = read_object(
        execution_path, kind="highambench-file-manifest"
    )
    execution_files = execution_manifest.get("files")
    if not isinstance(execution_files, list):
        raise MeasurementError("campaign execution manifest has no file inventory")
    expected_guard_sources: dict[str, dict[str, Any]] = {}
    for role, source_relative in (
        ("frontend", CPU_GUARD_FRONTEND_SOURCE_RELATIVE),
        ("host_helper", CPU_GUARD_SOURCE_RELATIVE),
    ):
        source_records = [
            item
            for item in execution_files
            if isinstance(item, Mapping)
            and item.get("path") == source_relative.as_posix()
        ]
        if len(source_records) != 1:
            raise MeasurementError(
                f"campaign execution manifest does not bind one CPU-guard {role} source"
            )
        expected_source = dict(source_records[0])
        if (
            set(expected_source) != {"path", "bytes", "sha256"}
            or isinstance(expected_source.get("bytes"), bool)
            or not isinstance(expected_source.get("bytes"), int)
            or expected_source["bytes"] < 1
            or not isinstance(expected_source.get("sha256"), str)
            or re.fullmatch(r"[0-9a-f]{64}", expected_source["sha256"])
            is None
        ):
            raise MeasurementError(
                f"campaign CPU-guard {role} source identity is malformed"
            )
        expected_guard_sources[role] = expected_source

    def verify_guard_control(
        value: object,
        *,
        action: str,
        lease_id: str,
    ) -> None:
        if not isinstance(value, Mapping):
            raise MeasurementError(f"CPU-guard {action} record is missing")
        evidence_descriptor = value.get("evidence")
        log_descriptor = value.get("log")
        command = value.get("command")
        if not isinstance(evidence_descriptor, Mapping) or not isinstance(
            log_descriptor, Mapping
        ):
            raise MeasurementError(f"CPU-guard {action} artifacts are missing")
        evidence_path = _resolve_artifact(
            results_root,
            evidence_descriptor,
            f"CPU-guard {action} evidence",
        )
        log_path = _resolve_artifact(
            results_root,
            log_descriptor,
            f"CPU-guard {action} log",
        )
        expected_root = (results_root / "cpu_guard_leases" / lease_id).resolve()
        if (
            evidence_path != expected_root / f"{action}.json"
            or log_path != expected_root / f"{action}.log"
        ):
            raise MeasurementError(f"CPU-guard {action} artifacts use another lease")
        evidence = read_object(evidence_path)
        expected_kind = f"highambench-cpu-guard-{action}"
        if (
            evidence.get("schema_version") != 1
            or evidence.get("kind") != expected_kind
            or evidence.get("verified") is not True
            or evidence.get("lease_id") != lease_id
            or (action == "acquire" and evidence.get("slots") != expected_slot_lists)
            or (
                action == "acquire"
                and evidence.get("reserved_cpus") != expected_reserved_list
            )
            or (action == "release" and evidence.get("released") is not True)
        ):
            raise MeasurementError(f"CPU-guard {action} evidence is invalid")
        if action == "acquire":
            _validate_cpu_guard_acquire_evidence(
                evidence,
                lease_id=lease_id,
                expected_slots=expected_slot_lists,
            )
            details = evidence["slot_details"]
            if any(
                detail.get("physical_cores") != expected_cores
                for detail, expected_cores in zip(
                    details, expected_slot_core_lists, strict=True
                )
            ):
                raise MeasurementError(
                    "CPU-guard acquire physical-core evidence changed"
                )
        else:
            _validate_cpu_guard_release_evidence(
                evidence,
                lease_id=lease_id,
                expected_slots=expected_slot_lists,
                allowed_recovery_phases={"active"},
                allow_already_inactive=False,
            )
        expected_command = (
            _cpu_guard_acquire_command(lease_id, evidence_path, expected_slots)
            if action == "acquire"
            else _cpu_guard_release_command(lease_id, evidence_path)
        )
        if command != expected_command:
            raise MeasurementError(f"CPU-guard {action} command changed")

    def verify_pre_acquire(
        value: object, executable: Mapping[str, Any]
    ) -> None:
        if (
            not isinstance(value, Mapping)
            or set(value) != {"schema_version", "kind", "outcome", "record"}
            or value.get("schema_version") != 1
            or value.get("kind") != CPU_GUARD_RECOVERY_KIND
            or value.get("outcome")
            not in {"guard-inactive", "released-owned-stale-lease"}
            or not isinstance(value.get("record"), Mapping)
        ):
            raise MeasurementError("CPU-guard pre-acquire recovery record is invalid")
        record_descriptor = value["record"]
        record_path = _resolve_artifact(
            results_root,
            record_descriptor,
            "CPU-guard pre-acquire recovery result",
        )
        recovery_root = (results_root / "cpu_guard_recoveries").resolve()
        attempt_root = record_path.parent
        campaign_id = campaign.get("campaign_id")
        if (
            record_path != attempt_root / "result.json"
            or attempt_root.parent != recovery_root
            or not isinstance(campaign_id, str)
            or re.fullmatch(
                rf"{re.escape(campaign_id)}-[0-9a-f]{{16}}",
                attempt_root.name,
            )
            is None
            or record_descriptor.get("mode") != "0o600"
            or stat.S_IMODE(record_path.stat().st_mode) != 0o600
            or record_path.stat().st_uid != os.getuid()
            or record_path.stat().st_nlink != 1
        ):
            raise MeasurementError(
                "CPU-guard pre-acquire result uses another recovery attempt"
            )
        for directory in (recovery_root, attempt_root):
            directory_status = directory.lstat()
            if (
                stat.S_ISLNK(directory_status.st_mode)
                or not stat.S_ISDIR(directory_status.st_mode)
                or directory_status.st_uid != os.getuid()
                or stat.S_IMODE(directory_status.st_mode) != 0o700
            ):
                raise MeasurementError(
                    "CPU-guard recovery directories are not private and user-owned"
                )
        record = read_object(record_path, kind=CPU_GUARD_RECOVERY_KIND)
        _verify_self_hash(record, "CPU-guard pre-acquire recovery result")
        base_keys = {
            "schema_version",
            "kind",
            "campaign_id",
            "campaign_lock_sha256",
            "recorded_at_utc",
            "expected_slots",
            "expected_reserved_cpus",
            "request",
            "request_record_sha256",
            "status",
            "outcome",
            "record_sha256",
        }
        outcome = record.get("outcome")
        expected_keys = (
            base_keys
            if outcome == "guard-inactive"
            else base_keys | {"stale_lease", "release"}
        )
        if (
            set(record) != expected_keys
            or record.get("schema_version") != 1
            or record.get("campaign_id") != campaign_id
            or record.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
            or not isinstance(record.get("recorded_at_utc"), str)
            or record.get("expected_slots") != expected_slot_lists
            or record.get("expected_reserved_cpus") != expected_reserved_list
            or outcome != value.get("outcome")
            or not isinstance(record.get("request"), Mapping)
            or not isinstance(record.get("status"), Mapping)
        ):
            raise MeasurementError(
                "CPU-guard pre-acquire recovery identity is invalid"
            )

        def private_artifact(
            descriptor: object, expected_path: Path, label: str
        ) -> Path:
            if not isinstance(descriptor, Mapping):
                raise MeasurementError(f"{label} descriptor is missing")
            path = _resolve_artifact(results_root, descriptor, label)
            status = path.stat()
            if (
                path != expected_path
                or descriptor.get("mode") != "0o600"
                or status.st_uid != os.getuid()
                or status.st_nlink != 1
                or stat.S_IMODE(status.st_mode) != 0o600
            ):
                raise MeasurementError(
                    f"{label} is not a private recovery artifact"
                )
            return path

        request_path = private_artifact(
            record["request"],
            attempt_root / "request.json",
            "CPU-guard recovery request",
        )
        request = read_object(
            request_path, kind=CPU_GUARD_RECOVERY_REQUEST_KIND
        )
        _verify_self_hash(request, "CPU-guard recovery request")
        if (
            set(request)
            != {
                "schema_version",
                "kind",
                "campaign_id",
                "campaign_lock_sha256",
                "created_at_utc",
                "expected_slots",
                "expected_reserved_cpus",
                "record_sha256",
            }
            or request.get("schema_version") != 1
            or request.get("campaign_id") != campaign_id
            or request.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
            or not isinstance(request.get("created_at_utc"), str)
            or request.get("expected_slots") != expected_slot_lists
            or request.get("expected_reserved_cpus") != expected_reserved_list
            or record.get("request_record_sha256")
            != request.get("record_sha256")
        ):
            raise MeasurementError("CPU-guard recovery request is invalid")

        status_control = record["status"]
        if (
            set(status_control) != {"command", "evidence", "log"}
            or status_control.get("command") != _cpu_guard_status_command()
        ):
            raise MeasurementError("CPU-guard status command changed")
        status_path = private_artifact(
            status_control.get("evidence"),
            attempt_root / "status.json",
            "CPU-guard status evidence",
        )
        private_artifact(
            status_control.get("log"),
            attempt_root / "status.log",
            "CPU-guard status log",
        )
        status_evidence = read_object(status_path, kind=CPU_GUARD_STATUS_KIND)
        generation = status_evidence.get("generation")
        phase = status_evidence.get("phase")
        recovery_required = status_evidence.get("recovery_required")
        active = status_evidence.get("active_lease")
        applied = status_evidence.get("applied")
        if (
            set(status_evidence)
            != {
                "schema_version",
                "kind",
                "verified",
                "generation",
                "phase",
                "recovery_required",
                "active_lease",
                "applied",
                "idle_sample_seconds",
                "maximum_busy_percent",
                "allowed_cpus",
                "maximum_slots",
            }
            or status_evidence.get("schema_version") != 1
            or status_evidence.get("verified") is not True
            or isinstance(generation, bool)
            or not isinstance(generation, int)
            or generation < 0
            or phase not in {"inactive", "preparing", "active", "releasing"}
            or not isinstance(recovery_required, bool)
            or recovery_required != (phase in {"preparing", "releasing"})
            or status_evidence.get("idle_sample_seconds")
            != CPU_GUARD_IDLE_SAMPLE_SECONDS
            or status_evidence.get("maximum_busy_percent")
            != CPU_GUARD_MAXIMUM_BUSY_PERCENT
        ):
            raise MeasurementError("CPU-guard status evidence is invalid")
        allowed_raw = status_evidence.get("allowed_cpus")
        maximum_slots = status_evidence.get("maximum_slots")
        try:
            allowed = (
                frozenset(resources.parse_cpu_list(allowed_raw))
                if isinstance(allowed_raw, str)
                else frozenset()
            )
        except resources.ResourceIsolationError as error:
            raise MeasurementError(
                f"CPU-guard status allowed CPU list is invalid: {error}"
            ) from error
        if (
            not allowed
            or resources.format_cpu_list(allowed) != allowed_raw
            or isinstance(maximum_slots, bool)
            or not isinstance(maximum_slots, int)
            or len(expected_slot_lists) > maximum_slots
            or not expected_reserved_cpus <= allowed
        ):
            raise MeasurementError(
                "CPU-guard status cannot admit the campaign CPU slots"
            )
        if outcome == "guard-inactive":
            if phase != "inactive" or active is not None or applied is not None:
                raise MeasurementError(
                    "CPU-guard inactive recovery observed an active lease"
                )
            return

        if (
            phase == "inactive"
            or not isinstance(active, Mapping)
            or not isinstance(applied, Mapping)
        ):
            raise MeasurementError("CPU-guard stale lease status is missing")
        lease_id = active.get("lease_id")
        if (
            not isinstance(lease_id, str)
            or re.fullmatch(
                rf"{re.escape(str(campaign_id))}-[0-9a-f]{{16}}", lease_id
            )
            is None
            or active.get("slots") != expected_slot_lists
            or active.get("reserved_cpus") != expected_reserved_list
            or applied.get("reserved_cpus") != expected_reserved_list
        ):
            raise MeasurementError(
                "CPU-guard stale lease status is not owned by this campaign"
            )
        stale = record.get("stale_lease")
        if (
            not isinstance(stale, Mapping)
            or set(stale)
            not in (
                {"lease_id", "intent", "acquire_log"},
                {"lease_id", "acquire_evidence", "acquire_log"},
                {
                    "lease_id",
                    "intent",
                    "acquire_evidence",
                    "acquire_log",
                },
            )
            or stale.get("lease_id") != lease_id
        ):
            raise MeasurementError("CPU-guard stale lease ownership proof is invalid")
        lease_root = (results_root / "cpu_guard_leases" / lease_id).resolve()
        private_artifact(
            stale.get("acquire_log"),
            lease_root / "acquire.log",
            "stale CPU-guard acquire log",
        )
        if "intent" in stale:
            intent_path = private_artifact(
                stale.get("intent"),
                lease_root / "intent.json",
                "stale CPU-guard acquire intent",
            )
            intent = read_object(intent_path, kind=CPU_GUARD_ACQUIRE_INTENT_KIND)
            _verify_self_hash(intent, "stale CPU-guard acquire intent")
            if (
                set(intent)
                != {
                    "schema_version",
                    "kind",
                    "campaign_id",
                    "campaign_lock_sha256",
                    "lease_id",
                    "created_at_utc",
                    "slots",
                    "reserved_cpus",
                    "cpu_guard_executable",
                    "record_sha256",
                }
                or intent.get("schema_version") != 1
                or intent.get("campaign_id") != campaign_id
                or intent.get("campaign_lock_sha256")
                != campaign.get("record_sha256")
                or intent.get("lease_id") != lease_id
                or not isinstance(intent.get("created_at_utc"), str)
                or intent.get("slots") != expected_slot_lists
                or intent.get("reserved_cpus") != expected_reserved_list
                or intent.get("cpu_guard_executable") != dict(executable)
            ):
                raise MeasurementError("stale CPU-guard acquire intent is invalid")
        if "acquire_evidence" in stale:
            acquire_path = private_artifact(
                stale.get("acquire_evidence"),
                lease_root / "acquire.json",
                "stale CPU-guard acquire evidence",
            )
            acquire = read_object(acquire_path)
            _validate_cpu_guard_acquire_evidence(
                acquire,
                lease_id=lease_id,
                expected_slots=expected_slot_lists,
            )
            details = acquire["slot_details"]
            if any(
                detail.get("physical_cores") != expected_cores
                for detail, expected_cores in zip(
                    details, expected_slot_core_lists, strict=True
                )
            ):
                raise MeasurementError(
                    "stale CPU-guard acquire physical-core evidence changed"
                )

        release = record.get("release")
        if not isinstance(release, Mapping) or set(release) != {
            "command",
            "evidence",
            "log",
        }:
            raise MeasurementError("CPU-guard stale release record is missing")
        release_path = private_artifact(
            release.get("evidence"),
            attempt_root / "release.json",
            "CPU-guard stale release evidence",
        )
        private_artifact(
            release.get("log"),
            attempt_root / "release.log",
            "CPU-guard stale release log",
        )
        release_evidence = read_object(release_path)
        if release.get("command") != _cpu_guard_release_command(
            lease_id, release_path
        ):
            raise MeasurementError("CPU-guard stale release evidence is invalid")
        _validate_cpu_guard_release_evidence(
            release_evidence,
            lease_id=lease_id,
            expected_slots=expected_slot_lists,
            allowed_recovery_phases={str(phase)},
            allow_already_inactive=False,
        )

    def verify_guard_lease(value: object, lease_id: str) -> None:
        if not isinstance(value, Mapping):
            raise MeasurementError("campaign lacks CPU-guard acquisition evidence")
        executable = value.get("executable")
        if (
            not isinstance(executable, Mapping)
            or set(executable) != {"frontend", "host_helper"}
        ):
            raise MeasurementError("campaign CPU-guard executable identity is missing")
        if (
            value.get("lease_id") != lease_id
            or value.get("slots") != expected_slot_lists
        ):
            raise MeasurementError("campaign CPU-guard lease identity is invalid")
        for role, installed_path in (
            ("frontend", CPU_GUARD_PATH),
            ("host_helper", CPU_GUARD_HOST_PATH),
        ):
            component = executable.get(role)
            expected_source = expected_guard_sources[role]
            if not isinstance(component, Mapping):
                raise MeasurementError(
                    f"campaign CPU-guard {role} identity is missing"
                )
            mode_raw = component.get("mode")
            try:
                mode = int(mode_raw, 8) if isinstance(mode_raw, str) else -1
            except ValueError:
                mode = -1
            digest = component.get("sha256")
            tracked_source = component.get("tracked_source")
            if (
                set(component)
                != {
                    "path",
                    "device",
                    "inode",
                    "owner_uid",
                    "owner_gid",
                    "hard_links",
                    "mode",
                    "sha256",
                    "tracked_source",
                }
                or component.get("path") != str(installed_path)
                or component.get("owner_uid") != 0
                or component.get("owner_gid") != 0
                or component.get("hard_links") != 1
                or isinstance(component.get("device"), bool)
                or not isinstance(component.get("device"), int)
                or isinstance(component.get("inode"), bool)
                or not isinstance(component.get("inode"), int)
                or component["device"] < 0
                or component["inode"] <= 0
                or mode != 0o755
                or not isinstance(digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", digest) is None
                or not isinstance(tracked_source, Mapping)
                or dict(tracked_source) != expected_source
                or digest != expected_source["sha256"]
            ):
                raise MeasurementError(
                    f"campaign CPU-guard {role} identity is invalid"
                )
        intent_descriptor = value.get("intent")
        if not isinstance(intent_descriptor, Mapping):
            raise MeasurementError("campaign CPU-guard acquire intent is missing")
        intent_path = _resolve_artifact(
            results_root,
            intent_descriptor,
            "campaign CPU-guard acquire intent",
        )
        expected_intent_path = (
            results_root / "cpu_guard_leases" / lease_id / "intent.json"
        ).resolve()
        intent_status = intent_path.stat()
        if (
            intent_path != expected_intent_path
            or intent_descriptor.get("mode") != "0o600"
            or intent_status.st_uid != os.getuid()
            or intent_status.st_nlink != 1
            or stat.S_IMODE(intent_status.st_mode) != 0o600
        ):
            raise MeasurementError(
                "campaign CPU-guard acquire intent uses another lease"
            )
        intent = read_object(intent_path, kind=CPU_GUARD_ACQUIRE_INTENT_KIND)
        _verify_self_hash(intent, "campaign CPU-guard acquire intent")
        if (
            set(intent)
            != {
                "schema_version",
                "kind",
                "campaign_id",
                "campaign_lock_sha256",
                "lease_id",
                "created_at_utc",
                "slots",
                "reserved_cpus",
                "cpu_guard_executable",
                "record_sha256",
            }
            or intent.get("schema_version") != 1
            or intent.get("campaign_id") != campaign.get("campaign_id")
            or intent.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
            or intent.get("lease_id") != lease_id
            or not isinstance(intent.get("created_at_utc"), str)
            or intent.get("slots") != expected_slot_lists
            or intent.get("reserved_cpus") != expected_reserved_list
            or intent.get("cpu_guard_executable") != dict(executable)
        ):
            raise MeasurementError("campaign CPU-guard acquire intent is invalid")
        verify_pre_acquire(value.get("pre_acquire"), executable)
        verify_guard_control(value.get("acquire"), action="acquire", lease_id=lease_id)

    expected_input = dict(input_verification)
    expected_input.pop("verified_at_utc", None)

    def verify_input(value: object, label: str) -> None:
        if not isinstance(value, Mapping):
            raise MeasurementError(f"{label} lacks input verification")
        observed = dict(value)
        observed.pop("verified_at_utc", None)
        if (
            value.get("deep_runtime_integrity_checked") is not True
            or observed != expected_input
        ):
            raise MeasurementError(f"{label} input verification is invalid")

    def verify_common(event: Mapping[str, Any]) -> None:
        _verify_self_hash(event, "campaign event")
        if (
            event.get("schema_version") != 1
            or event.get("kind") not in allowed_kinds
            or event.get("campaign_id") != campaign.get("campaign_id")
            or event.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
            or not isinstance(event.get("recorded_at_utc"), str)
        ):
            raise MeasurementError("campaign event has an invalid identity/schema")

    for event in events:
        verify_common(event)
    preflights = [event for event in events if event.get("kind") == "campaign-preflight"]
    core_locks = [
        event for event in events if event.get("kind") == "host-core-locks-acquired"
    ]
    campaign_terminals = [
        event for event in events if event.get("kind") == "campaign-terminal"
    ]
    recovery_terminals = [
        event
        for event in events
        if event.get("kind") == "campaign-recovery-terminal"
    ]
    invocation_terminals = [*campaign_terminals, *recovery_terminals]
    if not preflights or len(preflights) != len(core_locks) or len(preflights) != len(
        invocation_terminals
    ):
        raise MeasurementError(
            "campaign events lack matched preflight/core-lock/terminal evidence"
        )

    active: dict[str, Any] | None = None
    recovered_pair_events: list[Mapping[str, Any]] = []
    recovered_failed_pair_events: list[Mapping[str, Any]] = []
    recovery_bound_pair_event_hashes: set[str] = set()
    for event in events:
        kind = event["kind"]
        if kind == "campaign-preflight":
            if active is not None:
                raise MeasurementError("campaign event invocations overlap")
            verify_input(event.get("input_verification"), "campaign preflight")
            if (
                event.get("resource_slots") != expected_slots
                or event.get("hardware_identity")
                != campaign.get("hardware_identity")
            ):
                raise MeasurementError("campaign preflight resource identity changed")
            lease_id = event.get("cpu_guard_lease_id")
            if (
                not isinstance(lease_id, str)
                or _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None
            ):
                raise MeasurementError("campaign preflight CPU-guard lease is invalid")
            active = {
                "phase": "preflight",
                "preflight_record_sha256": event["record_sha256"],
                "core_locks_record_sha256": None,
                "pair_events": [],
                "cpu_guard_lease_id": lease_id,
            }
        elif kind == "host-core-locks-acquired":
            if active is None or active["phase"] != "preflight":
                raise MeasurementError("campaign core locks are out of order")
            recovery_context = event.get("recovery_lock_context")
            if recovery_context is not None:
                if recovery_context != {
                    "reacquired_for_interrupted_preflight": True,
                    "preflight_record_sha256": active[
                        "preflight_record_sha256"
                    ],
                }:
                    raise MeasurementError(
                        "campaign recovery core-lock context is invalid"
                    )
                verify_input(
                    event.get("input_verification"),
                    "campaign recovery core locks",
                )
            if (
                event.get("resource_slots") != expected_slots
                or event.get("hardware_identity")
                != campaign.get("hardware_identity")
            ):
                raise MeasurementError("campaign core-lock resource identity changed")
            locks = event.get("locks")
            if not isinstance(locks, list) or len(locks) != len(expected_cores):
                raise MeasurementError("campaign core-lock evidence has the wrong size")
            observed_cores: list[tuple[int, int, int]] = []
            lock_parent: Path | None = None
            for lock_record in locks:
                physical = (
                    lock_record.get("physical_core")
                    if isinstance(lock_record, Mapping)
                    else None
                )
                if not isinstance(physical, Mapping):
                    raise MeasurementError("campaign core-lock evidence is malformed")
                identity = core_identity(physical, "campaign core-lock identity")
                path_raw = lock_record.get("path")
                path = Path(path_raw) if isinstance(path_raw, str) else Path()
                expected_name = f"core-{identity[0]}-{identity[1]}-{identity[2]}.lock"
                if (
                    lock_record.get("acquired") is not True
                    or lock_record.get("label")
                    != f"physical core ({identity[0]}, {identity[1]}, {identity[2]})"
                    or lock_record.get("owner_uid") != os.getuid()
                    or not isinstance(lock_record.get("device"), int)
                    or not isinstance(lock_record.get("inode"), int)
                    or lock_record["device"] < 0
                    or lock_record["inode"] <= 0
                    or not path.is_absolute()
                    or ".." in path.parts
                    or path.name != expected_name
                ):
                    raise MeasurementError("campaign core-lock evidence is invalid")
                if lock_parent is None:
                    lock_parent = path.parent
                elif path.parent != lock_parent:
                    raise MeasurementError("campaign core locks use different namespaces")
                observed_cores.append(identity)
            if observed_cores != sorted(expected_cores):
                raise MeasurementError("campaign core locks differ from locked slots")
            if (
                lock_parent is None
                or lock_parent.name
                != f"highambench-resource-locks-{os.getuid()}"
            ):
                raise MeasurementError("campaign core-lock namespace is invalid")
            if recovery_context is None:
                verify_guard_lease(
                    event.get("cpu_guard_lease"),
                    str(active["cpu_guard_lease_id"]),
                )
            active["phase"] = "locked"
            active["core_locks_record_sha256"] = event["record_sha256"]
            active["core_locks_reacquired_for_recovery"] = (
                recovery_context is not None
            )
        elif kind == "pair-terminal":
            if active is None or active["phase"] != "locked":
                raise MeasurementError("pair terminal event is outside a locked invocation")
            if active.get("core_locks_reacquired_for_recovery") is True:
                raise MeasurementError(
                    "pair terminal follows a synthetic recovery lock event"
                )
            if event.get("cpu_guard_lease_id") != active["cpu_guard_lease_id"]:
                raise MeasurementError("pair terminal uses another CPU-guard lease")
            pair_id = event.get("pair_id")
            if not isinstance(pair_id, str):
                raise MeasurementError("pair terminal event has no pair id")
            if event.get("complete") is False:
                failed = _failed_pair_terminal_result(
                    results_root / "pairs" / pair_id,
                    expected_pair(pair_id),
                    campaign,
                    relative_to=results_root,
                )
                if any(event.get(key) != value for key, value in failed.items()):
                    raise MeasurementError(
                        f"failed pair terminal event is inconsistent: {pair_id}"
                    )
            active["pair_events"].append(event)
        elif kind == "campaign-terminal":
            if active is None or active["phase"] != "locked":
                raise MeasurementError("campaign terminal event is out of order")
            if active.get("core_locks_reacquired_for_recovery") is True:
                raise MeasurementError(
                    "normal campaign terminal follows a synthetic recovery lock event"
                )
            verify_input(event.get("input_verification"), "campaign terminal")
            selected = event.get("selected_pair_ids")
            results = event.get("pair_results")
            returncode = event.get("returncode")
            if (
                event.get("hardware_identity")
                != campaign.get("hardware_identity")
                or event.get("cpu_guard_lease_id")
                != active["cpu_guard_lease_id"]
                or not isinstance(selected, list)
                or not all(isinstance(pair_id, str) for pair_id in selected)
                or len(selected) != len(set(selected))
                or not isinstance(results, list)
                or returncode not in (0, 1, 2)
                or not all(isinstance(result, Mapping) for result in results)
                or not all(
                    isinstance(result.get("pair_id"), str) for result in results
                )
            ):
                raise MeasurementError("campaign terminal evidence is invalid")
            result_by_pair = {result.get("pair_id"): dict(result) for result in results}
            event_by_pair = {
                pair_event.get("pair_id"): {
                    key: pair_event.get(key)
                    for key in (
                        "pair_id",
                        "returncode",
                        "complete",
                        "cpu_guard_lease_id",
                        "cpu_guard_lease_ids",
                        "terminal",
                    )
                    if key in pair_event
                }
                for pair_event in active["pair_events"]
            }
            if (
                len(result_by_pair) != len(results)
                or len(event_by_pair) != len(active["pair_events"])
                or set(result_by_pair) != set(event_by_pair)
                or any(
                    result_by_pair[pair_id] != event_by_pair[pair_id]
                    for pair_id in result_by_pair
                )
                or not set(result_by_pair) <= set(selected)
                or (
                    returncode in (0, 1)
                    and set(result_by_pair) != set(selected)
                )
                or (
                    returncode == 0
                    and (
                        any(
                            result.get("returncode") != 0
                            or result.get("complete") is not True
                            for result in results
                        )
                    )
                )
                or (
                    returncode == 1
                    and not any(
                        result.get("returncode") != 0
                        or result.get("complete") is not True
                        for result in results
                    )
                )
                or (
                    returncode == 2
                    and (
                        not isinstance(event.get("error"), Mapping)
                        or not isinstance(event["error"].get("type"), str)
                        or not isinstance(event["error"].get("message"), str)
                    )
                )
                or (returncode in (0, 1) and event.get("error") is not None)
            ):
                raise MeasurementError("campaign terminal pair evidence is inconsistent")
            release_record = event.get("cpu_guard_release")
            if release_record is not None:
                verify_guard_control(
                    release_record,
                    action="release",
                    lease_id=str(active["cpu_guard_lease_id"]),
                )
            elif not (
                returncode == 2
                and isinstance(event.get("error"), Mapping)
            ):
                raise MeasurementError("campaign terminal lacks CPU-guard release")
            active = None
        else:
            if active is None or active["phase"] != "locked":
                raise MeasurementError("campaign recovery terminal is out of order")
            verify_input(event.get("input_verification"), "campaign recovery")
            recovered_invocation = event.get("recovered_invocation")
            recovered_results = event.get("recovered_pair_results")
            active_pair_ids = [
                pair_event.get("pair_id") for pair_event in active["pair_events"]
            ]
            recovered_pair_ids = [
                result.get("pair_id")
                for result in recovered_results
                if isinstance(result, Mapping)
            ] if isinstance(recovered_results, list) else []
            has_durable_commit = bool(active["pair_events"] or recovered_pair_ids)
            expected_reason = (
                "coordinator-exited-after-durable-pair-commit"
                if has_durable_commit
                else "coordinator-exited-before-campaign-terminal"
            )
            if (
                event.get("reason") != expected_reason
                or event.get("hardware_identity")
                != campaign.get("hardware_identity")
                or not isinstance(recovered_invocation, Mapping)
                or recovered_invocation
                != {
                    "preflight_record_sha256": active[
                        "preflight_record_sha256"
                    ],
                    "core_locks_record_sha256": active[
                        "core_locks_record_sha256"
                    ],
                    "pair_terminal_record_sha256s": [
                        pair_event.get("record_sha256")
                        for pair_event in active["pair_events"]
                    ],
                }
                or not isinstance(recovered_results, list)
                or len(recovered_pair_ids) != len(recovered_results)
                or len(recovered_pair_ids) != len(set(recovered_pair_ids))
                or set(recovered_pair_ids) & set(active_pair_ids)
                or any(
                    isinstance(result.get("returncode"), bool)
                    or not isinstance(result.get("returncode"), int)
                    or result.get("complete") not in (True, False)
                    or (
                        result.get("complete") is True
                        and result.get("returncode") != 0
                    )
                    or not isinstance(result.get("terminal"), Mapping)
                    for result in recovered_results
                    if isinstance(result, Mapping)
                )
            ):
                raise MeasurementError("campaign recovery evidence is invalid")
            recovery_bound_pair_event_hashes.update(
                str(pair_event["record_sha256"])
                for pair_event in active["pair_events"]
                if pair_event.get("complete") is True
            )
            for result in recovered_results:
                if result.get("complete") is True:
                    recovered_pair_events.append(result)
                    continue
                pair_id = str(result.get("pair_id"))
                failed = _failed_pair_terminal_result(
                    results_root / "pairs" / pair_id,
                    expected_pair(pair_id),
                    campaign,
                    relative_to=results_root,
                )
                if dict(result) != failed:
                    raise MeasurementError(
                        f"recovered failed pair result is inconsistent: {pair_id}"
                    )
                recovered_failed_pair_events.append(result)
            active = None
    if active is not None:
        raise MeasurementError("campaign event log ends during an active invocation")

    terminal_events = [event for event in events if event.get("kind") == "pair-terminal"]
    by_pair: dict[str, list[Mapping[str, Any]]] = {}
    for event in terminal_events:
        pair_id = event.get("pair_id")
        if not isinstance(pair_id, str):
            raise MeasurementError("pair-terminal event has no pair id")
        by_pair.setdefault(pair_id, []).append(event)
    for event in recovered_pair_events:
        pair_id = event.get("pair_id")
        if not isinstance(pair_id, str):
            raise MeasurementError("recovered pair terminal has no pair id")
        by_pair.setdefault(pair_id, []).append(event)
    verified_ids = {str(pair["pair_id"]) for pair in verified_pairs}
    recovered_ids = {
        str(event["pair_id"])
        for event in recovered_pair_events
        if isinstance(event.get("pair_id"), str)
    }
    recovery_bound_ids = {
        str(event["pair_id"])
        for event in terminal_events
        if event.get("record_sha256") in recovery_bound_pair_event_hashes
        and isinstance(event.get("pair_id"), str)
    }
    if not (recovered_ids | recovery_bound_ids) <= verified_ids:
        raise MeasurementError("campaign recovery names an unverified pair terminal")
    for pair in verified_pairs:
        pair_id = str(pair["pair_id"])
        matches = by_pair.get(pair_id, [])
        # Every durable pair commit must be represented exactly once.  Normal
        # executions use pair-terminal; a coordinator crash is represented by
        # the subsequent append-only campaign-recovery-terminal closure.
        if len(matches) != 1:
            raise MeasurementError(
                f"pair {pair_id} lacks exactly one authenticated terminal event"
            )
        event = matches[0]
        descriptor = event.get("terminal")
        if (
            event.get("returncode") != 0
            or event.get("complete") is not True
            or not isinstance(descriptor, Mapping)
        ):
            raise MeasurementError(f"pair {pair_id} terminal campaign event is invalid")
        terminal = _resolve_artifact(
            results_root, descriptor, f"pair {pair_id} event terminal"
        )
        expected_terminal = (
            results_root / "pairs" / pair_id / "outer_terminal.json"
        ).resolve()
        if terminal != expected_terminal:
            raise MeasurementError(f"pair {pair_id} event points to another terminal")
        terminal_value = read_object(
            terminal, kind="highambench-pair-outer-terminal"
        )
        _verify_self_hash(terminal_value, f"pair {pair_id} outer terminal")
        if (
            terminal_value.get("schema_version") not in (1, 2)
            or terminal_value.get("pair_id") != pair_id
            or terminal_value.get("returncode") != 0
            or terminal_value.get("complete") is not True
            or terminal_value.get("campaign_id") != campaign.get("campaign_id")
            or terminal_value.get("campaign_lock_sha256")
            != campaign.get("record_sha256")
        ):
            raise MeasurementError(
                f"pair {pair_id} outer terminal identity/status is invalid"
            )
    return {
        "event_count": len(events),
        "pair_terminal_events": len(terminal_events),
        "recovered_pair_terminal_events": len(recovered_pair_events),
        "recovered_failed_pair_terminal_events": len(
            recovered_failed_pair_events
        ),
        "campaign_invocations": len(invocation_terminals),
        "recovered_campaign_invocations": len(recovery_terminals),
        "sha256": sha256_file(event_path),
    }


def _verify_pair_infrastructure_incidents(
    results_root: Path,
    pair: Mapping[str, Any],
    expected: Mapping[str, Any],
    campaign: Mapping[str, Any],
) -> int:
    pair_id = str(expected["pair_id"])
    parent = results_root / "infrastructure_incidents" / pair_id
    if parent.is_symlink() or (parent.exists() and not parent.is_dir()):
        raise MeasurementError(f"pair {pair_id} incident directory is invalid")
    records = sorted(parent.glob("attempt-*.json")) if parent.is_dir() else []
    descriptors = pair.get("infrastructure_incidents")
    if not isinstance(descriptors, list) or len(descriptors) != len(records):
        raise MeasurementError(f"pair {pair_id} infrastructure incident list is incomplete")
    for descriptor, expected_path in zip(descriptors, records, strict=True):
        if not isinstance(descriptor, Mapping):
            raise MeasurementError(f"pair {pair_id} has a malformed incident descriptor")
        path = _resolve_artifact(results_root, descriptor, "infrastructure incident")
        if path != expected_path:
            raise MeasurementError(f"pair {pair_id} incident path changed")
        record = read_object(path, kind="highambench-infrastructure-incident")
        _verify_self_hash(record, "infrastructure incident")
        archive = parent / path.stem
        if (
            record.get("schema_version") != 1
            or record.get("campaign_id") != campaign.get("campaign_id")
            or record.get("campaign_lock_sha256") != campaign.get("record_sha256")
            or record.get("pair_id") != pair_id
            or record.get("archive") != archive.relative_to(results_root).as_posix()
            or not isinstance(record.get("reason"), str)
            or not record["reason"]
            or archive.is_symlink()
            or not archive.is_dir()
            or record.get("archive_manifest")
            != manifest_for_tree(results_root, [archive])
        ):
            raise MeasurementError(f"pair {pair_id} infrastructure incident changed")
    if parent.is_dir() and len(list(parent.glob("attempt-*[0-9]"))) != len(records):
        raise MeasurementError(f"pair {pair_id} has an unsealed incident archive")
    return len(records)


def verify_pair(
    benchmark_root: Path,
    results_root: Path,
    expected: Mapping[str, Any],
    campaign: Mapping[str, Any],
    runtime: Mapping[str, Any],
) -> dict[str, Any] | None:
    pair_root = results_root / "pairs" / str(expected["pair_id"])
    path = pair_root / "pair.json"
    if not path.exists():
        return None
    pair = read_object(path, kind=PAIR_KIND)
    _verify_self_hash(pair, f"pair {expected['pair_id']}")
    if (
        pair.get("schema_version") != 4
        or pair.get("pair_id") != expected["pair_id"]
        or pair.get("task_id") != expected["task_id"]
        or pair.get("repetition_id") != expected["repetition_id"]
        or pair.get("condition_order") != expected.get("condition_order")
        or pair.get("condition_order_is_execution_constraint") is not True
        or pair.get("run_ids") != expected.get("run_ids")
        or pair.get("complete") is not True
        or pair.get("infrastructure_failure") is not False
        or pair.get("campaign_id") != campaign.get("campaign_id")
        or pair.get("campaign_lock_sha256") != campaign.get("record_sha256")
    ):
        raise MeasurementError(f"pair {expected['pair_id']} identity/status is invalid")
    incident_count = _verify_pair_infrastructure_incidents(
        results_root, pair, expected, campaign
    )
    resources_by_condition = _verify_resource(
        pair_root, pair, expected, campaign
    )
    slots_by_condition = {
        condition: value["_slot"]
        for condition, value in resources_by_condition.items()
    }
    outer = _verify_outer_terminal(
        benchmark_root,
        results_root,
        pair_root,
        path,
        expected,
        campaign,
        slots_by_condition,
    )
    attempts_raw = pair.get("attempts")
    if not isinstance(attempts_raw, list) or len(attempts_raw) != 2:
        raise MeasurementError(f"pair {expected['pair_id']} lacks two attempts")
    attempts: list[dict[str, Any]] = []
    for attempt in attempts_raw:
        if not isinstance(attempt, Mapping):
            raise MeasurementError(
                f"pair {expected['pair_id']} has a malformed attempt descriptor"
            )
        condition = attempt.get("condition")
        resource = resources_by_condition.get(str(condition))
        if resource is None:
            raise MeasurementError(
                f"pair {expected['pair_id']} lacks condition resource evidence"
            )
        resource_path = Path(str(resource["_record_path"]))
        resource_proof = resource["_proof"]
        condition_resource = resource["_condition_resources"].get(str(condition))
        if not isinstance(condition_resource, Mapping):
            raise MeasurementError(
                f"pair {expected['pair_id']} lacks condition cgroup evidence"
            )
        attempts.append(
            _verify_attempt(
                pair_root,
                expected,
                attempt,
                benchmark_root=benchmark_root,
                results_root=results_root,
                campaign=campaign,
                runtime=runtime,
                resource_path=resource_path,
                resource_proof=resource_proof,
                condition_resource=condition_resource,
            )
        )
    if [item["condition"] for item in attempts] != ["N", "L"]:
        raise MeasurementError(f"pair {expected['pair_id']} lacks N or L")
    resource_summary = {
        condition: {
            key: value
            for key, value in resource.items()
            if not key.startswith("_")
        }
        for condition, resource in resources_by_condition.items()
    }
    return {
        "pair_id": expected["pair_id"],
        "task_id": expected["task_id"],
        "repetition_id": expected["repetition_id"],
        "condition_order": list(expected["condition_order"]),
        "resources": resource_summary,
        "outer_launch": outer,
        "infrastructure_incident_count": incident_count,
        "attempts": attempts,
    }


def verify(args: argparse.Namespace) -> int:
    benchmark_root = args.benchmark_root.resolve()
    campaign = _load_campaign(args.results_root)
    results_root = Path(str(campaign["results_root"]))
    if campaign.get("kind") != CAMPAIGN_KIND:
        raise MeasurementError("invalid campaign kind")
    inputs = verify_campaign_inputs(
        benchmark_root, results_root, campaign, deep_runtime=True
    )
    runtime = _load_runtime_snapshot(
        _artifact_path(results_root, campaign["runtime_snapshot"]), deep=False
    )
    expected_pairs = _order_pairs(benchmark_root)
    selected_pair_ids = set(args.pair_id)
    known_pair_ids = {str(pair["pair_id"]) for pair in expected_pairs}
    if not selected_pair_ids <= known_pair_ids:
        raise MeasurementError("selected pair id is outside the frozen run order")
    verified: list[dict[str, Any]] = []
    missing: list[str] = []
    for expected in expected_pairs:
        if selected_pair_ids and expected["pair_id"] not in selected_pair_ids:
            continue
        result = verify_pair(
            benchmark_root, results_root, expected, campaign, runtime
        )
        if result is None:
            missing.append(str(expected["pair_id"]))
        else:
            verified.append(result)
    campaign_events = _verify_campaign_events(
        results_root,
        campaign,
        verified,
        inputs,
        expected_pairs=expected_pairs,
    )
    if args.require_complete and missing:
        raise MeasurementError(
            f"campaign is incomplete: {len(missing)} of {len(expected_pairs)} pairs missing"
        )
    attempts = [attempt for pair in verified for attempt in pair["attempts"]]
    provider_schedule = _verify_serial_provider_schedule(verified)
    host_context_hashes = sorted(
        {
            str(attempt.get("host_developer_context_sha256"))
            for attempt in attempts
            if isinstance(attempt.get("host_developer_context_sha256"), str)
        }
    )
    if attempts and len(host_context_hashes) != 1:
        raise MeasurementError(
            "model-visible host developer context changed within the campaign"
        )
    manifest = read_object(benchmark_root / "metadata" / "manifest.json")
    targets_by_id = {
        str(target["task_id"]): target
        for paper in manifest.get("papers", [])
        if isinstance(paper, Mapping)
        for target in paper.get("targets", [])
        if isinstance(target, Mapping) and isinstance(target.get("task_id"), str)
    }
    for attempt in attempts:
        if attempt.get("condition") != "L":
            continue
        target = targets_by_id.get(str(attempt.get("task_id")), {})
        raw_intended = target.get("candidate_library_dependencies_for_audit")
        intended = sorted(
            str(name)
            for name in raw_intended
            if isinstance(name, str)
        ) if isinstance(raw_intended, list) else []
        used = sorted(
            str(name)
            for name in attempt.get("numstability_declarations", [])
            if isinstance(name, str)
        )
        intended_set = set(intended)
        used_set = set(used)
        if attempt.get("category") in ("C2", "C3"):
            attempt["target_numstability_audit"] = {
                "intended_declarations": intended,
                "intended_declarations_used": sorted(intended_set & used_set),
                "intended_declarations_not_used": sorted(intended_set - used_set),
                "other_numstability_declarations_used": sorted(
                    used_set - intended_set
                ),
                "used_any_intended_declaration": bool(intended_set & used_set),
            }
    failures = Counter(
        str(attempt["failure_code"])
        for attempt in attempts
        if attempt["pass"] is not True
    )
    profile_ids = {
        resource["profile_id"]
        for pair in verified
        for resource in pair["resources"].values()
    }
    if len(profile_ids) > 1:
        raise MeasurementError("verified pairs used different physical-core profiles")
    result_tree = manifest_for_tree(results_root, [results_root])
    summary = {
        "schema_version": 1,
        "kind": "highambench-verification-summary",
        "verified_at_utc": utc_now(),
        "campaign_id": campaign.get("campaign_id"),
        "verification_scope": "selected-pairs" if selected_pair_ids else "all-pairs",
        "selected_pair_ids": sorted(selected_pair_ids) if selected_pair_ids else None,
        "campaign_complete": len(verified) == len(expected_pairs),
        "inputs": inputs,
        "complete": not missing,
        "verified_pairs": len(verified),
        "missing_pairs": missing,
        "verified_attempts": len(attempts),
        "passes": sum(attempt["pass"] is True for attempt in attempts),
        "failures": dict(sorted(failures.items())),
        "token_usage_complete_attempts": sum(
            attempt["token_usage_complete"] is True for attempt in attempts
        ),
        "condition_performance": _direct_performance_rows(attempts),
        "attempt_results": attempts,
        "hardware_profile_ids": sorted(profile_ids),
        "campaign_events": campaign_events,
        "provider_schedule": provider_schedule,
        "host_developer_context_sha256": (
            host_context_hashes[0] if host_context_hashes else None
        ),
        "result_tree_manifest_sha256": result_tree["manifest_sha256"],
        "result_tree_file_count": len(result_tree["files"]),
        "private_chain_of_thought_recorded": False,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if not args.require_complete or not missing else 1


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--pair-id", action="append", default=[])
    parser.add_argument("--require-complete", action="store_true")
    return parser


def main() -> int:
    try:
        return verify(make_parser().parse_args())
    except (MeasurementError, OSError, ValueError) as error:
        print(f"verify-results error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
