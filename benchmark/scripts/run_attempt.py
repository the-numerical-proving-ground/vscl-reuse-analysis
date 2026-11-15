#!/usr/bin/env python3
"""Run and fully record one no-token-cap VSCLReuse N or L attempt."""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
from typing import Any, Mapping, Sequence

try:
    from .common import (
        MeasurementError,
        append_jsonl,
        artifact,
        atomic_write_bytes,
        atomic_write_json,
        canonical_digest,
        read_object,
        relative_child,
        resolved_regular_file,
        sha256_file,
        utc_now,
    )
except ImportError:  # pragma: no cover - direct execution
    from common import (  # type: ignore
        MeasurementError,
        append_jsonl,
        artifact,
        atomic_write_bytes,
        atomic_write_json,
        canonical_digest,
        read_object,
        relative_child,
        resolved_regular_file,
        sha256_file,
        utc_now,
    )


ATTEMPT_KIND = "highambench-measured-attempt"
WALL_SECONDS = 7200.0
STARTUP_SECONDS = 120.0
VALIDATION_COMMAND_MAX_SECONDS = 1800.0
POLL_SECONDS = 0.25


def _hidden_validation_system_error(validation: Mapping[str, Any] | None) -> str | None:
    if not isinstance(validation, Mapping) or validation.get("failure_code") != "SYSTEM_ERROR":
        return None
    note = validation.get("note")
    return note if isinstance(note, str) and note else "hidden validation reported a system error"


def _validation_command_timeout(remaining_seconds: float) -> float:
    return max(0.1, min(VALIDATION_COMMAND_MAX_SECONDS, remaining_seconds / 3.0))


def _import_validator(benchmark_root: Path) -> tuple[Any, Any]:
    package_root = benchmark_root.parent
    package_root_string = str(package_root)
    if package_root_string not in sys.path:
        sys.path.insert(0, package_root_string)
    try:
        from benchmark.tools.validator import (  # type: ignore
            ValidationConfig,
            validate,
        )
    except ImportError as error:
        raise MeasurementError(f"cannot import the tracked validator: {error}") from error
    return ValidationConfig, validate


def _authenticated_runtime_snapshot(path: Path) -> dict[str, Any]:
    try:
        from .run_benchmark import _load_runtime_snapshot
    except ImportError:  # pragma: no cover - direct execution
        from run_benchmark import _load_runtime_snapshot  # type: ignore

    # Campaign creation and final verification hash the full immutable runtime.
    # Per-attempt authorization rechecks its exact Git/mode/path identity without
    # rehashing the large read-only toolchain and derived build 360 times.
    return _load_runtime_snapshot(path.resolve(), deep=False)


def _campaign_authorization(
    args: argparse.Namespace, benchmark_root: Path, attempt_root: Path
) -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    Path,
]:
    """Fail closed unless this is the campaign-owned, isolated pair worker."""

    try:
        from . import resources
        from .run_benchmark import (
            MANAGER_MEMORY_BYTES,
            MEMORY_BYTES,
            _artifact_path,
            _campaign_pair_root,
            _external_private_directory,
            _load_campaign,
            _order_pairs,
            _resource_contract_identity,
            verify_campaign_inputs,
        )
    except ImportError:  # pragma: no cover - direct execution
        import resources  # type: ignore
        from run_benchmark import (  # type: ignore
            MANAGER_MEMORY_BYTES,
            MEMORY_BYTES,
            _artifact_path,
            _campaign_pair_root,
            _external_private_directory,
            _load_campaign,
            _order_pairs,
            _resource_contract_identity,
            verify_campaign_inputs,
        )

    results_root = _external_private_directory(
        args.results_root, "campaign results root", create=False
    )
    lock = _load_campaign(results_root)
    if lock.get("record_sha256") != args.campaign_lock_sha256:
        raise MeasurementError("attempt campaign-lock authorization is invalid")
    verify_campaign_inputs(benchmark_root, results_root, lock)
    expected_runtime = _artifact_path(results_root, lock["runtime_snapshot"])
    if args.runtime_snapshot.resolve(strict=True) != expected_runtime:
        raise MeasurementError("attempt runtime is not the campaign snapshot")
    agent = lock.get("agent")
    auth = lock.get("auth")
    runtime_tools = lock.get("runtime_tools")
    if not all(isinstance(item, Mapping) for item in (agent, auth, runtime_tools)):
        raise MeasurementError("campaign lacks attempt executable identity")
    bubblewrap = runtime_tools.get("bubblewrap")
    code_mode_host = agent.get("code_mode_host")
    if not isinstance(bubblewrap, Mapping) or not isinstance(
        code_mode_host, Mapping
    ):
        raise MeasurementError(
            "campaign lacks bubblewrap or Codex code-mode host identity"
        )
    expected_paths = {
        "codex": Path(str(agent.get("path"))).resolve(strict=True),
        "code_mode_host": Path(str(code_mode_host.get("path"))).resolve(
            strict=True
        ),
        "auth": Path(str(auth.get("path"))).resolve(strict=True),
        "offline_shell": _artifact_path(results_root, lock["offline_shell"]),
        "bubblewrap": Path(str(bubblewrap.get("path"))).resolve(strict=True),
        "toolchain": Path(str(lock.get("toolchain_root"))).resolve(strict=True),
        "shared_olean": (
            Path(str(lock.get("shared_olean_root")))
            / str(args.task_id).split("-")[0]
        ).resolve(strict=True),
    }
    supplied_paths = {
        "codex": args.codex.resolve(strict=True),
        "code_mode_host": args.code_mode_host.resolve(strict=True),
        "auth": args.auth_file.resolve(strict=True),
        "offline_shell": args.offline_shell.resolve(strict=True),
        "bubblewrap": args.bwrap.resolve(strict=True),
        "toolchain": args.toolchain_root.resolve(strict=True),
        "shared_olean": args.shared_olean_root.resolve(strict=True),
    }
    if supplied_paths != expected_paths:
        raise MeasurementError("attempt executable/runtime paths differ from campaign")

    pairs = {pair["pair_id"]: pair for pair in _order_pairs(benchmark_root)}
    pair = pairs.get(args.pair_id)
    if pair is None or pair.get("task_id") != args.task_id:
        raise MeasurementError("attempt does not name a canonical campaign pair")
    order = pair["condition_order"]
    if args.condition not in order:
        raise MeasurementError("attempt condition is absent from its pair")
    expected_run_id = pair["run_ids"][order.index(args.condition)]
    if args.run_id != expected_run_id:
        raise MeasurementError("attempt run id is not canonical")
    pair_root = _campaign_pair_root(results_root, args.pair_id)
    expected_attempt_root = pair_root / f"condition-{args.condition}"
    if attempt_root != expected_attempt_root:
        raise MeasurementError("attempt output path is not campaign-owned")
    expected_resource = pair_root / f"resource_record_{args.condition}.json"
    legacy_resource = pair_root / "resource_record.json"
    supplied_resource = args.resource_record.resolve(strict=True)
    if supplied_resource not in (expected_resource, legacy_resource):
        raise MeasurementError("attempt resource record is not condition-owned")
    expected_resource = supplied_resource

    resource_record = read_object(expected_resource)
    legacy_pair_resource = resource_record.get("kind") == "highambench-pair-resource"
    stored = resource_record.get("record_sha256")
    payload = dict(resource_record)
    payload.pop("record_sha256", None)
    slot = resource_record.get("slot")
    locked_slots = lock.get("resource_slots")
    if (
        stored != canonical_digest(payload)
        or resource_record.get("schema_version") != 2
        or resource_record.get("kind")
        not in ("highambench-pair-resource", "highambench-attempt-resource")
        or resource_record.get("pair_id") != args.pair_id
        or (
            not legacy_pair_resource
            and resource_record.get("condition") != args.condition
        )
        or resource_record.get("campaign_hardware_identity")
        != lock.get("hardware_identity")
        or not isinstance(slot, Mapping)
        or not isinstance(locked_slots, list)
        or slot not in locked_slots
    ):
        raise MeasurementError("attempt resource record is not campaign-authorized")
    recorded_start = resource_record.get(
        "kernel_proof_at_pair_start"
        if legacy_pair_resource
        else "kernel_proof_at_attempt_worker_start"
    )
    if (
        not isinstance(recorded_start, Mapping)
        or recorded_start.get("schema_version") != resources.SCHEMA_VERSION
        or recorded_start.get("kind") != "highambench-resource-proof"
        or recorded_start.get("verified") is not True
    ):
        raise MeasurementError("attempt resource record lacks its start proof")

    expected_condition_resource = (
        pair_root / f"condition_cgroup_begin_{args.condition}.json"
    )
    if (
        args.condition_resource_record.resolve(strict=True)
        != expected_condition_resource
    ):
        raise MeasurementError("attempt condition resource record is not pair-owned")
    condition_resource = read_object(
        expected_condition_resource,
        kind="highambench-fresh-condition-cgroup-begin",
    )
    parent_cgroup = condition_resource.get("parent_cgroup")
    condition_cgroup = condition_resource.get("cgroup")
    initial = condition_resource.get("initial")
    manager_contract = condition_resource.get("manager_resource_contract")
    wrapper_proof = resource_record.get("kernel_proof_before_exec")
    delegated_layout = (
        wrapper_proof.get("delegated_memory_layout")
        if isinstance(wrapper_proof, Mapping)
        else None
    )
    if (
        condition_resource.get("schema_version") != resources.SCHEMA_VERSION
        or condition_resource.get("verified") is not True
        or condition_resource.get("condition_id") != args.condition
        or condition_resource.get("measurement_scope")
        != "fresh_condition_cgroup_lifetime"
        or condition_resource.get("memory_peak_reset_used") is not False
        or condition_resource.get("expected_logical_cpus")
        != slot.get("logical_cpus")
        or not isinstance(parent_cgroup, Mapping)
        or not isinstance(condition_cgroup, Mapping)
        or not isinstance(initial, Mapping)
        or not isinstance(manager_contract, Mapping)
        or manager_contract.get("schema_version") != resources.SCHEMA_VERSION
        or manager_contract.get("kind") != "highambench-resource-proof"
        or manager_contract.get("verified") is not True
        or not isinstance(wrapper_proof, Mapping)
        or wrapper_proof.get("schema_version") != resources.SCHEMA_VERSION
        or wrapper_proof.get("kind") != "highambench-resource-proof"
        or wrapper_proof.get("verified") is not True
        or not isinstance(delegated_layout, Mapping)
        or delegated_layout.get("root") != parent_cgroup
        or _resource_contract_identity(wrapper_proof)
        != _resource_contract_identity(recorded_start)
        or _resource_contract_identity(manager_contract)
        != _resource_contract_identity(recorded_start)
        or initial.get("cgroup_procs") != ""
        or "populated 0"
        not in str(initial.get("cgroup_events", "")).splitlines()
        or initial.get("memory_current_bytes") != 0
        or initial.get("memory_peak_bytes") != 0
        or initial.get("memory_max") != str(MEMORY_BYTES)
        or initial.get("memory_high") != "max"
        or initial.get("memory_swap_max") != "0"
        or initial.get("memory_oom_group") != "1"
    ):
        raise MeasurementError("attempt condition cgroup record is invalid")
    cgroup_directory = condition_cgroup.get("directory")
    cgroup_device = condition_cgroup.get("device")
    cgroup_inode = condition_cgroup.get("inode")
    if (
        not isinstance(cgroup_directory, str)
        or not isinstance(cgroup_device, int)
        or not isinstance(cgroup_inode, int)
    ):
        raise MeasurementError("attempt condition cgroup identity is incomplete")
    cgroup_path = Path(cgroup_directory)
    try:
        cgroup_metadata = cgroup_path.stat(follow_symlinks=False)
    except OSError as error:
        raise MeasurementError("attempt condition cgroup is unavailable") from error
    if (
        cgroup_path.is_symlink()
        or not stat.S_ISDIR(cgroup_metadata.st_mode)
        or cgroup_path.parent != Path(str(parent_cgroup.get("directory")))
        or cgroup_metadata.st_dev != cgroup_device
        or cgroup_metadata.st_ino != cgroup_inode
    ):
        raise MeasurementError("attempt condition cgroup identity changed")

    live_proof = resources.verify_current_worker(
        slot, expected_memory_bytes=MEMORY_BYTES
    )
    if (
        live_proof.get("schema_version") != resources.SCHEMA_VERSION
        or live_proof.get("kind") != "highambench-resource-proof"
        or live_proof.get("verified") is not True
    ):
        raise MeasurementError("attempt live resource proof is invalid")
    live_identity = _resource_contract_identity(live_proof)
    manager_identity = _resource_contract_identity(recorded_start)
    live_cgroup = live_identity.get("cgroup")
    live_expected = live_identity.get("expected")
    manager_expected = manager_identity.get("expected")
    common_expected_keys = (
        "physical_cores_per_slot",
        "logical_cpus",
        "cpu_list",
        "memory_swap_max_bytes",
        "memory_oom_group",
        "affinity_change_errno",
    )
    live_limits = live_identity.get("cgroup_limits")
    manager_limits = manager_identity.get("cgroup_limits")
    if (
        not isinstance(live_cgroup, Mapping)
        or live_cgroup.get("directory") != cgroup_directory
        or not isinstance(live_expected, Mapping)
        or not isinstance(manager_expected, Mapping)
        or live_expected.get("memory_max_bytes") != MEMORY_BYTES
        or manager_expected.get("memory_max_bytes") != MANAGER_MEMORY_BYTES
        or any(
            live_expected.get(key) != manager_expected.get(key)
            for key in common_expected_keys
        )
        or live_identity.get("sched_getaffinity") != slot.get("logical_cpus")
        or live_identity.get("sched_setaffinity_probe")
        != manager_identity.get("sched_setaffinity_probe")
        or not isinstance(live_limits, Mapping)
        or not isinstance(manager_limits, Mapping)
        or live_limits.get("memory.max") != str(MEMORY_BYTES)
        or manager_limits.get("memory.max") != str(MANAGER_MEMORY_BYTES)
        or any(
            live_limits.get(key) != manager_limits.get(key)
            for key in ("memory.high", "memory.swap.max", "memory.oom.group")
        )
        or live_identity.get("pair_parent_cgroup")
        != manager_identity.get("pair_parent_cgroup")
        or live_identity.get("pair_parent_memory_controls")
        != manager_identity.get("pair_parent_memory_controls")
    ):
        raise MeasurementError("attempt live condition resource contract is invalid")
    entry_proof_path = resolved_regular_file(
        pair_root / f"condition_cgroup_entry_{args.condition}.json",
        label="condition cgroup entry proof",
    )
    entry_proof = read_object(entry_proof_path)
    if (
        entry_proof.get("schema_version") != resources.SCHEMA_VERSION
        or entry_proof.get("kind") != "highambench-resource-proof"
        or entry_proof.get("verified") is not True
        or _resource_contract_identity(entry_proof) != live_identity
    ):
        raise MeasurementError("condition entry/live resource contracts differ")
    return (
        lock,
        resource_record,
        condition_resource,
        live_proof,
        entry_proof_path,
    )


def _task_relative(benchmark_root: Path, declared: str) -> str:
    declared_path = Path(declared)
    marker = Path("benchmark")
    parts = declared_path.parts
    marker_parts = marker.parts
    for index in range(len(parts) - len(marker_parts) + 1):
        if parts[index : index + len(marker_parts)] == marker_parts:
            relative = Path(*parts[index + len(marker_parts) :])
            if not relative.parts:
                break
            return relative.as_posix()
    if not declared_path.is_absolute():
        candidate = benchmark_root / declared_path
        if candidate.exists():
            return declared_path.as_posix()
    raise MeasurementError(f"task path is not below benchmark root: {declared!r}")


def _task_metadata(benchmark_root: Path, task_id: str) -> dict[str, Any]:
    match = re.fullmatch(
        r"(P\d+)-(C[1-3])(?:-([A-Za-z0-9]+(?:-[A-Za-z0-9]+)*))?",
        task_id,
    )
    if match is None:
        raise MeasurementError(f"invalid task id: {task_id!r}")
    paper_id, category, suffix = match.groups()
    task_dir = category if suffix is None else f"{category}-{suffix}"
    task_json = benchmark_root / "tasks" / paper_id / task_dir / "task.json"
    task = read_object(task_json)
    if task.get("task_id") != task_id or task.get("paper_id") != paper_id:
        raise MeasurementError(f"task identity mismatch in {task_json}")
    if task.get("category") != category:
        raise MeasurementError(f"task category mismatch in {task_json}")
    formal = task.get("formal_statement")
    validation = task.get("validation")
    if not isinstance(formal, Mapping) or not isinstance(validation, Mapping):
        raise MeasurementError(f"task lacks formal/validation metadata: {task_id}")
    target = _task_relative(benchmark_root, str(formal.get("target_file")))
    context = _task_relative(benchmark_root, str(task.get("context_file")))
    theorem = validation.get("required_declaration")
    if not isinstance(theorem, str) or not theorem:
        theorem = formal.get("theorem_name")
        namespace = formal.get("namespace")
        if not isinstance(theorem, str) or not theorem:
            raise MeasurementError(f"task lacks required theorem name: {task_id}")
        if isinstance(namespace, str) and namespace and "." not in theorem:
            theorem = f"{namespace}.{theorem}"
    return {
        "task": task,
        "task_json": task_json,
        "task_id": task_id,
        "paper_id": paper_id,
        "category": category,
        "target_relative": target,
        "context_relative": context,
        "target_theorem": theorem,
    }


def _load_controlled_inputs(benchmark_root: Path, task_id: str) -> list[str]:
    path = benchmark_root / "metadata" / "controlled" / f"{task_id}.json"
    value = read_object(path, kind="highambench-controlled-files")
    raw_files = value.get("files")
    if not isinstance(raw_files, list):
        raise MeasurementError(f"controlled file list is invalid: {path}")
    paths: list[str] = []
    for raw in raw_files:
        if (
            not isinstance(raw, Mapping)
            or not isinstance(raw.get("path"), str)
            or not isinstance(raw.get("bytes"), int)
            or not isinstance(raw.get("sha256"), str)
        ):
            raise MeasurementError(f"controlled file entry is invalid: {path}")
        relative = raw["path"]
        # This legacy prompt is not an input to measured-v5.  Its historical
        # descriptor remains in the locked construction metadata, but neither
        # its bytes nor its path may influence staging or authorization.
        if relative == "agent_prompt.md":
            continue
        source = relative_child(benchmark_root, relative)
        if not source.is_file() or source.is_symlink():
            raise MeasurementError(f"controlled input is missing: {source}")
        if source.stat().st_size != raw["bytes"] or sha256_file(source) != raw["sha256"]:
            raise MeasurementError(
                f"fixed controlled input differs from its baseline: {source}"
            )
        paths.append(relative)
    return paths


def _stage_workspace(
    benchmark_root: Path, task_info: Mapping[str, Any], workspace: Path
) -> tuple[Path, Path]:
    if workspace.exists():
        raise MeasurementError(f"fresh attempt workspace already exists: {workspace}")
    task_root = workspace / "task"
    task_root.mkdir(parents=True, mode=0o700)
    records: list[dict[str, Any]] = []
    for relative in _load_controlled_inputs(
        benchmark_root, str(task_info["task_id"])
    ):
        source = relative_child(benchmark_root, relative)
        destination = task_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        destination.chmod(0o444)
        records.append(
            {
                "path": relative,
                "bytes": destination.stat().st_size,
                "sha256": sha256_file(destination),
            }
        )
    controlled = {
        "schema_version": 1,
        "kind": "highambench-controlled-files",
        "label": f"{task_info['task_id']}-campaign-controlled",
        "files": sorted(records, key=lambda item: item["path"]),
    }
    controlled_path = workspace / ".controlled.json"
    atomic_write_json(controlled_path, controlled, mode=0o444)
    target = task_root / str(task_info["target_relative"])
    if not target.is_file():
        raise MeasurementError(f"staged target is missing: {target}")
    candidate = workspace / "candidate.lean"
    shutil.copyfile(target, candidate)
    candidate.chmod(0o600)
    return controlled_path, candidate


def render_effective_prompt(
    benchmark_root: Path,
    task_info: Mapping[str, Any],
    condition: str,
    numstability_commit: str | None,
) -> bytes:
    prompt = (benchmark_root / "measurement_prompt.md").read_text(encoding="utf-8")
    if condition == "L":
        if not isinstance(numstability_commit, str) or re.fullmatch(
            r"[0-9a-f]{40}", numstability_commit
        ) is None:
            raise MeasurementError("condition L requires an exact NumStability commit")
        supplement = (benchmark_root / "condition_prompts" / "L.md").read_text(
            encoding="utf-8"
        )
        if supplement.count("{{NUMSTABILITY_COMMIT}}") != 1:
            raise MeasurementError("condition L prompt has the wrong commit placeholder")
        supplement = supplement.replace("{{NUMSTABILITY_COMMIT}}", numstability_commit)
        prompt += "\n\n" + supplement
    context = (
        benchmark_root / str(task_info["context_relative"])
    ).read_text(encoding="utf-8")
    target = (
        benchmark_root / str(task_info["target_relative"])
    ).read_text(encoding="utf-8")
    effective = (
        prompt.rstrip()
        + "\n\n## Task context\n\n"
        + context.rstrip()
        + "\n\n## Fixed Lean target\n\n```lean\n"
        + target.rstrip()
        + "\n```\n"
    )
    return effective.encode("utf-8")


def _runtime_paths(snapshot: Mapping[str, Any]) -> dict[str, Path | str]:
    source = snapshot.get("source")
    condition_l = snapshot.get("condition_l")
    if not isinstance(source, Mapping) or not isinstance(condition_l, Mapping):
        raise MeasurementError("runtime snapshot lacks source/condition_l")
    numstability = source.get("numstability")
    derived_build = source.get("derived_build")
    if not isinstance(numstability, Mapping) or not isinstance(
        derived_build, Mapping
    ):
        raise MeasurementError("runtime snapshot lacks NumStability identity")
    commit = numstability.get("commit")
    checkout = numstability.get("checkout")
    build_checkout = derived_build.get("checkout")
    library_olean = condition_l.get("lean_build_lib")
    pristine_mathlib = condition_l.get("mathlib_source")
    derived_mathlib = condition_l.get("mathlib_derived_package")
    packages_root = condition_l.get("derived_packages_root")
    if (
        not isinstance(commit, str)
        or re.fullmatch(r"[0-9a-f]{40}", commit) is None
        or not isinstance(checkout, str)
        or not isinstance(build_checkout, str)
        or not isinstance(library_olean, str)
        or not isinstance(pristine_mathlib, str)
        or not isinstance(derived_mathlib, str)
        or not isinstance(packages_root, str)
    ):
        raise MeasurementError("runtime snapshot has invalid dependency paths")
    checkout_path = Path(checkout).resolve()
    build_checkout_path = Path(build_checkout).resolve()
    library_olean_path = Path(library_olean).resolve()
    pristine_mathlib_path = Path(pristine_mathlib).resolve()
    derived_mathlib_path = Path(derived_mathlib).resolve()
    packages_root_path = Path(packages_root).resolve()
    if not all(
        path.is_dir()
        for path in (
            checkout_path,
            build_checkout_path,
            library_olean_path,
            pristine_mathlib_path,
            derived_mathlib_path,
            packages_root_path,
        )
    ):
        raise MeasurementError("runtime dependency checkout is missing")
    try:
        library_olean_path.relative_to(build_checkout_path)
        packages_root_path.relative_to(build_checkout_path)
        derived_mathlib_path.relative_to(packages_root_path)
    except ValueError as error:
        raise MeasurementError(
            "derived NumStability or mathlib path escapes the external build cache"
        ) from error
    if (
        derived_mathlib_path != packages_root_path / "mathlib"
        or packages_root_path != build_checkout_path / ".lake" / "packages"
        or checkout_path == pristine_mathlib_path
        or checkout_path in pristine_mathlib_path.parents
        or pristine_mathlib_path in checkout_path.parents
    ):
        raise MeasurementError("runtime pristine/derived dependency paths are inconsistent")
    return {
        "numstability_commit": commit,
        "numstability_checkout": checkout_path,
        "numstability_build_checkout": build_checkout_path,
        "pristine_mathlib_checkout": pristine_mathlib_path,
        "derived_mathlib_checkout": derived_mathlib_path,
        "packages_root": packages_root_path,
        "library_source": checkout_path / "NumStability",
        "library_root_file": checkout_path / "NumStability.lean",
        "library_olean": library_olean_path,
    }


def _lean_commands(
    benchmark_root: Path,
    workspace_placeholder: str,
    condition: str,
    bwrap: Path,
    toolchain_root: Path,
    packages_root: Path,
    shared_olean_root: Path,
    runtime: Mapping[str, Path | str],
    target_theorem: str,
) -> tuple[list[str], list[str]]:
    lean_isolated = benchmark_root / "tools" / "lean_isolated.py"
    base = [
        sys.executable,
        str(lean_isolated.resolve()),
        "--condition",
        condition,
        "--workspace",
        workspace_placeholder,
        "--toolchain-root",
        str(toolchain_root.resolve()),
        "--packages-root",
        str(packages_root.resolve()),
        "--shared-olean-root",
        str(shared_olean_root.resolve()),
        "--bwrap",
        str(bwrap.resolve(strict=True)),
    ]
    if condition == "L":
        base.extend(
            [
                "--library-source",
                str(runtime["library_source"]),
                "--library-root-file",
                str(runtime["library_root_file"]),
                "--library-olean",
                str(runtime["library_olean"]),
            ]
        )
    compile_command = [
        *base[:2],
        "olean",
        *base[2:],
        "--source",
        "{checked_submission}",
    ]
    audit_command = [
        *base[:2],
        "audit",
        *base[2:],
        "--source",
        "{checked_submission}",
        "--audit-helper",
        str((benchmark_root / "tools" / "dependency_audit.lean").resolve()),
        "--submission-module",
        "{submission_module}",
        "--target-theorem",
        target_theorem,
        "--expected-module",
        "{expected_module}",
        "--expected-theorem",
        "{expected_theorem}",
        "--local-modules-file",
        "{local_modules_file}",
    ]
    return compile_command, audit_command


def _validate_snapshot(
    *,
    benchmark_root: Path,
    workspace: Path,
    candidate_bytes: bytes,
    controlled_manifest: Path,
    task_info: Mapping[str, Any],
    condition: str,
    bwrap: Path,
    toolchain_root: Path,
    packages_root: Path,
    shared_olean_root: Path,
    runtime: Mapping[str, Path | str],
    hidden_parent: Path,
    timeout_seconds: float,
) -> dict[str, Any]:
    ValidationConfig, validate = _import_validator(benchmark_root)
    validation_workspace = hidden_parent / (
        "candidate-" + hashlib.sha256(candidate_bytes).hexdigest()[:16]
    )
    if validation_workspace.exists():
        shutil.rmtree(validation_workspace)
    validation_workspace.mkdir(mode=0o700)
    controlled = read_object(
        controlled_manifest, kind="highambench-controlled-files"
    )
    controlled_files = controlled.get("files")
    if not isinstance(controlled_files, list):
        raise MeasurementError("controlled validation manifest has no files")
    task_source = workspace / "task"
    task_destination = validation_workspace / "task"
    task_destination.mkdir()
    for raw_record in controlled_files:
        if not isinstance(raw_record, Mapping):
            raise MeasurementError("controlled validation file record is invalid")
        relative = raw_record.get("path")
        expected_sha = raw_record.get("sha256")
        expected_bytes = raw_record.get("bytes")
        if (
            not isinstance(relative, str)
            or not isinstance(expected_sha, str)
            or not isinstance(expected_bytes, int)
        ):
            raise MeasurementError("controlled validation file identity is invalid")
        source = relative_child(task_source, relative)
        if source.is_symlink() or not source.is_file():
            raise MeasurementError(f"controlled validation input is invalid: {source}")
        if source.stat().st_size != expected_bytes or sha256_file(source) != expected_sha:
            raise MeasurementError(f"controlled validation input changed: {source}")
        destination = task_destination / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        destination.chmod(0o444)
        if sha256_file(destination) != expected_sha:
            raise MeasurementError(f"controlled validation copy changed: {destination}")
    candidate = validation_workspace / "candidate.lean"
    atomic_write_bytes(candidate, candidate_bytes, mode=0o600)
    manifest_copy = validation_workspace / ".controlled.json"
    atomic_write_json(manifest_copy, controlled, mode=0o444)
    per_command_timeout = _validation_command_timeout(timeout_seconds)
    compile_command, audit_command = _lean_commands(
        benchmark_root,
        "{workspace}",
        condition,
        bwrap,
        toolchain_root,
        packages_root,
        shared_olean_root,
        runtime,
        str(task_info["target_theorem"]),
    )
    config = ValidationConfig(
        workspace=validation_workspace,
        submission_relative="candidate.lean",
        canonical_relative=f"task/{task_info['target_relative']}",
        target_theorem=str(task_info["target_theorem"]),
        compile_command=compile_command,
        condition=condition,
        controlled_manifest=manifest_copy,
        controlled_root_relative="task",
        forbidden_import_prefixes=("NumStability",) if condition == "N" else (),
        audit_command=audit_command,
        submission_module="candidate",
        audit_helper=benchmark_root / "tools" / "dependency_audit.lean",
        hidden_parent=hidden_parent / "validator",
        compile_timeout_seconds=per_command_timeout,
        audit_timeout_seconds=per_command_timeout,
        reject_workspace_local_module_imports=True,
        preserve_full_command_output=True,
    )
    started_ns = time.monotonic_ns()
    try:
        result = validate(config)
    finally:
        shutil.rmtree(validation_workspace, ignore_errors=True)
    result["validation_elapsed_seconds"] = round(
        (time.monotonic_ns() - started_ns) / 1_000_000_000, 6
    )
    result["candidate_sha256"] = hashlib.sha256(candidate_bytes).hexdigest()
    return result


def _unmarked_proof_lines(text: str, target_theorem: str) -> list[str]:
    """Locate the submitted target body without inserting or editing source."""
    root = str(Path(__file__).resolve().parents[2])
    if root not in sys.path:
        sys.path.insert(0, root)
    from benchmark.tools.validator import (
        _declaration_bounds,
        sanitize_lean,
    )

    try:
        match, _, end = _declaration_bounds(text, target_theorem)
    except RuntimeError as error:
        raise MeasurementError(str(error)) from error
    sanitized = sanitize_lean(text, erase_strings=True)
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    index = match.end()
    while index < end - 1:
        char = sanitized[index]
        if char in depths:
            depths[char] += 1
        elif char in closing:
            depths[closing[char]] = max(0, depths[closing[char]] - 1)
        elif sanitized[index:index + 2] == ":=" and not any(depths.values()):
            body_start = index + 2
            by = re.match(r"\s*by\b", sanitized[body_start:end])
            if by:
                body_start += by.end()
            # The introducer's own line is not a proof line unless it also
            # contains a proof term/tactic. Preserve later blank/comment lines.
            newline = text.find("\n", body_start, end)
            if newline != -1 and not text[body_start:newline].strip():
                body_start = newline + 1
            return text[body_start:end].splitlines()
        index += 1
    raise MeasurementError(f"cannot locate proof body of {target_theorem}")


def proof_loc(
    candidate_bytes: bytes, target_theorem: str | None = None
) -> dict[str, Any]:
    """Count lexical lines in the submitted candidate only.

    Import commands are ordinary submitted source lines.  This function never
    opens an imported module, so Mathlib and NumStability implementation lines
    cannot contribute to either LOC metric.
    """
    text = candidate_bytes.decode("utf-8", errors="strict")
    lines = text.splitlines()
    marker_indices = [
        index for index, line in enumerate(lines) if "-- PROOF_START" in line
    ]
    if not marker_indices and target_theorem is not None and text.strip():
        proof_lines = _unmarked_proof_lines(text, target_theorem)
        return {
            "physical_lines": len(lines),
            "nonblank_lines": sum(bool(line.strip()) for line in lines),
            "proof_region_physical_lines": len(proof_lines),
            "proof_region_nonblank_non_line_comment_lines": sum(
                bool(line.strip()) and not line.strip().startswith("--")
                for line in proof_lines
            ),
            "proof_region_source": "target_declaration_without_marker",
        }
    if len(marker_indices) != 1:
        raise MeasurementError("accepted candidate lacks one PROOF_START marker")
    marker_line = lines[marker_indices[0]]
    marker_indent = len(marker_line) - len(marker_line.lstrip())
    proof_lines: list[str] = []
    for line in lines[marker_indices[0] + 1 :]:
        stripped = line.strip()
        indentation = len(line) - len(line.lstrip())
        if (
            stripped
            and not stripped.startswith("--")
            and indentation < marker_indent
        ):
            break
        proof_lines.append(line)

    def code_line(line: str) -> bool:
        stripped = line.strip()
        return bool(stripped) and not stripped.startswith("--")

    return {
        "physical_lines": len(lines),
        "nonblank_lines": sum(bool(line.strip()) for line in lines),
        "proof_region_physical_lines": len(proof_lines),
        "proof_region_nonblank_non_line_comment_lines": sum(
            code_line(line) for line in proof_lines
        ),
    }


def candidate_loc(
    candidate_bytes: bytes, target_theorem: str | None = None
) -> dict[str, Any]:
    """Count the final candidate even when it is not an acceptable proof."""

    try:
        text = candidate_bytes.decode("utf-8", errors="strict")
        utf8_valid = True
    except UnicodeDecodeError:
        text = candidate_bytes.decode("utf-8", errors="replace")
        utf8_valid = False
    lines = text.splitlines()
    result: dict[str, Any] = {
        "physical_lines": len(lines),
        "nonblank_lines": sum(bool(line.strip()) for line in lines),
        "utf8_valid": utf8_valid,
        "proof_region_physical_lines": None,
        "proof_region_nonblank_non_line_comment_lines": None,
        "proof_region_counted": False,
    }
    if utf8_valid:
        try:
            proof = proof_loc(candidate_bytes, target_theorem)
        except MeasurementError as error:
            result["proof_region_error"] = str(error)
        else:
            result.update(proof)
            result["proof_region_counted"] = True
    else:
        result["proof_region_error"] = "candidate is not valid UTF-8"
    return result


def _read_prompt_start(path: Path) -> int | None:
    if not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(value, Mapping):
        return None
    for key in (
        "prompt_started_monotonic_ns",
        "started_at_monotonic_ns",
        "monotonic_ns",
    ):
        candidate = value.get(key)
        if isinstance(candidate, int) and not isinstance(candidate, bool) and candidate > 0:
            return candidate
    return None


def _root_turn_completed_monotonic_ns(
    audit_path: Path, agent_summary: Mapping[str, Any]
) -> int:
    """Return the authenticated protocol receipt time of the final root turn."""

    thread_id = agent_summary.get("thread_id")
    turn_id = agent_summary.get("turn_id")
    if not all(isinstance(value, str) and value for value in (thread_id, turn_id)):
        raise MeasurementError("natural submission lacks a root thread/turn identity")
    matches: list[int] = []
    try:
        lines = audit_path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as error:
        raise MeasurementError(f"cannot read submission protocol: {error}") from error
    for line in lines:
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise MeasurementError(f"submission protocol is malformed: {error}") from error
        message = record.get("message") if isinstance(record, Mapping) else None
        params = message.get("params") if isinstance(message, Mapping) else None
        turn = params.get("turn") if isinstance(params, Mapping) else None
        if (
            isinstance(record, Mapping)
            and record.get("record_type") == "app_server_protocol"
            and record.get("direction") == "app_server_to_adapter"
            and isinstance(message, Mapping)
            and message.get("method") == "turn/completed"
            and isinstance(params, Mapping)
            and params.get("threadId") == thread_id
            and isinstance(turn, Mapping)
            and turn.get("id") == turn_id
            and turn.get("status") == "completed"
        ):
            observed = record.get("monotonic_ns")
            if not isinstance(observed, int) or isinstance(observed, bool):
                raise MeasurementError(
                    "root turn/completed has no monotonic observation time"
                )
            matches.append(observed)
    if len(matches) != 1:
        raise MeasurementError(
            "natural submission lacks exactly one root turn/completed boundary"
        )
    return matches[0]


def _stop_process(
    process: subprocess.Popen[bytes], stop_reason_file: Path, reason: str
) -> dict[str, Any]:
    requested_monotonic_ns = time.monotonic_ns()
    atomic_write_json(
        stop_reason_file,
        {
            "reason": reason,
            "requested_at_utc": utc_now(),
            "requested_monotonic_ns": requested_monotonic_ns,
            "pid": process.pid,
        },
    )
    signal_sent: str | None = None
    if process.poll() is None:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGTERM)
            signal_sent = "SIGTERM"
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
                signal_sent = "SIGKILL"
            process.wait(timeout=5)
    return {
        "reason": reason,
        "signal": signal_sent,
        "returncode": process.poll(),
        "requested_monotonic_ns": requested_monotonic_ns,
        "completed_monotonic_ns": time.monotonic_ns(),
        "completed_at_utc": utc_now(),
    }


def run_attempt(args: argparse.Namespace) -> int:
    benchmark_root = args.benchmark_root.resolve()
    attempt_root = args.attempt_root.resolve()
    if attempt_root.exists():
        raise MeasurementError(f"attempt root already exists: {attempt_root}")
    (
        campaign_lock,
        _resource_value,
        _condition_resource_value,
        live_resource_proof,
        condition_entry_proof_path,
    ) = _campaign_authorization(args, benchmark_root, attempt_root)
    authorized_bwrap = args.bwrap.resolve(strict=True)
    attempt_root.mkdir(parents=True, mode=0o700)
    started_at = utc_now()
    task_info = _task_metadata(benchmark_root, args.task_id)
    snapshot = _authenticated_runtime_snapshot(args.runtime_snapshot)
    runtime = _runtime_paths(snapshot)
    if args.condition == "N" and args.library_runtime_root is not None:
        raise MeasurementError("condition N must not receive a NumStability path")
    if args.condition == "L":
        expected_runtime_root = Path(runtime["numstability_checkout"]).resolve()
        if args.library_runtime_root is None:
            args.library_runtime_root = expected_runtime_root
        elif args.library_runtime_root.resolve() != expected_runtime_root:
            raise MeasurementError("condition L runtime root differs from campaign lock")

    workspace = attempt_root / "workspace"
    controlled_manifest, candidate = _stage_workspace(
        benchmark_root, task_info, workspace
    )
    prompt_path = attempt_root / "effective_prompt.txt"
    prompt_bytes = render_effective_prompt(
        benchmark_root,
        task_info,
        args.condition,
        str(runtime["numstability_commit"]),
    )
    atomic_write_bytes(prompt_path, prompt_bytes, mode=0o444)

    logs = attempt_root / "logs"
    logs.mkdir(mode=0o700)
    audit_path = logs / "codex_protocol.jsonl"
    diagnostics_path = logs / "codex_diagnostics.jsonl"
    summary_path = logs / "codex_summary.json"
    prompt_start_path = logs / "prompt_start.json"
    stop_reason_path = logs / "stop_reason.json"
    process_log_path = logs / "adapter_process.log"
    commands_path = logs / "commands.jsonl"
    validation_path = logs / "validations.jsonl"
    state_parent = attempt_root / "codex_state"
    state_parent.mkdir(mode=0o700)

    adapter = benchmark_root / "scripts" / "observed_codex.py"
    adapter_command = [
        sys.executable,
        str(adapter.resolve()),
        "--condition",
        args.condition,
        "--workspace",
        str(workspace),
        "--controlled-relative",
        "task",
        "--shared-source-root",
        str(workspace / "task" / "shared"),
        "--shared-olean-root",
        str(args.shared_olean_root.resolve()),
        "--prompt-file",
        str(prompt_path),
        "--audit-output",
        str(audit_path),
        "--diagnostics-output",
        str(diagnostics_path),
        "--summary-output",
        str(summary_path),
        "--prompt-start-output",
        str(prompt_start_path),
        "--stop-reason-file",
        str(stop_reason_path),
        "--codex",
        str(args.codex.resolve()),
        "--code-mode-host",
        str(args.code_mode_host.resolve()),
        "--auth-file",
        str(args.auth_file.resolve()),
        "--offline-shell",
        str(args.offline_shell.resolve()),
        "--bwrap",
        str(authorized_bwrap),
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(Path(runtime["packages_root"]).resolve()),
        "--state-parent",
        str(state_parent),
        "--model",
        "gpt-6-sol",
        "--reasoning-effort",
        "xhigh",
    ]
    if args.condition == "L":
        adapter_command.extend(
            [
                "--library-runtime-root",
                str(Path(runtime["numstability_checkout"]).resolve()),
                "--library-runtime-commit",
                str(runtime["numstability_commit"]),
                "--library-olean-root",
                str(Path(runtime["library_olean"]).resolve()),
            ]
        )
    append_jsonl(
        commands_path,
        {
            "kind": "host-command",
            "role": "observed_codex_adapter",
            "argv": adapter_command,
            "recorded_at_utc": utc_now(),
        },
    )
    with process_log_path.open("wb") as process_log:
        process = subprocess.Popen(
            adapter_command,
            stdout=process_log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    setattr(args, "_adapter_process", process)
    setattr(args, "_adapter_stop_reason_path", stop_reason_path)

    startup_deadline = time.monotonic() + STARTUP_SECONDS
    prompt_start_ns: int | None = None
    while time.monotonic() < startup_deadline:
        prompt_start_ns = _read_prompt_start(prompt_start_path)
        if prompt_start_ns is not None:
            break
        if process.poll() is not None:
            break
        time.sleep(0.05)
    if prompt_start_ns is None:
        teardown = _stop_process(process, stop_reason_path, "startup_failure")
        startup_artifacts: dict[str, Any] = {
            "effective_prompt": artifact(prompt_path, relative_to=attempt_root),
            "adapter_process_log": artifact(
                process_log_path, relative_to=attempt_root
            ),
            "commands": artifact(commands_path, relative_to=attempt_root),
        }
        for name, path in (
            ("protocol", audit_path),
            ("diagnostics", diagnostics_path),
            ("agent_summary", summary_path),
            ("stop_reason", stop_reason_path),
        ):
            if path.is_file():
                startup_artifacts[name] = artifact(path, relative_to=attempt_root)
        result = {
            "schema_version": 3,
            "kind": ATTEMPT_KIND,
            "run_id": args.run_id,
            "pair_id": args.pair_id,
            "task_id": args.task_id,
            "condition": args.condition,
            "campaign_id": campaign_lock["campaign_id"],
            "campaign_lock_sha256": campaign_lock["record_sha256"],
            "started_at_utc": started_at,
            "finished_at_utc": utc_now(),
            "pass": False,
            "failure_code": "SYSTEM_ERROR",
            "failure_note": "Codex did not publish an authenticated prompt-start marker",
            "limits": {
                "wall_clock_seconds": int(WALL_SECONDS),
                "token_limit": None,
                "token_usage_recorded": True,
            },
            "model": "gpt-6-sol",
            "reasoning_effort": "xhigh",
            "hidden_chain_of_thought_available": False,
            "prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
            "prompt_bytes": len(prompt_bytes),
            "token_usage": None,
            "token_usage_complete": False,
            "token_usage_completeness_note": "attempt failed before prompt start",
            "teardown": teardown,
            "resource_record": artifact(
                args.resource_record.resolve(),
                relative_to=args.resource_record.resolve().parent,
            ),
            "condition_resource_record": artifact(
                args.condition_resource_record.resolve(),
                relative_to=args.resource_record.resolve().parent,
            ),
            "condition_cgroup_entry_proof": artifact(
                condition_entry_proof_path,
                relative_to=args.resource_record.resolve().parent,
            ),
            "resource_kernel_proof_at_attempt_start": live_resource_proof,
            "runtime_snapshot": artifact(args.runtime_snapshot.resolve()),
            "artifacts": startup_artifacts,
        }
        result["record_sha256"] = canonical_digest(result)
        atomic_write_json(attempt_root / "attempt.json", result, mode=0o444)
        shutil.rmtree(workspace, ignore_errors=True)
        return 2

    deadline_ns = prompt_start_ns + int(WALL_SECONDS * 1_000_000_000)
    accepted_bytes: bytes | None = None
    accepted_validation: dict[str, Any] | None = None
    accepted_elapsed: float | None = None
    submission_observed_ns: int | None = None
    final_validation: dict[str, Any] | None = None
    teardown: dict[str, Any] | None = None
    natural_process_completed = False
    last_candidate_bytes: bytes | None = None
    validation_system_error: str | None = None
    hidden_parent = attempt_root / "hidden"
    hidden_parent.mkdir(mode=0o700)

    while True:
        if process.poll() is not None:
            natural_process_completed = True
            break
        now_ns = time.monotonic_ns()
        remaining = max(0.0, (deadline_ns - now_ns) / 1_000_000_000)
        if remaining <= 0:
            teardown = _stop_process(process, stop_reason_path, "time_limit")
            break
        time.sleep(min(POLL_SECONDS, remaining))

    if teardown is None and not natural_process_completed:
        teardown = _stop_process(process, stop_reason_path, "runner_cleanup")

    agent_summary: Any = None
    if summary_path.is_file():
        with contextlib.suppress(OSError, UnicodeDecodeError, json.JSONDecodeError):
            agent_summary = json.loads(summary_path.read_text(encoding="utf-8"))
    termination = (
        agent_summary.get("termination")
        if isinstance(agent_summary, Mapping)
        else None
    )
    termination_kind = (
        termination.get("kind") if isinstance(termination, Mapping) else None
    )
    if (
        natural_process_completed
        and termination_kind == "natural"
        and isinstance(agent_summary, Mapping)
        and agent_summary.get("turn_status") == "completed"
    ):
        try:
            submission_observed_ns = _root_turn_completed_monotonic_ns(
                audit_path, agent_summary
            )
        except MeasurementError as error:
            validation_system_error = str(error)
        if (
            submission_observed_ns is not None
            and prompt_start_ns <= submission_observed_ns < deadline_ns
        ):
            if candidate.is_file() and not candidate.is_symlink():
                try:
                    candidate_bytes = candidate.read_bytes()
                except OSError as error:
                    validation_system_error = str(error)
                else:
                    last_candidate_bytes = candidate_bytes
                    if candidate_bytes:
                        digest = hashlib.sha256(candidate_bytes).hexdigest()
                        validation_started = time.monotonic_ns()
                        try:
                            validation = _validate_snapshot(
                                benchmark_root=benchmark_root,
                                workspace=workspace,
                                candidate_bytes=candidate_bytes,
                                controlled_manifest=controlled_manifest,
                                task_info=task_info,
                                condition=args.condition,
                                bwrap=authorized_bwrap,
                                toolchain_root=args.toolchain_root.resolve(),
                                packages_root=Path(runtime["packages_root"]),
                                shared_olean_root=args.shared_olean_root.resolve(),
                                runtime=runtime,
                                hidden_parent=hidden_parent,
                                timeout_seconds=(
                                    3.0 * VALIDATION_COMMAND_MAX_SECONDS
                                ),
                            )
                        except (MeasurementError, OSError, ValueError) as error:
                            validation_system_error = str(error)
                            validation = {
                                "pass": False,
                                "failure_code": "SYSTEM_ERROR",
                                "note": str(error),
                                "candidate_sha256": digest,
                            }
                        validation["observed_at_utc"] = utc_now()
                        validation["validation_started_monotonic_ns"] = (
                            validation_started
                        )
                        validation_finished_ns = time.monotonic_ns()
                        validation["validation_finished_monotonic_ns"] = (
                            validation_finished_ns
                        )
                        append_jsonl(validation_path, validation)
                        final_validation = validation
                        if validation.get("pass") is True:
                            accepted_bytes = candidate_bytes
                            accepted_validation = validation
                            accepted_elapsed = (
                                submission_observed_ns - prompt_start_ns
                            ) / 1_000_000_000
    if natural_process_completed:
        requested_monotonic_ns = time.monotonic_ns()
        atomic_write_json(
            stop_reason_path,
            {
                "reason": "agent_turn_completed",
                "requested_at_utc": utc_now(),
                "requested_monotonic_ns": requested_monotonic_ns,
                "pid": process.pid,
                "signal_sent": False,
            },
        )
        teardown = {
            "reason": "agent_turn_completed",
            "signal": None,
            "returncode": process.poll(),
            "requested_monotonic_ns": requested_monotonic_ns,
            "completed_monotonic_ns": time.monotonic_ns(),
            "completed_at_utc": utc_now(),
        }
    if teardown is None:  # pragma: no cover - defensive lifecycle guard
        raise MeasurementError("attempt ended without teardown evidence")
    network_audit = (
        agent_summary.get("network_isolation_audit")
        if isinstance(agent_summary, Mapping)
        else None
    )
    network_violation_count = (
        network_audit.get("violation_count")
        if isinstance(network_audit, Mapping)
        and isinstance(network_audit.get("violation_count"), int)
        else None
    )
    rule_violation = bool(
        termination_kind == "network_violation"
        or (network_violation_count is not None and network_violation_count > 0)
    )
    hidden_validation_system_error = _hidden_validation_system_error(final_validation)
    infrastructure_failure = bool(
        validation_system_error is not None
        or hidden_validation_system_error is not None
        or not isinstance(agent_summary, Mapping)
        or agent_summary.get("error") is not None
        or agent_summary.get("return_code") == 2
        or termination_kind in {None, "adapter_error", "signal"}
        or (
            termination_kind == "natural"
            and agent_summary.get("turn_status") != "completed"
        )
    )
    accepted_loc: dict[str, Any] | None = None
    if accepted_bytes is not None:
        try:
            accepted_loc = proof_loc(accepted_bytes, str(task_info["target_theorem"]))
        except (MeasurementError, UnicodeDecodeError) as error:
            validation_system_error = f"proof LOC measurement failed: {error}"
            infrastructure_failure = True
            accepted_loc = candidate_loc(accepted_bytes, str(task_info["target_theorem"]))
    passed = bool(
        accepted_bytes is not None
        and not rule_violation
        and not infrastructure_failure
    )

    accepted_path: Path | None = None
    disqualified_path: Path | None = None
    loc: dict[str, Any] | None = None
    validated_candidate_loc: dict[str, Any] | None = None
    if passed and accepted_bytes is not None:
        accepted_path = attempt_root / "accepted_proof.lean"
        atomic_write_bytes(accepted_path, accepted_bytes, mode=0o444)
        loc = accepted_loc
        validated_candidate_loc = loc
    elif accepted_bytes is not None:
        disqualified_path = attempt_root / "validated_but_disqualified_candidate.lean"
        atomic_write_bytes(disqualified_path, accepted_bytes, mode=0o444)
        validated_candidate_loc = accepted_loc

    final_candidate_source = (
        "last_observed" if last_candidate_bytes is not None else "none_observed"
    )
    if candidate.is_file() and not candidate.is_symlink():
        with contextlib.suppress(OSError):
            last_candidate_bytes = candidate.read_bytes()
            final_candidate_source = "final_on_disk"
    final_candidate_bytes = (
        last_candidate_bytes if last_candidate_bytes is not None else b""
    )
    final_candidate_path = attempt_root / "final_candidate.lean"
    atomic_write_bytes(final_candidate_path, final_candidate_bytes, mode=0o444)
    final_candidate_loc = candidate_loc(final_candidate_bytes, str(task_info["target_theorem"]))

    # An empty validation log is positive evidence that no candidate snapshot
    # reached the validator.  Seal it just like a non-empty JSONL artifact so a
    # normal NO_SUBMISSION or no-candidate TIME_LIMIT result is independently
    # verifiable instead of looking like missing telemetry.
    if not validation_path.exists():
        atomic_write_bytes(validation_path, b"", mode=0o444)

    artifacts: dict[str, Any] = {
        "effective_prompt": artifact(prompt_path, relative_to=attempt_root),
        "adapter_process_log": artifact(process_log_path, relative_to=attempt_root),
    }
    for name, path in (
        ("protocol", audit_path),
        ("diagnostics", diagnostics_path),
        ("agent_summary", summary_path),
        ("prompt_start", prompt_start_path),
        ("stop_reason", stop_reason_path),
        ("commands", commands_path),
        ("validations", validation_path),
    ):
        if path.is_file():
            artifacts[name] = artifact(path, relative_to=attempt_root)
    if accepted_path is not None:
        artifacts["accepted_proof"] = artifact(
            accepted_path, relative_to=attempt_root
        )
    if disqualified_path is not None:
        artifacts["validated_but_disqualified_candidate"] = artifact(
            disqualified_path, relative_to=attempt_root
        )
    artifacts["final_candidate"] = artifact(
        final_candidate_path, relative_to=attempt_root
    )

    timed_out = bool(
        teardown.get("reason") == "time_limit"
        or (
            submission_observed_ns is not None
            and submission_observed_ns >= deadline_ns
        )
    )
    failure_code = None
    failure_note = None
    if not passed:
        if infrastructure_failure:
            failure_code = "SYSTEM_ERROR"
            failure_note = (
                validation_system_error
                or hidden_validation_system_error
                or (
                    agent_summary.get("turn_error", {}).get("message")
                    if isinstance(agent_summary, Mapping)
                    and isinstance(agent_summary.get("turn_error"), Mapping)
                    else None
                )
                or "Codex adapter did not produce a valid successful terminal summary"
            )
        elif rule_violation:
            failure_code = "RULE_VIOLATION"
            failure_note = (
                f"model-selected commands made {network_violation_count} denied "
                "network request(s)"
            )
        elif timed_out:
            failure_code = "TIME_LIMIT"
            failure_note = "no final candidate was submitted before 7,200 seconds"
        elif isinstance(final_validation, Mapping):
            failure_code = final_validation.get("failure_code") or "PROOF_FAILURE"
            failure_note = final_validation.get("note")
        else:
            failure_code = "NO_SUBMISSION"
            failure_note = "agent completed without a valid candidate.lean"

    attempt_finished_monotonic_ns = time.monotonic_ns()
    record = {
        "schema_version": 3,
        "kind": ATTEMPT_KIND,
        "run_id": args.run_id,
        "pair_id": args.pair_id,
        "task_id": args.task_id,
        "paper_id": task_info["paper_id"],
        "category": task_info["category"],
        "condition": args.condition,
        "campaign_id": campaign_lock["campaign_id"],
        "campaign_lock_sha256": campaign_lock["record_sha256"],
        "started_at_utc": started_at,
        "prompt_started_monotonic_ns": prompt_start_ns,
        "deadline_monotonic_ns": deadline_ns,
        "attempt_finished_monotonic_ns": attempt_finished_monotonic_ns,
        "finished_at_utc": utc_now(),
        "pass": passed,
        "failure_code": failure_code,
        "failure_note": failure_note,
        "infrastructure_failure": infrastructure_failure,
        "rule_violation": rule_violation,
        "network_violation_count": network_violation_count,
        "limits": {
            "wall_clock_seconds": int(WALL_SECONDS),
            "token_limit": None,
            "token_usage_recorded": True,
        },
        "first_valid_seconds": (
            round(accepted_elapsed, 6) if accepted_elapsed is not None else None
        ),
        "submission_observed_monotonic_ns": submission_observed_ns,
        "time_measurement": (
            "authenticated CLOCK_MONOTONIC prompt release to root turn/completed; "
            "hidden validation begins after the submission boundary and is excluded"
        ),
        "post_submission_validation_seconds": (
            round(
                (
                    final_validation["validation_finished_monotonic_ns"]
                    - final_validation["validation_started_monotonic_ns"]
                )
                / 1_000_000_000,
                6,
            )
            if isinstance(final_validation, Mapping)
            and isinstance(
                final_validation.get("validation_started_monotonic_ns"), int
            )
            and isinstance(
                final_validation.get("validation_finished_monotonic_ns"), int
            )
            else None
        ),
        "model": "gpt-6-sol",
        "reasoning_effort": "xhigh",
        "hidden_chain_of_thought_available": False,
        "observable_reasoning_policy": (
            "record only reasoning text or summaries emitted by the Codex API"
        ),
        "prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "prompt_bytes": len(prompt_bytes),
        "task_metadata_limits_ignored": task_info["task"].get("limits"),
        "task_metadata_limits_note": (
            "legacy construction metadata; measurement_protocol.json is authoritative"
        ),
        "numstability": (
            {
                "commit": runtime["numstability_commit"],
                "access": "external_read_only",
            }
            if args.condition == "L"
            else {"access": "absent"}
        ),
        "token_usage": (
            agent_summary.get("raw_response_usage")
            if isinstance(agent_summary, Mapping)
            else None
        ),
        "token_usage_complete": bool(
            isinstance(agent_summary, Mapping)
            and isinstance(agent_summary.get("termination"), Mapping)
            and agent_summary["termination"].get("kind") == "natural"
            and agent_summary.get("error") is None
            and agent_summary.get("turn_status") == "completed"
        ),
        "token_usage_completeness_note": (
            agent_summary.get("raw_response_usage_completeness")
            if isinstance(agent_summary, Mapping)
            else "adapter summary unavailable"
        ),
        "agent_summary": agent_summary,
        "validation": accepted_validation or final_validation,
        "proof_loc": loc,
        "validated_candidate_loc": validated_candidate_loc,
        "final_candidate_loc": final_candidate_loc,
        "final_candidate_source": final_candidate_source,
        "teardown": teardown,
        "resource_record": artifact(
            args.resource_record.resolve(), relative_to=args.resource_record.resolve().parent
        ),
        "condition_resource_record": artifact(
            args.condition_resource_record.resolve(),
            relative_to=args.resource_record.resolve().parent,
        ),
        "condition_cgroup_entry_proof": artifact(
            condition_entry_proof_path,
            relative_to=args.resource_record.resolve().parent,
        ),
        "resource_kernel_proof_at_attempt_start": live_resource_proof,
        "runtime_snapshot": artifact(args.runtime_snapshot.resolve()),
        "artifacts": artifacts,
    }
    record["record_sha256"] = canonical_digest(record)
    atomic_write_json(attempt_root / "attempt.json", record, mode=0o444)
    shutil.rmtree(workspace, ignore_errors=True)
    shutil.rmtree(hidden_parent, ignore_errors=True)
    if infrastructure_failure:
        return 2
    return 0 if passed else 1


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parents[1]
    parser.add_argument("--benchmark-root", type=Path, default=here)
    parser.add_argument("--attempt-root", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--campaign-lock-sha256", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--pair-id", required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition", choices=("N", "L"), required=True)
    parser.add_argument("--runtime-snapshot", type=Path, required=True)
    parser.add_argument("--resource-record", type=Path, required=True)
    parser.add_argument("--condition-resource-record", type=Path, required=True)
    parser.add_argument("--codex", type=Path, required=True)
    parser.add_argument("--code-mode-host", type=Path, required=True)
    parser.add_argument("--auth-file", type=Path, required=True)
    parser.add_argument("--offline-shell", type=Path, required=True)
    parser.add_argument("--bwrap", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--shared-olean-root", type=Path, required=True)
    parser.add_argument("--library-runtime-root", type=Path)
    return parser


def main() -> int:
    arguments = make_parser().parse_args()
    try:
        return run_attempt(arguments)
    except (MeasurementError, OSError, ValueError) as error:
        print(f"run-attempt error: {error}", file=sys.stderr)
        return 2
    finally:
        process = getattr(arguments, "_adapter_process", None)
        stop_path = getattr(arguments, "_adapter_stop_reason_path", None)
        if (
            isinstance(process, subprocess.Popen)
            and process.poll() is None
            and isinstance(stop_path, Path)
        ):
            with contextlib.suppress(BaseException):
                _stop_process(process, stop_path, "runner_exception_cleanup")


if __name__ == "__main__":
    raise SystemExit(main())
