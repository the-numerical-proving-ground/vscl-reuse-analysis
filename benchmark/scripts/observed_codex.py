#!/usr/bin/env python3
"""Run one observable, uncapped Codex attempt in a Bubblewrap sandbox.

The Codex app-server keeps the host network namespace so it can reach its model
provider.  Commands selected by the model are launched through the mounted
``offline_shell`` seccomp supervisor and therefore cannot open sockets.  Every
line sent to or received from app-server is written to an outer audit JSONL
file.  Only observable reasoning summaries are recorded; hidden model
chain-of-thought is neither available nor claimed.
"""

from __future__ import annotations

import argparse
import contextlib
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import queue
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, Mapping, Sequence, TextIO


MODEL = "gpt-6-sol"
REASONING_EFFORT = "xhigh"
INITIALIZE_REQUEST_ID = 1
THREAD_START_REQUEST_ID = 2
TURN_START_REQUEST_ID = 3
NETWORK_MARKER_ENV = "HIGHAMBENCH_NETWORK_VIOLATION_MARKER"
RAW_USAGE_METHOD = "rawResponse/completed"
CODE_MODE_HOST_FAILURE_FRAGMENT = (
    "failed to spawn code-mode host /codex-code-mode-host"
)

# These are app-server feature names, not an allow/deny list interpreted by the
# model.  A fresh CODEX home also means no user plugin or app configuration is
# inherited by an attempt.
DISABLED_FEATURES = (
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

class AdapterError(RuntimeError):
    """A fail-closed adapter or protocol error."""


class StopRequested(Exception):
    def __init__(self, state: Mapping[str, Any]):
        super().__init__(str(state.get("kind", "stop_requested")))
        self.state = dict(state)


def _timestamps() -> dict[str, int]:
    return {
        "unix_ns": time.time_ns(),
        "monotonic_ns": time.monotonic_ns(),
    }


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _canonical_json_line(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ) + "\n"


def _write_json_exclusive(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(descriptor)


def _regular_file(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_file():
        raise AdapterError(f"{label} must be a regular non-symlink file: {path}")
    return path.resolve(strict=True)


def _executable_regular_file(path: Path, label: str) -> Path:
    resolved = _regular_file(path, label)
    mode = stat.S_IMODE(resolved.stat().st_mode)
    if mode & 0o7000 or not os.access(resolved, os.X_OK):
        raise AdapterError(
            f"{label} must be executable by the benchmark user and have no "
            f"special mode bits: {path}"
        )
    return resolved


def code_mode_host_launch_failure(message: Any) -> bool:
    """Recognize the app-server warning that makes every code-mode tool fail."""

    if not isinstance(message, Mapping) or message.get("method") != "warning":
        return False
    params = message.get("params")
    warning = params.get("message") if isinstance(params, Mapping) else None
    return isinstance(warning, str) and CODE_MODE_HOST_FAILURE_FRAGMENT in warning


def _directory(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise AdapterError(f"{label} must be a non-symlink directory: {path}")
    return path.resolve(strict=True)


def _below(root: Path, path: Path, label: str) -> Path:
    root = root.resolve(strict=True)
    resolved = path.resolve(strict=True)
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise AdapterError(f"{label} escapes {root}: {path}") from error
    return resolved


def _outside_workspace(path: Path, workspace: Path, label: str) -> Path:
    if not path.is_absolute():
        raise AdapterError(f"{label} must be absolute")
    resolved_parent = path.parent.resolve(strict=True)
    candidate = resolved_parent / path.name
    workspace = workspace.resolve(strict=True)
    try:
        candidate.relative_to(workspace)
    except ValueError:
        return candidate
    raise AdapterError(f"{label} must be outside the model-writable workspace")


def _reject_symlinks(root: Path, label: str) -> None:
    for directory, names, files in os.walk(root, followlinks=False):
        base = Path(directory)
        for name in (*names, *files):
            path = base / name
            if path.is_symlink():
                raise AdapterError(f"{label} contains a symlink: {path}")


def _required_runtime_path(root: Path, relative: Path, label: str) -> Path:
    """Resolve a required runtime path after rejecting every symlink component."""

    cursor = root
    for component in relative.parts:
        cursor = cursor / component
        if cursor.is_symlink():
            raise AdapterError(f"{label} contains a symlink component: {cursor}")
    return _below(root, cursor, label)


def _contains_forbidden_library_name(path: Path) -> bool:
    lowered = path.name.casefold().replace("-", "").replace("_", "")
    return lowered == "numstability" or path.name.casefold() == "library_lookup.md"


def _reject_numstability_material(root: Path, label: str) -> None:
    """Keep condition N and the common package mount free of library material."""

    for directory, names, files in os.walk(root, followlinks=False):
        base = Path(directory)
        for name in (*names, *files):
            path = base / name
            if _contains_forbidden_library_name(path):
                raise AdapterError(f"{label} contains NumStability material: {path}")


@dataclass(frozen=True)
class LibraryRuntime:
    root: Path
    commit: str
    source: Path
    root_file: Path
    lookup_guide: Path
    olean: Path


def _library_record(runtime: LibraryRuntime | None) -> dict[str, Any] | None:
    if runtime is None:
        return None
    return {
        "root": str(runtime.root),
        "pristine_source_checkout_root": str(runtime.root),
        "commit": runtime.commit,
        "source": str(runtime.source),
        "root_file": str(runtime.root_file),
        "lookup_guide": str(runtime.lookup_guide),
        "olean": str(runtime.olean),
        "derived_olean_root": str(runtime.olean),
        "detached_checkout_verified": True,
        "pristine_worktree_verified_including_untracked_and_ignored": True,
        "symlink_escape_rejected": True,
        "git_optional_locks": "0",
        "source_and_olean_roots_separate": True,
        "derived_olean_tree_non_writable": True,
        "mounted_read_only": True,
    }


def _git_output(root: Path, arguments: Sequence[str], label: str) -> str:
    environment = {
        key: value for key, value in os.environ.items() if not key.startswith("GIT_")
    }
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    completed = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=environment,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise AdapterError(f"cannot verify {label}: {detail}")
    return completed.stdout.strip()


def _paths_overlap(first: Path, second: Path) -> bool:
    try:
        first.relative_to(second)
        return True
    except ValueError:
        pass
    try:
        second.relative_to(first)
        return True
    except ValueError:
        return False


def _verify_library_olean_root(olean_root: Path, source_root: Path) -> Path:
    """Authenticate a separately built, sealed NumStability Lean object tree."""

    olean_root = _directory(olean_root, "derived library olean root")
    if _paths_overlap(olean_root, source_root):
        raise AdapterError(
            "derived library olean root must be separate from the pristine source checkout"
        )

    entries = [olean_root]
    for directory, names, files in os.walk(olean_root, followlinks=False):
        base = Path(directory)
        entries.extend(base / name for name in (*names, *files))
    for path in entries:
        status = path.lstat()
        if stat.S_ISLNK(status.st_mode):
            raise AdapterError(f"derived library olean root contains a symlink: {path}")
        if not (stat.S_ISDIR(status.st_mode) or stat.S_ISREG(status.st_mode)):
            raise AdapterError(
                f"derived library olean root contains a non-file entry: {path}"
            )
        if stat.S_IMODE(status.st_mode) & 0o222 or os.access(path, os.W_OK):
            raise AdapterError(
                f"derived library olean root contains a writable entry: {path}"
            )

    root_olean = olean_root / "NumStability.olean"
    module_root = olean_root / "NumStability"
    if (
        root_olean.is_symlink()
        or not root_olean.is_file()
        or root_olean.stat().st_size == 0
    ):
        raise AdapterError(
            "derived library olean root lacks nonempty regular NumStability.olean"
        )
    if module_root.is_symlink() or not module_root.is_dir():
        raise AdapterError(
            "derived library olean root lacks the NumStability module directory"
        )
    module_oleans = [
        path
        for path in module_root.rglob("*.olean")
        if path.is_file() and not path.is_symlink() and path.stat().st_size > 0
    ]
    if not module_oleans:
        raise AdapterError("derived library olean root contains no nonempty module oleans")
    return olean_root


def verify_library_runtime(
    root: Path,
    expected_commit: str,
    olean_root: Path,
) -> LibraryRuntime:
    if re.fullmatch(r"[0-9a-f]{40}", expected_commit) is None:
        raise AdapterError("library runtime commit must be a lowercase 40-hex Git commit")
    root = _directory(root, "library runtime root")
    top = Path(_git_output(root, ("rev-parse", "--show-toplevel"), "library worktree"))
    if top.resolve(strict=True) != root:
        raise AdapterError("library runtime root is not the Git worktree root")
    actual_commit = _git_output(root, ("rev-parse", "HEAD"), "library commit")
    if actual_commit != expected_commit:
        raise AdapterError(
            f"library runtime is at {actual_commit}, expected {expected_commit}"
        )
    symbolic = subprocess.run(
        ("git", "-C", str(root), "symbolic-ref", "-q", "HEAD"),
        check=False,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        env={
            **{
                key: value
                for key, value in os.environ.items()
                if not key.startswith("GIT_")
            },
            "GIT_OPTIONAL_LOCKS": "0",
        },
    )
    if symbolic.returncode == 0:
        raise AdapterError("library runtime must be a detached checkout")
    if symbolic.returncode != 1:
        raise AdapterError("could not establish detached library checkout state")
    worktree_status = _git_output(
        root,
        (
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--ignored=matching",
        ),
        "pristine library worktree cleanliness",
    )
    if worktree_status:
        raise AdapterError(
            "pristine library source checkout has tracked, untracked, or ignored material"
        )

    source = _required_runtime_path(root, Path("NumStability"), "library source")
    root_file = _required_runtime_path(
        root, Path("NumStability.lean"), "library root source"
    )
    lookup = _required_runtime_path(
        root, Path("docs/LIBRARY_LOOKUP.md"), "library lookup guide"
    )
    source = _directory(source, "library source")
    root_file = _regular_file(root_file, "library root source")
    lookup = _regular_file(lookup, "library lookup guide")
    _reject_symlinks(source, "library source")
    olean = _verify_library_olean_root(olean_root, root)
    return LibraryRuntime(root, actual_commit, source, root_file, lookup, olean)


class JsonlLog:
    """Thread-safe, immediately flushed JSONL with a total local order."""

    def __init__(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        self.path = path
        self._handle = path.open("x", encoding="utf-8", buffering=1)
        path.chmod(0o600)
        self._lock = threading.Lock()
        self._sequence = 0
        self._closed = False

    def append(self, record_type: str, **fields: Any) -> dict[str, Any]:
        with self._lock:
            if self._closed:
                raise AdapterError(f"attempted to write closed log {self.path}")
            self._sequence += 1
            record = {
                "sequence": self._sequence,
                "record_type": record_type,
                **_timestamps(),
                **fields,
            }
            self._handle.write(_canonical_json_line(record))
            self._handle.flush()
            return record

    def close(self) -> None:
        with self._lock:
            if self._closed:
                return
            self._handle.flush()
            os.fsync(self._handle.fileno())
            self._handle.close()
            self._closed = True


def observable_categories(message: Mapping[str, Any]) -> list[str]:
    """Label useful observable event classes without dropping the raw message."""

    method = message.get("method")
    categories = {"protocol"}
    if method == RAW_USAGE_METHOD or method == "thread/tokenUsage/updated":
        categories.add("token_usage")

    typed_values: list[str] = []

    def visit(value: Any) -> None:
        if isinstance(value, Mapping):
            for key, child in value.items():
                if key in ("type", "kind", "method", "name") and isinstance(child, str):
                    typed_values.append(child.casefold())
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(message)
    joined = " ".join(typed_values)
    if "reasoning" in joined:
        categories.add("observable_reasoning")
    is_tool_output = any(
        term in joined
        for term in ("tool_output", "function_call_output", "commandexecutionoutput")
    )
    if is_tool_output:
        categories.add("tool_output")
    if not is_tool_output and any(
        term in joined for term in ("tool_call", "function_call", "commandexecution")
    ):
        categories.add("tool_call")
    if any(term in joined for term in ("agent_message", "output_text", "assistant")):
        categories.add("model_output")
    return sorted(categories)


def _normalized_usage(value: Any) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise AdapterError("raw response usage is missing or malformed")
    required = (
        "inputTokens",
        "cachedInputTokens",
        "outputTokens",
        "reasoningOutputTokens",
        "totalTokens",
    )
    if not all(
        isinstance(value.get(field), int)
        and not isinstance(value[field], bool)
        and value[field] >= 0
        for field in required
    ):
        raise AdapterError("raw response usage contains an invalid token count")
    cache_write = value.get("cacheWriteInputTokens", 0)
    if not isinstance(cache_write, int) or isinstance(cache_write, bool) or cache_write < 0:
        raise AdapterError("raw response cache-write usage is invalid")
    normalized = {
        "input_tokens": int(value["inputTokens"]),
        "cached_input_tokens": int(value["cachedInputTokens"]),
        "cache_write_input_tokens": int(cache_write),
        "output_tokens": int(value["outputTokens"]),
        "reasoning_output_tokens": int(value["reasoningOutputTokens"]),
        "total_tokens": int(value["totalTokens"]),
    }
    if normalized["cached_input_tokens"] > normalized["input_tokens"]:
        raise AdapterError("cached input exceeds input usage")
    if normalized["cache_write_input_tokens"] > normalized["input_tokens"]:
        raise AdapterError("cache-write input exceeds input usage")
    if normalized["reasoning_output_tokens"] > normalized["output_tokens"]:
        raise AdapterError("reasoning output exceeds output usage")
    if normalized["total_tokens"] != (
        normalized["input_tokens"] + normalized["output_tokens"]
    ):
        raise AdapterError("raw response total usage is inconsistent")
    return normalized


class RawUsageAccumulator:
    """Sum unique raw provider responses without imposing a token limit."""

    FIELDS = (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    )

    def __init__(self) -> None:
        self._responses: dict[str, dict[str, Any]] = {}
        self._order: list[str] = []
        self._duplicates = 0
        self._totals = {field: 0 for field in self.FIELDS}

    def observe(self, message: Mapping[str, Any]) -> None:
        if message.get("method") != RAW_USAGE_METHOD:
            return
        params = message.get("params")
        if not isinstance(params, Mapping):
            raise AdapterError("raw response notification has malformed params")
        response_id = params.get("responseId")
        thread_id = params.get("threadId")
        turn_id = params.get("turnId")
        if not all(
            isinstance(value, str) and value
            for value in (response_id, thread_id, turn_id)
        ):
            raise AdapterError("raw response notification lacks an identity")
        usage = _normalized_usage(params.get("usage"))
        record = {
            "response_id": response_id,
            "thread_id": thread_id,
            "turn_id": turn_id,
            "usage": usage,
        }
        prior = self._responses.get(response_id)
        if prior is not None:
            if prior != record:
                raise AdapterError("raw response id was reused with different usage")
            self._duplicates += 1
            return
        self._responses[str(response_id)] = record
        self._order.append(str(response_id))
        for field in self.FIELDS:
            self._totals[field] += usage[field]

    def snapshot(self) -> dict[str, Any]:
        return {
            "measurement_source": "codex_app_server_rawResponse/completed",
            "scope": "all_observed_unique_completed_responses",
            "limit_enforced": False,
            "input_includes_cached": True,
            "response_count": len(self._order),
            "duplicate_event_count": self._duplicates,
            "response_ids": list(self._order),
            **self._totals,
        }


class ProtocolStreams:
    """JSONL protocol transport used by the live process and fake-stream tests."""

    def __init__(
        self,
        protocol_input: TextIO,
        protocol_output: TextIO,
        audit: JsonlLog,
        usage: RawUsageAccumulator,
    ) -> None:
        self.protocol_input = protocol_input
        self.protocol_output = protocol_output
        self.audit = audit
        self.usage = usage
        self._write_lock = threading.Lock()

    def send(self, message: Mapping[str, Any]) -> None:
        wire = _canonical_json_line(message)
        with self._write_lock:
            self.audit.append(
                "app_server_protocol",
                direction="adapter_to_app_server",
                raw_json=wire.rstrip("\n"),
                message=dict(message),
                observable_categories=observable_categories(message),
            )
            self.protocol_input.write(wire)
            self.protocol_input.flush()

    def receive(self) -> dict[str, Any]:
        line = self.protocol_output.readline()
        if line == "":
            raise EOFError("Codex app-server closed stdout")
        raw = line.rstrip("\n")
        try:
            parsed = json.loads(raw)
        except json.JSONDecodeError as error:
            self.audit.append(
                "app_server_protocol_error",
                direction="app_server_to_adapter",
                raw_json=raw,
                error=str(error),
            )
            raise AdapterError("Codex app-server emitted invalid JSON") from error
        if not isinstance(parsed, dict):
            raise AdapterError("Codex app-server emitted a non-object JSON message")
        self.audit.append(
            "app_server_protocol",
            direction="app_server_to_adapter",
            raw_json=raw,
            message=parsed,
            observable_categories=observable_categories(parsed),
        )
        self.usage.observe(parsed)
        return parsed


class ProtocolMailbox:
    def __init__(self, streams: ProtocolStreams):
        self._streams = streams
        self._queue: queue.Queue[object] = queue.Queue()
        self._thread = threading.Thread(target=self._pump, name="codex-stdout", daemon=True)

    def start(self) -> None:
        self._thread.start()

    def _pump(self) -> None:
        try:
            while True:
                self._queue.put(self._streams.receive())
        except BaseException as error:
            self._queue.put(error)

    def get(self, controller: "StopController", process: subprocess.Popen[str]) -> dict[str, Any]:
        while True:
            stop = controller.state()
            if stop is not None:
                raise StopRequested(stop)
            try:
                item = self._queue.get(timeout=0.1)
            except queue.Empty:
                if process.poll() is not None:
                    raise AdapterError(
                        f"Codex app-server exited unexpectedly with {process.returncode}"
                    )
                continue
            if isinstance(item, BaseException):
                if isinstance(item, EOFError) and process.poll() is not None:
                    raise AdapterError(
                        f"Codex app-server closed stdout with {process.returncode}"
                    ) from item
                raise item
            if not isinstance(item, dict):
                raise AdapterError("internal protocol mailbox corruption")
            return item

    def drain(self, timeout_seconds: float = 0.2) -> None:
        deadline = time.monotonic() + timeout_seconds
        while time.monotonic() < deadline:
            try:
                self._queue.get(timeout=max(0.0, deadline - time.monotonic()))
            except queue.Empty:
                return

    def join(self) -> None:
        self._thread.join(timeout=2.0)


class StopController:
    def __init__(self, control_path: Path | None):
        self.control_path = control_path
        self._signal_name: str | None = None
        self._prior: dict[int, Any] = {}

    def install(self) -> None:
        for number in (signal.SIGINT, signal.SIGTERM):
            self._prior[number] = signal.getsignal(number)

            def handler(_number: int, _frame: Any, *, name=number.name) -> None:
                self._signal_name = name

            signal.signal(number, handler)

    def restore(self) -> None:
        for number, prior in self._prior.items():
            signal.signal(number, prior)

    def _control_reason(self) -> str | None:
        if self.control_path is None or not self.control_path.exists():
            return None
        if self.control_path.is_symlink() or not self.control_path.is_file():
            raise AdapterError("stop-reason control path is not a regular file")
        text = self.control_path.read_text(encoding="utf-8").strip()
        if not text:
            raise AdapterError("stop-reason control file is empty")
        try:
            value = json.loads(text)
        except json.JSONDecodeError:
            reason = text
        else:
            reason = value.get("reason") if isinstance(value, Mapping) else None
        if not isinstance(reason, str) or not reason.strip():
            raise AdapterError("stop-reason control file has no reason")
        return reason.strip()

    def state(self) -> dict[str, Any] | None:
        reason = self._control_reason()
        if reason in ("accepted_candidate", "interrupted_for_accepted_candidate"):
            return {
                "kind": "interrupted_for_accepted_candidate",
                "control_reason": reason,
                "signal": self._signal_name,
            }
        if reason is not None:
            return {
                "kind": "control_stop",
                "control_reason": reason,
                "signal": self._signal_name,
            }
        if self._signal_name is not None:
            return {"kind": "signal", "signal": self._signal_name}
        return None


@dataclass
class AttemptState:
    thread_id: str | None = None
    turn_id: str | None = None
    turn_status: str | None = None
    turn_error: dict[str, Any] | None = None
    turn_completed: dict[str, int] | None = None

    def observe(self, message: Mapping[str, Any]) -> None:
        if code_mode_host_launch_failure(message):
            raise AdapterError("Codex code-mode host failed to launch")
        method = message.get("method")
        params = message.get("params")
        if not isinstance(params, Mapping):
            return
        if method == "thread/started":
            thread = params.get("thread")
            candidate = thread.get("id") if isinstance(thread, Mapping) else params.get("threadId")
            if isinstance(candidate, str) and candidate and self.thread_id is None:
                self.thread_id = candidate
            return
        if method not in ("turn/started", "turn/completed"):
            return
        event_thread_id = params.get("threadId")
        if not isinstance(event_thread_id, str) or not event_thread_id:
            raise AdapterError(f"{method} lacks a thread id")
        if self.thread_id is None:
            raise AdapterError(f"{method} arrived before the root thread identity")
        if event_thread_id != self.thread_id:
            return
        if method == "turn/started":
            turn = params.get("turn")
            candidate = turn.get("id") if isinstance(turn, Mapping) else params.get("turnId")
            if isinstance(candidate, str) and candidate:
                if self.turn_id not in (None, candidate):
                    raise AdapterError("turn/started disagrees with the root turn id")
                self.turn_id = candidate
        else:
            turn = params.get("turn")
            if not isinstance(turn, Mapping):
                raise AdapterError("turn/completed lacks a turn record")
            candidate = turn.get("id")
            status = turn.get("status")
            if not isinstance(candidate, str) or not candidate:
                raise AdapterError("turn/completed lacks a turn id")
            if status not in ("completed", "failed", "interrupted"):
                raise AdapterError("turn/completed has an invalid status")
            if self.turn_id not in (None, candidate):
                raise AdapterError("turn/completed disagrees with the root turn id")
            self.turn_id = candidate
            self.turn_status = status
            error = turn.get("error")
            self.turn_error = dict(error) if isinstance(error, Mapping) else None
            self.turn_completed = _timestamps()


def _result(message: Mapping[str, Any], request_id: int, method: str) -> Mapping[str, Any]:
    if message.get("id") != request_id or "method" in message:
        raise AdapterError(f"internal request matching error for {method}")
    if message.get("error") is not None:
        raise AdapterError(f"Codex app-server rejected {method}: {message['error']}")
    result = message.get("result")
    if not isinstance(result, Mapping):
        raise AdapterError(f"Codex app-server returned malformed {method} result")
    return result


def _request(
    streams: ProtocolStreams,
    mailbox: ProtocolMailbox,
    controller: StopController,
    process: subprocess.Popen[str],
    state: AttemptState,
    request_id: int,
    method: str,
    params: Mapping[str, Any],
) -> Mapping[str, Any]:
    streams.send({"id": request_id, "method": method, "params": dict(params)})
    while True:
        message = mailbox.get(controller, process)
        if message.get("id") == request_id and "method" not in message:
            return _result(message, request_id, method)
        state.observe(message)


def _bind(command: list[str], source: Path, destination: str, writable: bool = False) -> None:
    source = source.resolve(strict=True)
    command.extend(("--bind" if writable else "--ro-bind", str(source), destination))


def _package_mounts(packages_root: Path) -> list[Path]:
    packages_root = _directory(packages_root, "mathlib packages root")
    _reject_numstability_material(packages_root, "mathlib packages root")
    packages = []
    for candidate in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if candidate.is_symlink():
            raise AdapterError(f"package root is a symlink: {candidate}")
        if candidate.is_dir():
            packages.append(candidate.resolve(strict=True))
    if not any(package.name == "mathlib" for package in packages):
        raise AdapterError("mathlib packages root has no mathlib checkout")
    return packages


def _codex_config(model: str, reasoning_effort: str) -> list[str]:
    if model != MODEL or reasoning_effort != REASONING_EFFORT:
        raise AdapterError(f"benchmark adapter requires {MODEL} at {REASONING_EFFORT}")
    return [
        f'model="{model}"',
        f'model_reasoning_effort="{reasoning_effort}"',
        'approval_policy="never"',
        'sandbox_mode="danger-full-access"',
        'history.persistence="none"',
        "memories.use_memories=false",
        "memories.generate_memories=false",
    ]


def bubblewrap_command(
    args: argparse.Namespace,
    state_home: Path,
    network_marker: Path,
    library: LibraryRuntime | None,
) -> list[str]:
    workspace = _directory(args.workspace, "workspace")
    codex = _regular_file(args.codex, "Codex executable")
    code_mode_host = _executable_regular_file(
        args.code_mode_host, "Codex code-mode host executable"
    )
    if (
        code_mode_host.parent != codex.parent
        or code_mode_host.name != "codex-code-mode-host"
    ):
        raise AdapterError(
            "Codex code-mode host must be the exact sibling of the Codex executable"
        )
    offline_shell = _regular_file(args.offline_shell, "offline shell")
    toolchain = _directory(args.toolchain_root, "Lean toolchain")
    shared_source = _directory(args.shared_source_root, "shared source")
    shared_olean = _directory(args.shared_olean_root, "shared olean")
    _reject_numstability_material(workspace, "condition workspace")
    _reject_numstability_material(shared_source, "shared source")
    _reject_numstability_material(shared_olean, "shared olean")
    packages = _package_mounts(args.packages_root)
    marker = _regular_file(network_marker, "network audit marker")
    marker_inside = f"/run/highambench-audit/{marker.name}"
    state_tmp = _directory(state_home.parent / "tmp", "private temporary directory")

    if args.condition == "N" and library is not None:
        raise AdapterError("condition N must not receive a library runtime")
    if args.condition == "L" and library is None:
        raise AdapterError("condition L requires a verified library runtime")

    inside_home = PurePosixPath(args.inside_home)
    if not inside_home.is_absolute() or ".." in inside_home.parts:
        raise AdapterError("inside home must be an absolute normalized path")

    command = [
        str(Path(args.bwrap).resolve(strict=True)),
        "--unshare-all",
        "--share-net",
        "--die-with-parent",
        "--ro-bind", "/usr", "/usr",
        "--ro-bind", "/bin", "/bin",
        "--ro-bind", "/lib", "/lib",
        "--ro-bind", "/lib64", "/lib64",
        "--ro-bind", "/etc", "/etc",
        "--proc", "/proc",
        "--dev", "/dev",
        "--bind", str(state_tmp), "/tmp",
        "--dir", "/run",
        "--dir", "/run/systemd",
        "--dir", "/run/highambench-audit",
    ]
    resolver = Path("/run/systemd/resolve")
    if resolver.is_dir():
        _bind(command, resolver, "/run/systemd/resolve")
    command.extend(("--dir", str(inside_home.parent)))
    _bind(command, state_home, str(inside_home), writable=True)
    _bind(command, workspace, "/workspace", writable=True)
    _bind(command, marker, marker_inside, writable=True)
    controlled = workspace / args.controlled_relative
    if args.controlled_relative:
        controlled = _below(workspace, controlled, "controlled task directory")
        _bind(command, controlled, f"/workspace/{args.controlled_relative}")
    _bind(command, shared_source, "/shared")
    _bind(command, shared_olean, "/shared-olean")
    _bind(command, codex, "/codex")
    _bind(command, code_mode_host, "/codex-code-mode-host")
    _bind(command, offline_shell, "/offline-shell")
    _bind(command, toolchain, "/lean")
    command.extend(("--dir", "/packages"))
    for package in packages:
        _bind(command, package, f"/packages/{package.name}")

    lean_paths = ["/shared-olean", "/shared"]
    if library is not None:
        command.extend(("--dir", "/library", "--dir", "/library/docs"))
        _bind(command, library.source, "/library/NumStability")
        _bind(command, library.root_file, "/library/NumStability.lean")
        _bind(command, library.lookup_guide, "/library/docs/LIBRARY_LOOKUP.md")
        _bind(command, library.olean, "/library-olean")
        lean_paths.append("/library-olean")
    for package in packages:
        build = package / ".lake" / "build" / "lib" / "lean"
        if build.is_dir():
            lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    lean_paths.extend(("/lean/lib/lean", "/workspace"))

    command.extend(
        (
            "--setenv", "PATH", "/lean/bin:/usr/bin:/bin",
            "--setenv", "HOME", str(inside_home),
            "--setenv", "CODEX_HOME", str(inside_home / ".codex"),
            "--setenv", "TMPDIR", "/tmp",
            "--setenv", "LEAN_PATH", ":".join(lean_paths),
            "--setenv", "SHELL", "/offline-shell",
            "--setenv", NETWORK_MARKER_ENV, marker_inside,
            "--chdir", "/workspace",
            "/codex", "app-server", "--stdio", "--strict-config",
        )
    )
    for config in _codex_config(args.model, args.reasoning_effort):
        command.extend(("--config", config))
    for feature in DISABLED_FEATURES:
        command.extend(("--disable", feature))
    return command


def effective_prompt(prompt_file: Path) -> str:
    prompt_file = _regular_file(prompt_file, "effective prompt")
    raw = prompt_file.read_bytes()
    if not raw:
        raise AdapterError("effective prompt is empty")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise AdapterError("effective prompt is not valid UTF-8") from error


def _sanitized_environment() -> dict[str, str]:
    allowed = ("LANG", "LC_ALL", "TERM", "TZ")
    environment = {key: os.environ[key] for key in allowed if key in os.environ}
    environment["PATH"] = "/usr/bin:/bin"
    return environment


def _thread_id(result: Mapping[str, Any]) -> str:
    thread = result.get("thread")
    candidate = thread.get("id") if isinstance(thread, Mapping) else result.get("threadId")
    if not isinstance(candidate, str) or not candidate:
        raise AdapterError("thread/start returned no thread id")
    return candidate


def _turn_id(result: Mapping[str, Any]) -> str:
    turn = result.get("turn")
    candidate = turn.get("id") if isinstance(turn, Mapping) else result.get("turnId")
    if not isinstance(candidate, str) or not candidate:
        raise AdapterError("turn/start returned no turn id")
    return candidate


def _candidate_record(workspace: Path) -> dict[str, Any]:
    path = workspace / "candidate.lean"
    record: dict[str, Any] = {"path": str(path), "exists": path.exists()}
    if path.is_symlink():
        record.update({"valid_regular_file": False, "error": "symlink"})
        return record
    if not path.is_file():
        record["valid_regular_file"] = False
        return record
    data = path.read_bytes()
    record.update(
        {
            "valid_regular_file": True,
            "size_bytes": len(data),
            "sha256": _sha256_bytes(data),
            "loc": len(data.decode("utf-8", errors="replace").splitlines()),
        }
    )
    return record


def _marker_identity(path: Path) -> dict[str, Any]:
    metadata = path.lstat()
    return {
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
        "mode": metadata.st_mode,
        "link_count": metadata.st_nlink,
        "size_bytes": metadata.st_size,
        "ctime_ns": metadata.st_ctime_ns,
        "mtime_ns": metadata.st_mtime_ns,
    }


def network_marker_record(
    path: Path, initial: Mapping[str, Any]
) -> dict[str, Any]:
    """Authenticate the kernel-owned evidence inode and fail closed on tampering."""

    if not path.exists() or path.is_symlink() or not path.is_file():
        return {
            "present": False,
            "violation_count": 1,
            "tamper_detected": True,
            "integrity": "missing_or_replaced",
            "initial": dict(initial),
        }
    final = _marker_identity(path)
    data = path.read_bytes()
    same_inode = all(
        final.get(key) == initial.get(key)
        for key in ("device", "inode", "mode", "link_count")
    )
    metadata_changed = any(
        final.get(key) != initial.get(key) for key in ("ctime_ns", "mtime_ns")
    )
    tamper_detected = bool(
        not same_inode
        or final.get("size_bytes") != len(data)
        or (not data and metadata_changed)
    )
    violation_count = len(data) if data else (1 if tamper_detected else 0)
    return {
        "present": True,
        "violation_count": violation_count,
        "tamper_detected": tamper_detected,
        "integrity": "tampered" if tamper_detected else "authenticated",
        "size_bytes": len(data),
        "sha256": _sha256_bytes(data),
        "initial": dict(initial),
        "final": final,
    }


def _stop_process(process: subprocess.Popen[str] | None) -> dict[str, Any] | None:
    if process is None:
        return None
    started = _timestamps()
    if process.stdin is not None:
        with contextlib.suppress(OSError, ValueError):
            process.stdin.close()
    sent: str | None = None
    if process.poll() is None:
        try:
            process.wait(timeout=0.25)
        except subprocess.TimeoutExpired:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGTERM)
                sent = "SIGTERM"
    if process.poll() is None:
        try:
            process.wait(timeout=2.0)
        except subprocess.TimeoutExpired:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
                sent = "SIGKILL"
            process.wait(timeout=2.0)
    return {
        "started": started,
        "completed": _timestamps(),
        "signal_sent": sent,
        "returncode": process.poll(),
    }


def _stderr_pump(
    stream: TextIO,
    diagnostics: JsonlLog,
    audit: JsonlLog,
) -> None:
    for line in stream:
        raw = line.rstrip("\n")
        diagnostics.append("app_server_stderr", raw_line=raw)
        audit.append("app_server_diagnostic", stream="stderr", raw_line=raw)


def _provenance(args: argparse.Namespace, command: Sequence[str]) -> dict[str, Any]:
    return {
        "adapter_argv": list(sys.argv),
        "bubblewrap_argv": list(command),
        "codex_config_overrides": _codex_config(args.model, args.reasoning_effort),
        "disabled_features": list(DISABLED_FEATURES),
        "enabled_features": [],
        "model": args.model,
        "root_reasoning_effort": args.reasoning_effort,
        "subagents_enabled": False,
        "parallel_subagents_enabled": False,
        "max_concurrent_threads_per_session": 1,
        "rollout_budget_configured": False,
        "provider_token_gate_configured": False,
        "token_limit_configured": False,
        "adapter_path": str(Path(__file__).resolve()),
        "adapter_sha256": _sha256_file(Path(__file__).resolve()),
        "codex_path": str(Path(args.codex).resolve()),
        "codex_sha256": _sha256_file(Path(args.codex).resolve()),
        "code_mode_host_path": str(Path(args.code_mode_host).resolve()),
        "code_mode_host_sha256": _sha256_file(Path(args.code_mode_host).resolve()),
        "offline_shell_path": str(Path(args.offline_shell).resolve()),
        "offline_shell_sha256": _sha256_file(Path(args.offline_shell).resolve()),
    }


def run(args: argparse.Namespace) -> int:
    started = _timestamps()
    workspace = _directory(args.workspace, "workspace")
    audit_path = _outside_workspace(args.audit_output, workspace, "audit output")
    diagnostics_path = _outside_workspace(
        args.diagnostics_output, workspace, "diagnostics output"
    )
    summary_path = _outside_workspace(args.summary_output, workspace, "summary output")
    start_path = _outside_workspace(
        args.prompt_start_output, workspace, "prompt-start output"
    )
    for output in (audit_path, diagnostics_path, summary_path, start_path):
        if output.exists() or output.is_symlink():
            raise AdapterError(f"attempt output already exists: {output}")
    control_path = None
    if args.stop_reason_file is not None:
        control_path = _outside_workspace(
            args.stop_reason_file, workspace, "stop-reason control file"
        )

    audit = JsonlLog(audit_path)
    diagnostics = JsonlLog(diagnostics_path)
    usage = RawUsageAccumulator()
    controller = StopController(control_path)
    controller.install()
    process: subprocess.Popen[str] | None = None
    mailbox: ProtocolMailbox | None = None
    stderr_thread: threading.Thread | None = None
    state_root: Path | None = None
    network_marker: Path | None = None
    network_marker_initial: dict[str, Any] | None = None
    command: list[str] = []
    attempt = AttemptState()
    termination: dict[str, Any] = {"kind": "adapter_error"}
    error_record: dict[str, str] | None = None
    prompt_started = False
    auth_removed_before_prompt = False
    teardown: dict[str, Any] | None = None
    library: LibraryRuntime | None = None
    provenance: dict[str, Any] | None = None
    return_code = 2
    try:
        if args.condition == "L":
            if (
                args.library_runtime_root is None
                or args.library_runtime_commit is None
                or args.library_olean_root is None
            ):
                raise AdapterError(
                    "condition L requires --library-runtime-root, "
                    "--library-runtime-commit, and --library-olean-root"
                )
            library = verify_library_runtime(
                args.library_runtime_root,
                args.library_runtime_commit,
                args.library_olean_root,
            )
        elif (
            args.library_runtime_root is not None
            or args.library_runtime_commit is not None
            or args.library_olean_root is not None
        ):
            raise AdapterError("condition N must not receive library runtime arguments")

        prompt = effective_prompt(args.prompt_file)
        state_parent = _directory(args.state_parent, "Codex state parent")
        state_root = Path(tempfile.mkdtemp(prefix="highambench-observed-", dir=state_parent))
        state_home = state_root / "home"
        (state_root / "tmp").mkdir(mode=0o700)
        codex_state = state_home / ".codex"
        codex_state.mkdir(parents=True)
        temporary_auth = codex_state / "auth.json"
        shutil.copyfile(_regular_file(args.auth_file, "Codex auth file"), temporary_auth)
        temporary_auth.chmod(0o600)

        marker_fd, marker_name = tempfile.mkstemp(
            prefix="network-audit-", dir=state_root
        )
        os.close(marker_fd)
        network_marker = Path(marker_name)
        network_marker_initial = _marker_identity(network_marker)
        command = bubblewrap_command(args, state_home, network_marker, library)
        provenance = _provenance(args, command)
        audit.append(
            "adapter_start",
            schema_version=1,
            condition=args.condition,
            hidden_chain_of_thought_available=False,
            observable_reasoning_policy=(
                "record every reasoning summary/text event emitted by app-server; "
                "private chain-of-thought is unavailable"
            ),
            prompt_file=str(Path(args.prompt_file).resolve()),
            prompt_sha256=_sha256_bytes(prompt.encode("utf-8")),
            prompt=prompt,
            library_runtime=_library_record(library),
            provenance=provenance,
        )

        process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
            env=_sanitized_environment(),
            start_new_session=True,
        )
        if process.stdin is None or process.stdout is None or process.stderr is None:
            raise AdapterError("could not open Codex app-server protocol pipes")
        streams = ProtocolStreams(process.stdin, process.stdout, audit, usage)
        mailbox = ProtocolMailbox(streams)
        mailbox.start()
        stderr_thread = threading.Thread(
            target=_stderr_pump,
            args=(process.stderr, diagnostics, audit),
            name="codex-stderr",
            daemon=True,
        )
        stderr_thread.start()

        _request(
            streams,
            mailbox,
            controller,
            process,
            attempt,
            INITIALIZE_REQUEST_ID,
            "initialize",
            {
                "clientInfo": {
                    "name": "highambench-observed",
                    "title": "VSCLReuse observed adapter",
                    "version": "1",
                },
                "capabilities": {"experimentalApi": True},
            },
        )
        streams.send({"method": "initialized"})
        thread_result = _request(
            streams,
            mailbox,
            controller,
            process,
            attempt,
            THREAD_START_REQUEST_ID,
            "thread/start",
            {
                "approvalPolicy": "never",
                "cwd": "/workspace",
                "ephemeral": False,
                "experimentalRawEvents": True,
                "historyMode": "legacy",
                "model": args.model,
                "sandbox": "danger-full-access",
            },
        )
        result_thread_id = _thread_id(thread_result)
        if attempt.thread_id not in (None, result_thread_id):
            raise AdapterError("thread/start response disagrees with the root thread id")
        attempt.thread_id = result_thread_id

        # Codex loads the credential while starting the thread.  It is unlinked
        # before the prompt-bearing request can launch any model-selected tool.
        temporary_auth.unlink(missing_ok=True)
        if temporary_auth.exists():
            raise AdapterError("temporary Codex authentication could not be removed")
        auth_removed_before_prompt = True
        audit.append(
            "temporary_auth_removed",
            before_turn_start=True,
            state_home=str(state_home),
        )

        turn_request = {
            "id": TURN_START_REQUEST_ID,
            "method": "turn/start",
            "params": {
                "approvalPolicy": "never",
                "cwd": "/workspace",
                "effort": args.reasoning_effort,
                "input": [{"type": "text", "text": prompt}],
                "model": args.model,
                "sandboxPolicy": {"type": "dangerFullAccess"},
                "threadId": attempt.thread_id,
            },
        }
        turn_wire = _canonical_json_line(turn_request)
        streams.send(turn_request)
        start_record = {
            "schema_version": 1,
            "kind": "highambench_prompt_started",
            **_timestamps(),
            "thread_id": attempt.thread_id,
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
            "prompt_sha256": _sha256_bytes(prompt.encode("utf-8")),
            "turn_start_wire_sha256": _sha256_bytes(turn_wire.encode("utf-8")),
            "temporary_auth_removed": True,
            "turn_start_flushed": True,
        }
        _write_json_exclusive(start_path, start_record)
        prompt_started = True
        audit.append("prompt_start_marker_written", marker=start_record)
        turn_response_seen = False
        while not (turn_response_seen and attempt.turn_status is not None):
            message = mailbox.get(controller, process)
            if message.get("id") == TURN_START_REQUEST_ID and "method" not in message:
                result = _result(message, TURN_START_REQUEST_ID, "turn/start")
                result_turn_id = _turn_id(result)
                if attempt.turn_id not in (None, result_turn_id):
                    raise AdapterError(
                        "turn/start response disagrees with the observed turn id"
                    )
                attempt.turn_id = result_turn_id
                turn_response_seen = True
                continue
            attempt.observe(message)
        mailbox.drain()
        termination = {"kind": "natural", "turn_status": attempt.turn_status}
        return_code = 0 if attempt.turn_status == "completed" else 1
    except StopRequested as stopped:
        termination = dict(stopped.state)
        return_code = 0 if termination.get("kind") == "interrupted_for_accepted_candidate" else 130
        audit.append("adapter_stop_requested", stop=termination)
    except BaseException as error:
        if isinstance(error, KeyboardInterrupt):
            termination = {"kind": "signal", "signal": "SIGINT"}
            return_code = 130
        else:
            error_record = {"type": type(error).__name__, "message": str(error)}
            termination = {"kind": "adapter_error"}
            audit.append("adapter_error", error=error_record)
            return_code = 2
    finally:
        # A control file written immediately before SIGTERM wins over a generic
        # signal label, including when the signal arrived during setup.
        with contextlib.suppress(BaseException):
            final_stop = controller.state()
            if (
                final_stop is not None
                and final_stop.get("kind") == "interrupted_for_accepted_candidate"
            ):
                termination = final_stop
                return_code = 0
        teardown = _stop_process(process)
        if mailbox is not None:
            mailbox.join()
        if stderr_thread is not None:
            stderr_thread.join(timeout=2.0)

        marker_record: dict[str, Any] = {
            "present": False,
            "violation_count": 0,
            "tamper_detected": False,
            "integrity": "not_initialized",
        }
        if network_marker is not None and network_marker_initial is not None:
            marker_record = network_marker_record(
                network_marker, network_marker_initial
            )
            network_marker.unlink(missing_ok=True)
            if marker_record["violation_count"]:
                termination = {
                    "kind": "network_violation",
                    "prior": termination,
                    "turn_status": attempt.turn_status,
                    "evidence_integrity": marker_record["integrity"],
                }
                return_code = 1

        candidate = _candidate_record(workspace)
        if termination.get("kind") in ("natural", "interrupted_for_accepted_candidate"):
            if not candidate.get("valid_regular_file"):
                return_code = 1
                termination = {
                    "kind": "candidate_missing_or_invalid",
                    "prior": termination,
                }

        completed = _timestamps()
        summary_base = {
            "schema_version": 1,
            "condition": args.condition,
            "started": started,
            "completed": completed,
            "duration_seconds": max(
                0.0, (completed["monotonic_ns"] - started["monotonic_ns"]) / 1e9
            ),
            "return_code": return_code,
            "termination": termination,
            "interrupted_for_accepted_candidate": (
                termination.get("kind") == "interrupted_for_accepted_candidate"
            ),
            "prompt_started": prompt_started,
            "temporary_auth_removed_before_prompt": auth_removed_before_prompt,
            "thread_id": attempt.thread_id,
            "turn_id": attempt.turn_id,
            "turn_status": attempt.turn_status,
            "turn_completed": attempt.turn_completed,
            "turn_error": attempt.turn_error,
            "hidden_chain_of_thought_available": False,
            "observable_reasoning_recorded_in_audit": True,
            "raw_response_usage": usage.snapshot(),
            "raw_response_usage_completeness": (
                "all rawResponse/completed events emitted before app-server teardown; "
                "provider-private or interrupted in-flight usage is not observable"
            ),
            "candidate": candidate,
            "library_runtime": _library_record(library),
            "network_isolation_audit": marker_record,
            "process_teardown": teardown,
            "error": error_record,
            "provenance": (
                provenance if provenance is not None else {
                    "adapter_argv": list(sys.argv),
                    "model": args.model,
                    "root_reasoning_effort": args.reasoning_effort,
                }
            ),
        }
        with contextlib.suppress(BaseException):
            audit.append("adapter_terminal", summary=summary_base)
        audit.close()
        diagnostics.close()
        summary_base["audit"] = {
            "path": str(audit_path),
            "sha256": _sha256_file(audit_path),
        }
        summary_base["diagnostics"] = {
            "path": str(diagnostics_path),
            "sha256": _sha256_file(diagnostics_path),
        }
        try:
            _write_json_exclusive(summary_path, summary_base)
        finally:
            if state_root is not None:
                shutil.rmtree(state_root, ignore_errors=True)
            controller.restore()
    return return_code


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--condition", required=True, choices=("N", "L"))
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--controlled-relative", default="task")
    parser.add_argument("--shared-source-root", required=True, type=Path)
    parser.add_argument("--shared-olean-root", required=True, type=Path)
    parser.add_argument("--prompt-file", required=True, type=Path)
    parser.add_argument("--audit-output", required=True, type=Path)
    parser.add_argument("--diagnostics-output", required=True, type=Path)
    parser.add_argument("--summary-output", required=True, type=Path)
    parser.add_argument("--prompt-start-output", required=True, type=Path)
    parser.add_argument("--stop-reason-file", type=Path)
    parser.add_argument("--codex", required=True, type=Path)
    parser.add_argument("--code-mode-host", required=True, type=Path)
    parser.add_argument("--auth-file", required=True, type=Path)
    parser.add_argument("--offline-shell", required=True, type=Path)
    parser.add_argument("--toolchain-root", required=True, type=Path)
    parser.add_argument("--packages-root", required=True, type=Path)
    parser.add_argument("--library-runtime-root", type=Path)
    parser.add_argument("--library-runtime-commit")
    parser.add_argument("--library-olean-root", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    parser.add_argument("--state-parent", required=True, type=Path)
    parser.add_argument("--inside-home", default="/sandbox/agent")
    parser.add_argument("--model", choices=(MODEL,), default=MODEL)
    parser.add_argument(
        "--reasoning-effort", choices=(REASONING_EFFORT,), default=REASONING_EFFORT
    )
    return parser


def main() -> int:
    try:
        return run(make_parser().parse_args())
    except (AdapterError, OSError, ValueError) as error:
        print(f"observed Codex adapter error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
