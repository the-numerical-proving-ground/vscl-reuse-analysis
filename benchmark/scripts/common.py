#!/usr/bin/env python3
"""Small shared primitives for the tracked VSCLReuse measurement scripts."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import tempfile
from typing import Any, Iterable, Mapping, Sequence


class MeasurementError(RuntimeError):
    """A fail-closed measurement protocol error."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def resolved_regular_file(path: Path, *, label: str = "artifact") -> Path:
    """Resolve a regular file only after rejecting every symlink component."""

    absolute = Path(os.path.abspath(os.fspath(path)))
    cursor = Path(absolute.anchor)
    for component in absolute.parts[1:]:
        cursor /= component
        if cursor.is_symlink():
            raise MeasurementError(f"{label} contains a symlink component: {cursor}")
    try:
        resolved = absolute.resolve(strict=True)
    except OSError as error:
        raise MeasurementError(f"{label} is missing: {absolute}") from error
    if not resolved.is_file():
        raise MeasurementError(f"{label} is not a regular file: {absolute}")
    return resolved


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise MeasurementError(f"cannot read JSON {path}: {error}") from error


def read_object(path: Path, *, kind: str | None = None) -> dict[str, Any]:
    value = read_json(path)
    if not isinstance(value, dict):
        raise MeasurementError(f"expected a JSON object: {path}")
    if kind is not None and value.get("kind") != kind:
        raise MeasurementError(
            f"{path} has kind {value.get('kind')!r}, expected {kind!r}"
        )
    return value


def atomic_write_bytes(path: Path, payload: bytes, *, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=str(path.parent)
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(mode)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Any, *, mode: int = 0o600) -> None:
    atomic_write_bytes(path, canonical_json_bytes(value), mode=mode)


def append_jsonl(path: Path, value: Mapping[str, Any]) -> None:
    path = Path(os.path.abspath(os.fspath(path)))
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as error:
        raise MeasurementError(
            f"append-only JSONL parent is missing: {path.parent}"
        ) from error
    if parent != path.parent or not parent.is_dir():
        raise MeasurementError(
            f"append-only JSONL parent contains a symlink or is not a directory: {path.parent}"
        )
    payload = canonical_json_bytes(dict(value))
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_CLOEXEC"):
        raise MeasurementError("secure append-only JSONL flags are unavailable")
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_APPEND
        | os.O_NOFOLLOW
        | os.O_CLOEXEC
    )
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as error:
        raise MeasurementError(
            f"cannot securely open append-only JSONL file: {path}"
        ) from error
    locked = False
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        locked = True
        status = os.fstat(descriptor)
        if (
            not stat.S_ISREG(status.st_mode)
            or status.st_uid != os.getuid()
            or stat.S_IMODE(status.st_mode) & 0o077
            or status.st_nlink != 1
        ):
            raise MeasurementError(
                f"append-only JSONL file is not a private, user-owned regular file: {path}"
            )
        remaining = memoryview(payload)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise MeasurementError(f"short append-only JSONL write: {path}")
            remaining = remaining[written:]
        os.fsync(descriptor)
    finally:
        if locked:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            except OSError:
                pass
        os.close(descriptor)


def relative_child(root: Path, relative: str) -> Path:
    if not relative or Path(relative).is_absolute():
        raise MeasurementError(f"invalid relative path: {relative!r}")
    root = root.resolve()
    unresolved = Path(os.path.abspath(os.fspath(root / relative)))
    cursor = Path(unresolved.anchor)
    for component in unresolved.parts[1:]:
        cursor /= component
        if cursor.is_symlink():
            raise MeasurementError(f"path contains a symlink component: {cursor}")
    candidate = unresolved.resolve(strict=False)
    try:
        candidate.relative_to(root)
    except ValueError as error:
        raise MeasurementError(f"path escapes {root}: {relative!r}") from error
    return candidate


def artifact(path: Path, *, relative_to: Path | None = None) -> dict[str, Any]:
    resolved = resolved_regular_file(path)
    label = str(resolved)
    if relative_to is not None:
        try:
            label = resolved.relative_to(relative_to.resolve()).as_posix()
        except ValueError as error:
            raise MeasurementError(f"artifact escapes {relative_to}: {path}") from error
    stat_result = resolved.stat()
    return {
        "path": label,
        "bytes": stat_result.st_size,
        "sha256": sha256_file(resolved),
        "mode": oct(stat_result.st_mode & 0o777),
    }


def manifest_for_paths(root: Path, paths: Iterable[Path]) -> dict[str, Any]:
    root = root.resolve()
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    for original in sorted(paths, key=lambda path: os.fspath(path)):
        raw = resolved_regular_file(original, label="manifest input")
        try:
            relative = raw.relative_to(root).as_posix()
        except ValueError as error:
            raise MeasurementError(f"manifest path escapes {root}: {raw}") from error
        if relative in seen:
            continue
        seen.add(relative)
        if not raw.is_file() or raw.is_symlink():
            raise MeasurementError(f"manifest input is not a regular file: {raw}")
        record = artifact(raw, relative_to=root)
        records.append(
            {
                "path": record["path"],
                "bytes": record["bytes"],
                "sha256": record["sha256"],
            }
        )
    payload = {
        "schema_version": 1,
        "kind": "highambench-file-manifest",
        "root": str(root),
        "files": records,
    }
    payload["manifest_sha256"] = canonical_digest(payload)
    return payload


def manifest_for_tree(root: Path, include_roots: Sequence[Path]) -> dict[str, Any]:
    files: list[Path] = []
    for include in include_roots:
        absolute = Path(os.path.abspath(os.fspath(include)))
        cursor = Path(absolute.anchor)
        for component in absolute.parts[1:]:
            cursor /= component
            if cursor.is_symlink():
                raise MeasurementError(
                    f"manifest root contains a symlink component: {cursor}"
                )
        path = absolute.resolve(strict=True)
        if path.is_file():
            files.append(path)
            continue
        if not path.is_dir():
            raise MeasurementError(f"manifest root is missing: {path}")
        for candidate in path.rglob("*"):
            if candidate.is_symlink():
                raise MeasurementError(
                    f"controlled corpus contains a symlink: {candidate}"
                )
            if candidate.is_file() and "__pycache__" not in candidate.parts:
                files.append(candidate)
    return manifest_for_paths(root, files)


def verify_manifest(root: Path, manifest: Mapping[str, Any]) -> dict[str, Any]:
    if manifest.get("kind") != "highambench-file-manifest":
        raise MeasurementError("invalid controlled manifest kind")
    stored_digest = manifest.get("manifest_sha256")
    without_digest = dict(manifest)
    without_digest.pop("manifest_sha256", None)
    if stored_digest != canonical_digest(without_digest):
        raise MeasurementError("controlled manifest self-hash is invalid")
    expected_records = manifest.get("files")
    if not isinstance(expected_records, list):
        raise MeasurementError("controlled manifest files must be a list")
    actual = manifest_for_paths(
        root,
        [root / str(item.get("path")) for item in expected_records],
    )
    expected = dict(manifest)
    # Absolute checkout paths are provenance, not identity. The campaign verifier
    # supplies the same root but normalize defensively for copied result roots.
    actual["root"] = expected.get("root")
    actual["manifest_sha256"] = canonical_digest(
        {key: value for key, value in actual.items() if key != "manifest_sha256"}
    )
    return {
        "ok": actual == expected,
        "expected_manifest_sha256": stored_digest,
        "actual_manifest_sha256": actual.get("manifest_sha256"),
        "expected_file_count": len(expected_records),
        "actual_file_count": len(actual.get("files", [])),
    }


def command_version(command: Path, *arguments: str) -> dict[str, Any]:
    resolved = command.resolve()
    if not resolved.is_file():
        raise MeasurementError(f"executable is missing: {resolved}")
    completed = subprocess.run(
        [str(resolved), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=30,
        check=False,
    )
    output = completed.stdout.strip()
    if completed.returncode != 0:
        raise MeasurementError(
            f"version command failed ({completed.returncode}): {resolved}: {output}"
        )
    return {
        "path": str(resolved),
        "sha256": sha256_file(resolved),
        "version_output": output,
    }


def git_identity(root: Path) -> dict[str, Any]:
    root = root.resolve()

    def git(*arguments: str) -> str:
        environment = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith("GIT_")
        }
        environment["GIT_OPTIONAL_LOCKS"] = "0"
        completed = subprocess.run(
            ["git", "-C", str(root), *arguments],
            env=environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
            check=False,
        )
        if completed.returncode != 0:
            raise MeasurementError(
                f"git {' '.join(arguments)} failed in {root}: "
                f"{completed.stderr.strip()}"
            )
        return completed.stdout.strip()

    status = git("status", "--porcelain=v1", "--untracked-files=all")
    return {
        "root": str(root),
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current") or None,
        "dirty": bool(status),
        "status_lines": status.splitlines(),
    }


@dataclass(frozen=True)
class CommandResult:
    argv: list[str]
    returncode: int
    started_at_utc: str
    finished_at_utc: str
    stdout: str
    stderr: str

    def as_record(self) -> dict[str, Any]:
        return {
            "argv": self.argv,
            "returncode": self.returncode,
            "started_at_utc": self.started_at_utc,
            "finished_at_utc": self.finished_at_utc,
            "stdout": self.stdout,
            "stderr": self.stderr,
        }


def run_captured(
    argv: Sequence[str],
    *,
    cwd: Path | None = None,
    env: Mapping[str, str] | None = None,
    timeout: float | None = None,
) -> CommandResult:
    started = utc_now()
    completed = subprocess.run(
        list(argv),
        cwd=str(cwd) if cwd else None,
        env=dict(env) if env is not None else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )
    return CommandResult(
        argv=list(argv),
        returncode=completed.returncode,
        started_at_utc=started,
        finished_at_utc=utc_now(),
        stdout=completed.stdout,
        stderr=completed.stderr,
    )
