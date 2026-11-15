#!/usr/bin/python3 -I
"""Restricted sudo frontend for the host-namespace VSCLReuse CPU guard.

The sudo-authorized program deliberately contains no CPU/cgroup operations.
It authenticates the configured operator and relays the exact command line to
the separately installed, root-owned host helper through a transient system
service.  A service created by the host system manager enters the manager's
PID namespace, allowing the host helper to inspect every host task before it
changes a CPU partition.
"""

from __future__ import annotations

import contextlib
import fcntl
import json
import math
import os
import re
import secrets
import stat
import subprocess
import sys
from pathlib import Path
from typing import Sequence


CONFIG_PATH = Path("/etc/highambench/cpu-guard.json")
HOST_HELPER = Path("/usr/local/libexec/highambench/highambench-cpu-guard-host")
INSTALL_LOCK = Path("/var/lib/highambench-cpu-guard/relay-install.lock")
SYSTEMD_RUN = "/usr/bin/systemd-run"
MAX_CONFIG_BYTES = 65_536
SAFE_ENV = {
    "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
    "LANG": "C",
    "LC_ALL": "C",
}


def _verify_secure_directory(path: Path, *, exact_mode: int | None = None) -> None:
    try:
        info = os.lstat(path)
    except OSError as error:
        raise FrontendError(f"cannot inspect privileged directory {path}: {error}") from error
    mode = stat.S_IMODE(info.st_mode)
    if (
        stat.S_ISLNK(info.st_mode)
        or not stat.S_ISDIR(info.st_mode)
        or info.st_uid != 0
        or info.st_gid != 0
        or mode & 0o022
        or (exact_mode is not None and mode != exact_mode)
    ):
        raise FrontendError(f"privileged directory is not secure: {path}")


class FrontendError(RuntimeError):
    """A fail-closed frontend authentication or relay error."""


@contextlib.contextmanager
def _installation_generation_lock(path: Path = INSTALL_LOCK):
    """Hold the shared code/config generation lock for the complete relay."""

    _verify_secure_directory(path.parent, exact_mode=0o700)
    try:
        descriptor = os.open(
            path,
            os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
    except OSError as error:
        raise FrontendError(f"cannot open installation generation lock: {error}") from error
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != 0
            or info.st_gid != 0
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink != 1
            or info.st_nlink != 1
        ):
            raise FrontendError(
                "installation generation lock must be root-owned mode 0600"
            )
        fcntl.flock(descriptor, fcntl.LOCK_SH)
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _strict_json_loads(raw: str) -> object:
    def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in items:
            if key in result:
                raise FrontendError(f"duplicate JSON key: {key!r}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> object:
        raise FrontendError(f"non-finite JSON number is forbidden: {value}")

    def finite_float(value: str) -> float:
        parsed = float(value)
        if not math.isfinite(parsed):
            raise FrontendError(f"non-finite JSON number is forbidden: {value}")
        return parsed

    return json.loads(
        raw,
        object_pairs_hook=pairs,
        parse_constant=invalid_constant,
        parse_float=finite_float,
    )


def _read_root_configuration(path: Path = CONFIG_PATH) -> dict[str, object]:
    """Read the fixed root configuration without following a final symlink."""

    _verify_secure_directory(path.parent, exact_mode=0o755)
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    except OSError as error:
        raise FrontendError(f"cannot open root configuration: {error}") from error
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != 0
            or info.st_gid != 0
            or stat.S_IMODE(info.st_mode) != 0o600
        ):
            raise FrontendError(
                "root configuration must be a root-owned mode-0600 regular file"
            )
        chunks: list[bytes] = []
        size = 0
        while True:
            chunk = os.read(descriptor, min(8192, MAX_CONFIG_BYTES + 1 - size))
            if not chunk:
                break
            chunks.append(chunk)
            size += len(chunk)
            if size > MAX_CONFIG_BYTES:
                raise FrontendError("CPU-guard configuration is oversized")
    finally:
        os.close(descriptor)
    try:
        value = _strict_json_loads(b"".join(chunks).decode("utf-8"))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise FrontendError(f"cannot parse CPU-guard configuration: {error}") from error
    if not isinstance(value, dict) or value.get("schema_version") != 1:
        raise FrontendError("unsupported CPU-guard configuration")
    operator_uid = value.get("operator_uid")
    if (
        isinstance(operator_uid, bool)
        or not isinstance(operator_uid, int)
        or not 1 <= operator_uid <= 2**31 - 1
    ):
        raise FrontendError("configuration operator_uid is invalid")
    return value


def _authorize(operator_uid: int) -> None:
    if os.geteuid() != 0:
        raise FrontendError("CPU-guard frontend must run as root through sudo")
    sudo_uid = os.environ.get("SUDO_UID")
    if sudo_uid is None:
        # Root retains a direct administrative recovery path.  The internal
        # host helper is never granted to the configured unprivileged user.
        if os.getuid() != 0:
            raise FrontendError("cannot identify the invoking operator")
        return
    if re.fullmatch(r"[0-9]+", sudo_uid) is None or int(sudo_uid) != operator_uid:
        raise FrontendError("invoking sudo user is not the configured operator")


def _verify_host_helper(path: Path = HOST_HELPER) -> None:
    if path != HOST_HELPER:
        raise FrontendError("internal host helper path is not fixed")
    for parent in (
        Path("/usr/local"),
        Path("/usr/local/libexec"),
        Path("/usr/local/libexec/highambench"),
    ):
        _verify_secure_directory(parent)
    try:
        info = os.lstat(path)
    except OSError as error:
        raise FrontendError(f"cannot inspect internal host helper: {error}") from error
    if (
        stat.S_ISLNK(info.st_mode)
        or not stat.S_ISREG(info.st_mode)
        or info.st_uid != 0
        or info.st_gid != 0
        or stat.S_IMODE(info.st_mode) != 0o755
        or info.st_nlink != 1
    ):
        raise FrontendError(
            "internal host helper must be a root-owned mode-0755 regular file"
        )


def build_relay_command(arguments: Sequence[str]) -> list[str]:
    """Build one injection-safe host-systemd relay command."""

    unit = f"highambench-cpu-guard-host-{os.getpid()}-{secrets.token_hex(16)}"
    return [
        SYSTEMD_RUN,
        "--system",
        "--wait",
        "--pipe",
        "--collect",
        "--quiet",
        "--service-type=exec",
        f"--unit={unit}",
        "--working-directory=/",
        "--property=UMask=0077",
        "--setenv=PATH=/usr/sbin:/usr/bin:/sbin:/bin",
        "--setenv=LANG=C",
        "--setenv=LC_ALL=C",
        "--",
        str(HOST_HELPER),
        *arguments,
    ]


def main(argv: Sequence[str] | None = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    # Lock order is always installation-generation then campaign/slot locks
    # (the latter are acquired only by the host helper).  An installer holds
    # the exclusive form, so an old frontend/host/config generation can never
    # resume after new bytes have been committed.
    with _installation_generation_lock():
        config = _read_root_configuration()
        operator_uid = config["operator_uid"]
        assert isinstance(operator_uid, int) and not isinstance(operator_uid, bool)
        _authorize(operator_uid)
        _verify_host_helper()
        completed = subprocess.run(
            build_relay_command(arguments),
            env=SAFE_ENV,
            cwd="/",
            check=False,
        )
        return completed.returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FrontendError, OSError) as error:
        print(f"highambench CPU-guard frontend: {error}", file=sys.stderr)
        raise SystemExit(2)
