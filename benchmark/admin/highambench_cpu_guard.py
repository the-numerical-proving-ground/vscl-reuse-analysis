#!/usr/bin/python3 -I
"""Root-side CPU partition guard for VSCLReuse.

This file is deliberately standalone: an installed copy imports only Python's
standard library and uses fixed absolute paths for privileged executables.  It
has no operation that sends a signal or stops a unit.  A campaign acquires one
lease containing one or more disjoint CPU slots, launches measured jobs in
those slots in parallel, and releases the lease only after every slot is empty.
"""

from __future__ import annotations

import argparse
import contextlib
import dataclasses
import errno
import fcntl
import json
import os
import re
import secrets
import math
import stat
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable, Iterator, Mapping, Sequence


CONFIG_PATH = Path("/etc/highambench/cpu-guard.json")
CGROUP_ROOT = Path("/sys/fs/cgroup")
STATE_ROOT = Path("/run/highambench-cpu-guard")
STATE_PATH = STATE_ROOT / "state.json"
STATE_LOCK_PATH = STATE_ROOT / "state.lock"
LEASE_LOCK_PATH = STATE_ROOT / "campaign.lock"
INSTALL_LOCK_PATH = Path("/var/lib/highambench-cpu-guard/relay-install.lock")
SYSTEMCTL = "/usr/bin/systemctl"
SYSTEMD_RUN = "/usr/bin/systemd-run"
GUARD_SLICE = "highambench.slice"
CONTROLLER_PIN = "highambench-cpuset-pin"
STATE_SCHEMA = 2
EVIDENCE_SCHEMA = 1
STATE_PHASES = frozenset({"inactive", "preparing", "active", "releasing"})
LEASE_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,127}")
UNIT_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.@-]{0,180}")
SAFE_ENV = {
    "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
    "LANG": "C",
    "LC_ALL": "C",
}


class GuardError(RuntimeError):
    """A fail-closed validation or host-isolation error."""


def parse_cpu_list(raw: str) -> frozenset[int]:
    """Parse the Linux CPU-list syntax used by cpuset files."""

    if not isinstance(raw, str) or not raw.strip():
        raise GuardError("CPU list must not be empty")
    cpus: set[int] = set()
    for item in raw.strip().split(","):
        token = item.strip()
        if not token:
            raise GuardError(f"invalid CPU list: {raw!r}")
        if "-" in token:
            if token.count("-") != 1:
                raise GuardError(f"invalid CPU range: {token!r}")
            first_raw, last_raw = token.split("-", 1)
            if re.fullmatch(r"[0-9]+", first_raw) is None or re.fullmatch(r"[0-9]+", last_raw) is None:
                raise GuardError(f"invalid CPU range: {token!r}")
            first, last = int(first_raw), int(last_raw)
            if first > last:
                raise GuardError(f"descending CPU range: {token!r}")
            values = range(first, last + 1)
        else:
            if re.fullmatch(r"[0-9]+", token) is None:
                raise GuardError(f"invalid CPU number: {token!r}")
            values = (int(token),)
        for cpu in values:
            if cpu > 1_048_575:
                raise GuardError(f"CPU number is unreasonably large: {cpu}")
            if cpu in cpus:
                raise GuardError(f"CPU {cpu} occurs more than once")
            cpus.add(cpu)
    return frozenset(cpus)


def format_cpu_list(cpus: Sequence[int] | set[int] | frozenset[int]) -> str:
    """Return one canonical compact Linux CPU list."""

    ordered = sorted(set(cpus))
    if not ordered:
        raise GuardError("cannot format an empty CPU set")
    pieces: list[str] = []
    start = previous = ordered[0]
    for cpu in ordered[1:]:
        if cpu == previous + 1:
            previous = cpu
            continue
        pieces.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = cpu
    pieces.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(pieces)


def _parse_optional_cpu_list(raw: str) -> frozenset[int]:
    return frozenset() if not raw.strip() else parse_cpu_list(raw)


@dataclasses.dataclass(frozen=True)
class Configuration:
    operator_uid: int
    run_uid: int
    run_gid: int
    python_executable: Path
    resources_script: Path
    allowed_cpus: frozenset[int]
    physical_cores_per_slot: int
    maximum_slots: int
    idle_sample_seconds: float
    maximum_busy_percent: float

    @classmethod
    def from_mapping(cls, value: Mapping[str, object]) -> "Configuration":
        expected = {
            "schema_version",
            "operator_uid",
            "run_uid",
            "run_gid",
            "python_executable",
            "resources_script",
            "allowed_cpus",
            "physical_cores_per_slot",
            "maximum_slots",
            "idle_sample_seconds",
            "maximum_busy_percent",
        }
        if set(value) != expected:
            missing = sorted(expected - set(value))
            extra = sorted(set(value) - expected)
            raise GuardError(f"invalid configuration keys; missing={missing}, extra={extra}")
        if value.get("schema_version") != 1:
            raise GuardError("unsupported CPU-guard configuration schema")

        def integer(name: str, *, minimum: int, maximum: int) -> int:
            raw = value[name]
            if isinstance(raw, bool) or not isinstance(raw, int):
                raise GuardError(f"configuration {name} must be an integer")
            if not minimum <= raw <= maximum:
                raise GuardError(
                    f"configuration {name} must be between {minimum} and {maximum}"
                )
            return raw

        operator_uid = integer("operator_uid", minimum=1, maximum=2**31 - 1)
        run_uid = integer("run_uid", minimum=1, maximum=2**31 - 1)
        run_gid = integer("run_gid", minimum=1, maximum=2**31 - 1)
        cores = integer("physical_cores_per_slot", minimum=1, maximum=64)
        maximum_slots = integer("maximum_slots", minimum=1, maximum=64)
        executable_raw = value["python_executable"]
        resources_raw = value["resources_script"]
        if not isinstance(executable_raw, str) or not executable_raw.startswith("/"):
            raise GuardError("python_executable must be an absolute path")
        if not isinstance(resources_raw, str) or not resources_raw.startswith("/"):
            raise GuardError("resources_script must be an absolute path")
        executable = Path(executable_raw)
        resources = Path(resources_raw)
        if executable != Path(os.path.normpath(executable_raw)):
            raise GuardError("python_executable must be normalized")
        if resources != Path(os.path.normpath(resources_raw)):
            raise GuardError("resources_script must be normalized")
        allowed_raw = value["allowed_cpus"]
        if not isinstance(allowed_raw, str):
            raise GuardError("allowed_cpus must be a CPU-list string")
        seconds_raw = value["idle_sample_seconds"]
        busy_raw = value["maximum_busy_percent"]
        if isinstance(seconds_raw, bool) or not isinstance(seconds_raw, (int, float)):
            raise GuardError("idle_sample_seconds must be numeric")
        if isinstance(busy_raw, bool) or not isinstance(busy_raw, (int, float)):
            raise GuardError("maximum_busy_percent must be numeric")
        seconds, busy = float(seconds_raw), float(busy_raw)
        if not math.isfinite(seconds) or not 0.25 <= seconds <= 30.0:
            raise GuardError("idle_sample_seconds must be between 0.25 and 30")
        if not math.isfinite(busy) or not 0.0 <= busy <= 5.0:
            raise GuardError("maximum_busy_percent must be between 0 and 5")
        return cls(
            operator_uid=operator_uid,
            run_uid=run_uid,
            run_gid=run_gid,
            python_executable=executable,
            resources_script=resources,
            allowed_cpus=parse_cpu_list(allowed_raw),
            physical_cores_per_slot=cores,
            maximum_slots=maximum_slots,
            idle_sample_seconds=seconds,
            maximum_busy_percent=busy,
        )


def _secure_root_file(path: Path) -> None:
    parent = os.lstat(path.parent)
    if (
        stat.S_ISLNK(parent.st_mode)
        or not stat.S_ISDIR(parent.st_mode)
        or parent.st_uid != 0
        or parent.st_gid != 0
        or stat.S_IMODE(parent.st_mode) != 0o755
    ):
        raise GuardError(
            f"root configuration parent must be root-owned mode 0755: {path.parent}"
        )
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise GuardError(f"root configuration is not a regular non-symlink file: {path}")
    if (
        info.st_uid != 0
        or info.st_gid != 0
        or stat.S_IMODE(info.st_mode) != 0o600
        or info.st_nlink != 1
    ):
        raise GuardError(
            f"root configuration must be root-owned, singly linked mode 0600: {path}"
        )


def load_configuration(path: Path = CONFIG_PATH) -> Configuration:
    _secure_root_file(path)
    try:
        raw = path.read_bytes()
        if len(raw) > 65_536:
            raise GuardError("CPU-guard configuration is oversized")
        value = _strict_json_loads(raw.decode("utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise GuardError(f"cannot read CPU-guard configuration: {error}") from error
    if not isinstance(value, dict):
        raise GuardError("CPU-guard configuration must be a JSON object")
    config = Configuration.from_mapping(value)
    try:
        resolved_python = config.python_executable.resolve(strict=True)
    except OSError as error:
        raise GuardError(f"python_executable cannot be resolved: {error}") from error
    if not resolved_python.is_file() or not os.access(resolved_python, os.X_OK):
        raise GuardError("python_executable must resolve to an executable regular file")
    try:
        resolved_resources = config.resources_script.resolve(strict=True)
    except OSError as error:
        raise GuardError(f"resources_script cannot be resolved: {error}") from error
    if resolved_resources != config.resources_script or not resolved_resources.is_file():
        raise GuardError("resources_script must name a real file without symlinks")
    if not os.access(config.python_executable, os.X_OK):
        raise GuardError("configured python_executable is not executable")
    return config


def _strict_json_loads(raw: str) -> object:
    def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in items:
            if key in result:
                raise GuardError(f"duplicate JSON key: {key!r}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> object:
        raise GuardError(f"non-finite JSON number is forbidden: {value}")

    def finite_float(value: str) -> float:
        parsed = float(value)
        if not math.isfinite(parsed):
            raise GuardError(f"non-finite JSON number is forbidden: {value}")
        return parsed

    return json.loads(
        raw,
        object_pairs_hook=pairs,
        parse_constant=invalid_constant,
        parse_float=finite_float,
    )


def authorize(config: Configuration) -> None:
    if os.geteuid() != 0:
        raise GuardError("CPU guard must run as root through its restricted sudo rule")
    sudo_uid = os.environ.get("SUDO_UID")
    if sudo_uid is None:
        # Direct root operation is retained for recovery by the administrator.
        if os.getuid() != 0:
            raise GuardError("cannot identify the invoking operator")
        return
    if re.fullmatch(r"[0-9]+", sudo_uid) is None or int(sudo_uid) != config.operator_uid:
        raise GuardError("invoking sudo user is not the configured benchmark operator")


@contextlib.contextmanager
def installation_generation_lock(path: Path = INSTALL_LOCK_PATH) -> Iterator[None]:
    """Hold the shared install generation across every host-side operation."""

    try:
        parent = os.lstat(path.parent)
    except OSError as error:
        raise GuardError(f"cannot inspect installation lock parent: {error}") from error
    if (
        stat.S_ISLNK(parent.st_mode)
        or not stat.S_ISDIR(parent.st_mode)
        or parent.st_uid != 0
        or parent.st_gid != 0
        or stat.S_IMODE(parent.st_mode) != 0o700
    ):
        raise GuardError("installation lock parent must be root-owned mode 0700")
    try:
        descriptor = os.open(
            path,
            os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
    except OSError as error:
        raise GuardError(f"cannot open installation generation lock: {error}") from error
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != 0
            or info.st_gid != 0
            or stat.S_IMODE(info.st_mode) != 0o600
            or info.st_nlink != 1
        ):
            raise GuardError(
                "installation generation lock must be root-owned mode 0600"
            )
        fcntl.flock(descriptor, fcntl.LOCK_SH)
        yield
    finally:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)


def _initial_state() -> dict[str, object]:
    return {
        "schema_version": STATE_SCHEMA,
        "generation": 0,
        "phase": "inactive",
        "active_lease": None,
        "baseline": None,
        "applied": None,
    }


class StateStore:
    """Root-only, flock-serialized JSON state."""

    def __init__(
        self,
        root: Path = STATE_ROOT,
        state_path: Path = STATE_PATH,
        lock_path: Path = STATE_LOCK_PATH,
        lease_lock_path: Path = LEASE_LOCK_PATH,
    ) -> None:
        self.root = root
        self.state_path = state_path
        self.lock_path = lock_path
        self.lease_lock_path = lease_lock_path

    def slot_lock_path(self, slot_key: str) -> Path:
        if re.fullmatch(r"[0-9]+(?:-[0-9]+)*(?:,[0-9]+(?:-[0-9]+)*)*", slot_key) is None:
            raise GuardError("invalid canonical slot key")
        return self.root / f"slot-{slot_key.replace(',', '_')}.lock"

    def prepare(self) -> None:
        try:
            self.root.mkdir(mode=0o700)
        except FileExistsError:
            pass
        info = os.lstat(self.root)
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            raise GuardError(f"state root is not a real directory: {self.root}")
        if info.st_uid != 0 or stat.S_IMODE(info.st_mode) != 0o700:
            raise GuardError(f"state root must be root-owned mode 0700: {self.root}")

    @contextlib.contextmanager
    def state_lock(self) -> Iterator[dict[str, object]]:
        self.prepare()
        descriptor = os.open(
            self.lock_path,
            os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            state_value = self._load()
            yield state_value
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

    @contextlib.contextmanager
    def lease_lock(self, *, shared: bool) -> Iterator[int]:
        """Hold the campaign lock and expose its authenticated descriptor.

        Launch passes the shared-lock descriptor to ``systemd-run`` as stdin.
        Do not explicitly unlock here: ``flock`` is attached to the shared
        open-file description, so closing only this process's descriptor lets
        a queued/running launch retain the lock after an abrupt helper exit.
        The lock is released automatically when the final duplicate closes.
        """

        self.prepare()
        descriptor = os.open(
            self.lease_lock_path,
            os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        try:
            root_identity = os.lstat(self.root)
            lock_identity = os.fstat(descriptor)
            if (
                not stat.S_ISREG(lock_identity.st_mode)
                or lock_identity.st_uid != root_identity.st_uid
                or lock_identity.st_gid != root_identity.st_gid
                or stat.S_IMODE(lock_identity.st_mode) != 0o600
                or lock_identity.st_nlink != 1
            ):
                raise GuardError(
                    "campaign lock must be an owner-matched mode-0600 regular file"
                )
            fcntl.flock(descriptor, fcntl.LOCK_SH if shared else fcntl.LOCK_EX)
            yield descriptor
        finally:
            os.close(descriptor)

    @contextlib.contextmanager
    def slot_lock(self, slot_key: str) -> Iterator[None]:
        """Reject concurrent reuse of one slot without blocking other slots."""

        self.prepare()
        descriptor = os.open(
            self.slot_lock_path(slot_key),
            os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        try:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise GuardError(f"slot {slot_key} already has an active launch") from error
            yield
        finally:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
            os.close(descriptor)

    def _load(self) -> dict[str, object]:
        if not self.state_path.exists():
            return _initial_state()
        info = os.lstat(self.state_path)
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
            raise GuardError("state file is not a regular non-symlink file")
        if info.st_uid != 0 or info.st_mode & 0o077:
            raise GuardError("state file must be root-owned mode 0600")
        try:
            raw = self.state_path.read_bytes()
            if len(raw) > 1_048_576:
                raise GuardError("CPU-guard state is oversized")
            value = _strict_json_loads(raw.decode("utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            raise GuardError(f"cannot parse guard state: {error}") from error
        if not isinstance(value, dict):
            raise GuardError("invalid CPU-guard state schema")
        # Version 1 was only ever persisted as either fully inactive or fully
        # active.  Converting it in memory is safe: no partial-write phase could
        # have been represented, and the next mutation atomically writes v2.
        if value.get("schema_version") == 1:
            legacy_keys = {
                "schema_version",
                "generation",
                "active_lease",
                "baseline",
                "applied",
            }
            if set(value) != legacy_keys:
                raise GuardError("invalid legacy CPU-guard state schema")
            value = dict(value)
            value["schema_version"] = STATE_SCHEMA
            value["phase"] = (
                "inactive" if value.get("active_lease") is None else "active"
            )
        if value.get("schema_version") != STATE_SCHEMA:
            raise GuardError("invalid CPU-guard state schema")
        if set(value) != {
            "schema_version",
            "generation",
            "phase",
            "active_lease",
            "baseline",
            "applied",
        }:
            raise GuardError("CPU-guard state has unexpected or missing keys")
        generation = value.get("generation")
        if isinstance(generation, bool) or not isinstance(generation, int) or generation < 0:
            raise GuardError("CPU-guard state generation is invalid")
        phase = value.get("phase")
        if not isinstance(phase, str) or phase not in STATE_PHASES:
            raise GuardError("CPU-guard state phase is invalid")
        active, baseline, applied = (
            value.get("active_lease"),
            value.get("baseline"),
            value.get("applied"),
        )
        if phase == "inactive":
            if active is not None:
                raise GuardError("inactive CPU-guard state retains an active lease")
            if baseline is not None or applied is not None:
                raise GuardError("inactive CPU-guard state retains a partition transaction")
        elif not isinstance(active, dict) or not isinstance(baseline, dict) or not isinstance(applied, dict):
            raise GuardError("active CPU-guard state is incomplete")
        return value

    def save(self, value: Mapping[str, object]) -> None:
        self.prepare()
        temporary = self.root / f".state.{os.getpid()}.{secrets.token_hex(6)}"
        descriptor = -1
        try:
            descriptor = os.open(
                temporary,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
                0o600,
            )
            payload = (
                json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
            ).encode()
            offset = 0
            while offset < len(payload):
                offset += os.write(descriptor, payload[offset:])
            os.fsync(descriptor)
            os.close(descriptor)
            descriptor = -1
            os.replace(temporary, self.state_path)
            directory_fd = os.open(
                self.root, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
            )
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
        finally:
            if descriptor >= 0:
                os.close(descriptor)
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass


def _read_text_nofollow(path: Path) -> str:
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 65536)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks).decode("utf-8").strip()
    finally:
        os.close(descriptor)


def _write_text_nofollow(path: Path, value: str) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        encoded = (value + "\n").encode("ascii")
        written = os.write(descriptor, encoded)
        if written != len(encoded):
            raise GuardError(f"short write to {path}")
    finally:
        os.close(descriptor)


def _safe_run(
    command: Sequence[str],
    *,
    check: bool = True,
    capture_output: bool = True,
) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            list(command),
            check=False,
            text=True,
            capture_output=capture_output,
            cwd="/",
            env=SAFE_ENV,
        )
    except OSError as error:
        raise GuardError(f"cannot execute fixed privileged tool {command[0]}: {error}") from error
    if check and completed.returncode != 0:
        detail = (completed.stderr or completed.stdout or "no diagnostic").strip()
        raise GuardError(f"command {command[0]} failed ({completed.returncode}): {detail}")
    return completed


@dataclasses.dataclass(frozen=True)
class CpuTimes:
    busy: int
    idle: int

    @property
    def total(self) -> int:
        return self.busy + self.idle


def parse_proc_stat(raw: str) -> dict[int, CpuTimes]:
    """Parse counters without double-counting guest time."""

    result: dict[int, CpuTimes] = {}
    for line in raw.splitlines():
        fields = line.split()
        if not fields or re.fullmatch(r"cpu[0-9]+", fields[0]) is None:
            continue
        if len(fields) < 9:
            raise GuardError(f"short /proc/stat CPU row: {line!r}")
        try:
            counters = [int(item) for item in fields[1:11]]
        except ValueError as error:
            raise GuardError(f"non-integer /proc/stat CPU row: {line!r}") from error
        counters += [0] * (10 - len(counters))
        user, nice, system, idle, iowait, irq, softirq, steal, guest, guest_nice = counters[:10]
        adjusted_user, adjusted_nice = user - guest, nice - guest_nice
        if min(adjusted_user, adjusted_nice, system, idle, iowait, irq, softirq, steal) < 0:
            raise GuardError(f"invalid negative adjusted /proc/stat counter: {line!r}")
        cpu = int(fields[0][3:])
        result[cpu] = CpuTimes(
            busy=adjusted_user + adjusted_nice + system + irq + softirq + steal,
            idle=idle + iowait,
        )
    return result


def busy_percentages(
    before: Mapping[int, CpuTimes],
    after: Mapping[int, CpuTimes],
    cpus: frozenset[int],
) -> dict[int, float]:
    percentages: dict[int, float] = {}
    for cpu in sorted(cpus):
        if cpu not in before or cpu not in after:
            raise GuardError(f"CPU {cpu} is missing from a /proc/stat sample")
        busy_delta = after[cpu].busy - before[cpu].busy
        idle_delta = after[cpu].idle - before[cpu].idle
        total_delta = busy_delta + idle_delta
        if busy_delta < 0 or idle_delta < 0 or total_delta <= 0:
            raise GuardError(f"CPU {cpu} counters regressed or did not advance")
        percentages[cpu] = 100.0 * busy_delta / total_delta
    return percentages


@dataclasses.dataclass(frozen=True)
class Core:
    cpus: frozenset[int]
    signature: tuple[str, ...]


PF_KTHREAD = 0x00200000
# Linux UAPI ``PID_NS_INIT_INO``.  Unlike equality between two namespace
# handles, this distinguishes the initial (host) PID namespace from a private
# namespace that happens to contain its own PID-1 systemd.
INITIAL_PID_NAMESPACE_INODE = 0xEFFFFFFC


def proc_stat_is_kernel_thread(raw: str, tid: int) -> bool:
    """Parse field 9 of /proc/TID/stat without trusting the parenthesized comm."""

    prefix = f"{tid} ("
    closing = raw.rfind(")")
    if not raw.startswith(prefix) or closing < len(prefix):
        raise GuardError(f"malformed /proc stat record for TID {tid}")
    fields = raw[closing + 1 :].strip().split()
    if len(fields) < 7 or len(fields[0]) != 1:
        raise GuardError(f"short /proc stat record for TID {tid}")
    try:
        flags = int(fields[6], 10)
    except ValueError as error:
        raise GuardError(f"invalid /proc stat flags for TID {tid}") from error
    if flags < 0:
        raise GuardError(f"negative /proc stat flags for TID {tid}")
    return bool(flags & PF_KTHREAD)


class LinuxPlatform:
    """All Linux interaction, kept behind a replaceable test seam."""

    def __init__(
        self,
        *,
        cgroup_root: Path = CGROUP_ROOT,
        proc_root: Path = Path("/proc"),
        sys_cpu_root: Path = Path("/sys/devices/system/cpu"),
        sleeper: Callable[[float], None] = time.sleep,
    ) -> None:
        self.cgroup_root = cgroup_root
        self.proc_root = proc_root
        self.sys_cpu_root = sys_cpu_root
        self.sleeper = sleeper

    def assert_host_pid_namespace(self) -> None:
        """Prove this process can see host PID 1 and host cgroup members.

        The sudo frontend may itself run in a private PID namespace.  The
        privileged implementation is therefore executed by the host system
        manager, and this check fails before any state/cgroup mutation unless
        that relay actually entered the manager's PID namespace.
        """

        mountinfo = _read_text_nofollow(self.proc_root / "self/mountinfo")
        proc_mounts = []
        for line in mountinfo.splitlines():
            before, separator, after = line.partition(" - ")
            fields = before.split()
            filesystem = after.split()
            if (
                separator
                and len(fields) >= 5
                and fields[4] == str(self.proc_root)
                and filesystem
                and filesystem[0] == "proc"
            ):
                proc_mounts.append(line)
        if len(proc_mounts) != 1:
            raise GuardError(
                "host PID namespace attestation failed: /proc is not an exact procfs mount"
            )
        comm = _read_text_nofollow(self.proc_root / "1/comm")
        if comm != "systemd":
            raise GuardError(
                "host PID namespace attestation failed: PID 1 is not systemd"
            )
        status = _read_text_nofollow(self.proc_root / "1/status")
        nspid_lines = [line for line in status.splitlines() if line.startswith("NSpid:")]
        uid_lines = [line for line in status.splitlines() if line.startswith("Uid:")]
        if uid_lines != ["Uid:\t0\t0\t0\t0"]:
            raise GuardError(
                "host PID namespace attestation failed: PID 1 is not root-owned"
            )
        if len(nspid_lines) != 1 or nspid_lines[0].split()[1:] != ["1"]:
            raise GuardError(
                "host PID namespace attestation failed: PID 1 is namespace-translated"
            )
        try:
            pid_one_path = self.proc_root / "1/ns/pid"
            self_path = self.proc_root / "self/ns/pid"
            pid_one_namespace = os.readlink(pid_one_path)
            self_namespace = os.readlink(self_path)
            pid_one_inode = os.stat(pid_one_path).st_ino
            self_inode = os.stat(self_path).st_ino
        except OSError as error:
            raise GuardError(
                f"host PID namespace attestation cannot read namespace links: {error}"
            ) from error
        if (
            pid_one_namespace != self_namespace
            or pid_one_namespace != f"pid:[{INITIAL_PID_NAMESPACE_INODE}]"
            or pid_one_inode != INITIAL_PID_NAMESPACE_INODE
            or self_inode != INITIAL_PID_NAMESPACE_INODE
        ):
            raise GuardError(
                "host PID namespace attestation failed: helper and PID 1 differ"
            )
        manager_state = _safe_run(
            [SYSTEMCTL, "show", "--property=ActiveState", "--value", "--", "init.scope"]
        ).stdout.strip()
        manager_cgroup = _safe_run(
            [
                SYSTEMCTL,
                "show",
                "--property=ControlGroup",
                "--value",
                "--",
                "init.scope",
            ]
        ).stdout.strip()
        if manager_state != "active" or manager_cgroup != "/init.scope":
            raise GuardError(
                "host PID namespace attestation failed: system manager identity changed"
            )
        cgroup_lines = _read_text_nofollow(self.proc_root / "1/cgroup").splitlines()
        if cgroup_lines != ["0::/init.scope"]:
            raise GuardError(
                "host PID namespace attestation failed: PID 1 cgroup is unexpected"
            )
        manager_members = _read_text_nofollow(
            self.cgroup_root / "init.scope/cgroup.procs"
        ).splitlines()
        root_members = _read_text_nofollow(self.cgroup_root / "cgroup.procs").splitlines()
        if "1" not in manager_members or any(
            re.fullmatch(r"[1-9][0-9]*", item) is None
            for item in [*manager_members, *root_members]
        ):
            raise GuardError(
                "host PID namespace attestation failed: cgroup PIDs are hidden"
            )

    @property
    def guard_path(self) -> Path:
        return self.cgroup_root / GUARD_SLICE

    def slot_unit(self, index: int) -> str:
        return f"highambench-slot{index}.slice"

    def slot_path(self, index: int) -> Path:
        return self.guard_path / self.slot_unit(index)

    def controller_pin_path(self, index: int) -> Path:
        return self.slot_path(index) / CONTROLLER_PIN

    def controller_pin_identity(self, index: int) -> dict[str, object]:
        pin = self.controller_pin_path(index)
        try:
            info = pin.lstat()
        except OSError as error:
            raise GuardError(
                f"cannot inspect {self.slot_unit(index)} controller pin: {error}"
            ) from error
        mode = stat.S_IMODE(info.st_mode)
        if (
            pin.is_symlink()
            or not stat.S_ISDIR(info.st_mode)
            or info.st_uid != 0
            or info.st_gid != 0
            or mode != 0o755
            or self.cgroup_type(pin) != "domain"
        ):
            raise GuardError(
                f"{self.slot_unit(index)} controller pin must be a root-owned "
                "mode-0755 domain cgroup"
            )
        return {
            "device": info.st_dev,
            "inode": info.st_ino,
            "mode": mode,
            "type": "domain",
        }

    def _verify_empty_controller_pin(
        self, index: int, *, require_cpuset: bool
    ) -> dict[str, object]:
        identity = self.controller_pin_identity(index)
        pin = self.controller_pin_path(index)
        if (
            (require_cpuset and "cpuset" not in self.subtree_controllers(pin))
            or self.direct_processes(pin)
            or self.children(pin)
            or self.populated(pin)
        ):
            raise GuardError(
                f"{self.slot_unit(index)} controller pin is not empty and stable"
            )
        return identity

    def _preflight_static_hierarchy(self, maximum_slots: int) -> None:
        expected_slots = {self.slot_unit(index) for index in range(maximum_slots)}
        actual_slots = {path.name for path in self.children(self.guard_path)}
        if actual_slots != expected_slots:
            raise GuardError(
                "VSCLReuse slice has unexpected or missing child cgroups before "
                f"controller setup: expected={sorted(expected_slots)}, "
                f"actual={sorted(actual_slots)}"
            )
        if self.direct_processes(self.guard_path):
            raise GuardError("VSCLReuse parent contains direct processes")
        for index in range(maximum_slots):
            self.verify_slot_unit(index)
            slot = self.slot_path(index)
            if self.direct_processes(slot):
                raise GuardError(f"{self.slot_unit(index)} contains direct processes")
            children = self.children(slot)
            if children and {path.name for path in children} != {CONTROLLER_PIN}:
                raise GuardError(
                    f"{self.slot_unit(index)} contains an unexpected child cgroup"
                )
            if children:
                self._verify_empty_controller_pin(index, require_cpuset=False)
            if self.populated(slot):
                raise GuardError(f"{self.slot_unit(index)} is populated")
        if self.populated(self.guard_path):
            raise GuardError("VSCLReuse parent hierarchy is populated")

    def prepare_slices(self, maximum_slots: int) -> None:
        controllers = _read_text_nofollow(self.cgroup_root / "cgroup.controllers").split()
        delegated = _read_text_nofollow(self.cgroup_root / "cgroup.subtree_control").split()
        if "cpuset" not in controllers or "cpuset" not in delegated:
            raise GuardError("the unified root cgroup must expose and enable cpuset")
        _safe_run([SYSTEMCTL, "start", "--", GUARD_SLICE])
        if not self.guard_path.is_dir():
            raise GuardError("systemd did not create the VSCLReuse slice cgroup")
        units = [self.slot_unit(index) for index in range(maximum_slots)]
        _safe_run([SYSTEMCTL, "start", "--", *units])
        # Prove the predictable hierarchy is empty before the first controller
        # write.  Never adopt or mutate a populated/nested pre-existing pin.
        self._preflight_static_hierarchy(maximum_slots)
        self.verify_guard_unit()
        _write_text_nofollow(self.guard_path / "cgroup.subtree_control", "+cpuset")
        for index in range(maximum_slots):
            if not self.slot_path(index).is_dir():
                raise GuardError(f"systemd did not create {self.slot_unit(index)}")
            # Enable cpuset below the already-realized dedicated slice before
            # any transient service is created.  systemd-run then need not
            # mutate/re-realize the slot's own cpuset mask to delegate cpuset
            # files to the measured service.
            _write_text_nofollow(
                self.slot_path(index) / "cgroup.subtree_control", "+cpuset"
            )
            if "cpuset" not in self.subtree_controllers(self.slot_path(index)):
                raise GuardError(
                    f"{self.slot_unit(index)} did not enable cpuset delegation"
                )
            pin = self.controller_pin_path(index)
            try:
                pin.mkdir(mode=0o755)
                os.chmod(pin, 0o755, follow_symlinks=False)
            except FileExistsError:
                pass
            # Revalidate an object that may have appeared between preflight and
            # mkdir before writing through it.
            self._verify_empty_controller_pin(index, require_cpuset=False)
            _write_text_nofollow(pin / "cgroup.subtree_control", "+cpuset")
            self._verify_empty_controller_pin(index, require_cpuset=True)
        self._preflight_static_hierarchy(maximum_slots)
        if "cpuset" not in self.subtree_controllers(self.guard_path):
            raise GuardError("VSCLReuse parent did not retain cpuset")
        for index in range(maximum_slots):
            if "cpuset" not in self.subtree_controllers(self.slot_path(index)):
                raise GuardError(f"{self.slot_unit(index)} did not retain cpuset")
            self._verify_empty_controller_pin(index, require_cpuset=True)

    def subtree_controllers(self, cgroup: Path) -> frozenset[str]:
        return frozenset(
            _read_text_nofollow(cgroup / "cgroup.subtree_control").split()
        )

    def _verify_slice_unit(self, unit: str, expected: str) -> None:
        active = _safe_run(
            [SYSTEMCTL, "show", "--property=ActiveState", "--value", "--", unit]
        ).stdout.strip()
        control_group = _safe_run(
            [SYSTEMCTL, "show", "--property=ControlGroup", "--value", "--", unit]
        ).stdout.strip()
        if (
            active != "active"
            or control_group != expected
            or self.unit_startup_allowed_cpus(unit)
            or self.unit_startup_allowed_memory_nodes(unit)
        ):
            raise GuardError(
                f"systemd slice unit identity is not stable: {unit} "
                f"state={active!r} cgroup={control_group!r}"
            )

    def verify_guard_unit(self) -> None:
        self._verify_slice_unit(GUARD_SLICE, f"/{GUARD_SLICE}")

    def verify_slot_unit(self, index: int) -> None:
        unit = self.slot_unit(index)
        self._verify_slice_unit(unit, f"/{GUARD_SLICE}/{unit}")

    def _unit_cpu_property(self, unit: str, property_name: str) -> str:
        if property_name not in {"AllowedCPUs", "StartupAllowedCPUs"}:
            raise GuardError("refusing an unsupported systemd CPU property")
        raw = _safe_run(
            [SYSTEMCTL, "show", f"--property={property_name}", "--value", "--", unit]
        ).stdout.strip()
        if not raw:
            return ""
        # systemctl formats CPU sets as whitespace-separated ranges, while the
        # cgroup and evidence contract uses the canonical comma-separated form.
        normalized = ",".join(raw.split())
        cpus = parse_cpu_list(normalized)
        return format_cpu_list(cpus)

    def unit_allowed_cpus(self, unit: str) -> str:
        return self._unit_cpu_property(unit, "AllowedCPUs")

    def unit_startup_allowed_cpus(self, unit: str) -> str:
        return self._unit_cpu_property(unit, "StartupAllowedCPUs")

    def set_unit_allowed_cpus(self, unit: str, cpus: str) -> None:
        if cpus:
            parsed = parse_cpu_list(cpus)
            if format_cpu_list(parsed) != cpus:
                raise GuardError("refusing a non-canonical systemd AllowedCPUs value")
        _safe_run(
            [
                SYSTEMCTL,
                "set-property",
                "--runtime",
                "--",
                unit,
                f"AllowedCPUs={cpus}",
            ]
        )
        if self.unit_allowed_cpus(unit) != cpus:
            raise GuardError(f"systemd did not retain AllowedCPUs for {unit}")

    def _unit_memory_property(self, unit: str, property_name: str) -> str:
        if property_name not in {"AllowedMemoryNodes", "StartupAllowedMemoryNodes"}:
            raise GuardError("refusing an unsupported systemd memory-node property")
        raw = _safe_run(
            [SYSTEMCTL, "show", f"--property={property_name}", "--value", "--", unit]
        ).stdout.strip()
        if not raw:
            return ""
        normalized = ",".join(raw.split())
        nodes = parse_cpu_list(normalized)
        return format_cpu_list(nodes)

    def unit_allowed_memory_nodes(self, unit: str) -> str:
        return self._unit_memory_property(unit, "AllowedMemoryNodes")

    def unit_startup_allowed_memory_nodes(self, unit: str) -> str:
        return self._unit_memory_property(unit, "StartupAllowedMemoryNodes")

    def cgroup_type(self, cgroup: Path) -> str:
        return _read_text_nofollow(cgroup / "cgroup.type")

    def verify_slot_boundary(
        self,
        index: int,
        cpus: frozenset[int],
        campaign_cpus: frozenset[int],
        controller_pin: Mapping[str, object],
        guard_effective_mems: frozenset[int],
        slot_effective_mems: frozenset[int],
        *,
        expected_service: Path | None,
    ) -> None:
        self.verify_guard_unit()
        self.verify_slot_unit(index)
        slot = self.slot_path(index)
        expected_raw = format_cpu_list(cpus)
        if (
            self.partition(self.guard_path) != "root"
            or self.cpus(self.guard_path) != format_cpu_list(campaign_cpus)
            or self.effective_cpus(self.guard_path)
            or self.partition(slot) != "root"
            or self.cpus(slot) != expected_raw
            or self.effective_cpus(slot) != cpus
            or self.unit_allowed_cpus(GUARD_SLICE)
            != format_cpu_list(campaign_cpus)
            or self.unit_allowed_cpus(self.slot_unit(index)) != expected_raw
            or self.mems(self.guard_path) != ""
            or self.unit_allowed_memory_nodes(GUARD_SLICE) != ""
            or self.effective_mems(self.guard_path) != guard_effective_mems
            or self.mems(slot) != ""
            or self.unit_allowed_memory_nodes(self.slot_unit(index)) != ""
            or self.effective_mems(slot) != slot_effective_mems
            or "cpuset" not in self.subtree_controllers(self.guard_path)
            or "cpuset" not in self.subtree_controllers(slot)
        ):
            raise GuardError("systemd slot boundary changed during launch")
        pin = self.controller_pin_path(index)
        if (
            self.controller_pin_identity(index) != dict(controller_pin)
            or self._verify_empty_controller_pin(index, require_cpuset=True)
            != dict(controller_pin)
        ):
            raise GuardError("root-owned cpuset controller pin changed during launch")
        expected_children = {pin.name}
        if expected_service is not None:
            if expected_service.parent != slot:
                raise GuardError("measured service cgroup escaped its exact slot")
            expected_children.add(expected_service.name)
        if (
            {path.name for path in self.children(slot)} != expected_children
            or self.direct_processes(slot)
        ):
            raise GuardError("systemd slot hierarchy changed during launch")

    def root_effective_cpus(self) -> frozenset[int]:
        return parse_cpu_list(_read_text_nofollow(self.cgroup_root / "cpuset.cpus.effective"))

    def online_cpus(self) -> frozenset[int]:
        return parse_cpu_list(_read_text_nofollow(self.sys_cpu_root / "online"))

    def root_siblings(self) -> list[Path]:
        siblings: list[Path] = []
        for entry in os.scandir(self.cgroup_root):
            if entry.name == GUARD_SLICE:
                continue
            if entry.is_symlink():
                raise GuardError(f"unexpected symlink below cgroup root: {entry.path}")
            if entry.is_dir(follow_symlinks=False):
                siblings.append(Path(entry.path))
        return sorted(siblings, key=lambda path: path.name)

    def cpus(self, cgroup: Path) -> str:
        return _read_text_nofollow(cgroup / "cpuset.cpus")

    def mems(self, cgroup: Path) -> str:
        return _read_text_nofollow(cgroup / "cpuset.mems")

    def effective_cpus(self, cgroup: Path) -> frozenset[int]:
        # A valid, empty parent partition may distribute its complete CPU
        # allotment to child partition roots.  Leaf slots are still required
        # to compare equal to their non-empty lease masks, but the shared
        # reader must preserve this kernel-defined empty state.
        return _parse_optional_cpu_list(
            _read_text_nofollow(cgroup / "cpuset.cpus.effective")
        )

    def effective_mems(self, cgroup: Path) -> frozenset[int]:
        return _parse_optional_cpu_list(
            _read_text_nofollow(cgroup / "cpuset.mems.effective")
        )

    def set_cpus(self, cgroup: Path, cpus: str) -> None:
        _write_text_nofollow(cgroup / "cpuset.cpus", cpus)

    def partition(self, cgroup: Path) -> str:
        return _read_text_nofollow(cgroup / "cpuset.cpus.partition")

    def set_partition(self, cgroup: Path, value: str) -> None:
        if value not in {"member", "root"}:
            raise GuardError(f"refusing unsupported partition state {value!r}")
        _write_text_nofollow(cgroup / "cpuset.cpus.partition", value)
        observed = self.partition(cgroup)
        if observed != value:
            raise GuardError(
                f"partition write did not become valid: wanted {value}, observed {observed}"
            )

    def direct_processes(self, cgroup: Path) -> list[int]:
        raw = _read_text_nofollow(cgroup / "cgroup.procs")
        return [] if not raw else [int(item) for item in raw.splitlines()]

    def children(self, cgroup: Path) -> list[Path]:
        result: list[Path] = []
        for entry in os.scandir(cgroup):
            if entry.is_symlink():
                raise GuardError(f"unexpected symlink in managed cgroup: {entry.path}")
            if entry.is_dir(follow_symlinks=False):
                result.append(Path(entry.path))
        return sorted(result, key=lambda path: path.name)

    def populated(self, cgroup: Path) -> bool:
        fields = {}
        for line in _read_text_nofollow(cgroup / "cgroup.events").splitlines():
            name, separator, value = line.partition(" ")
            if separator:
                fields[name] = value.strip()
        if fields.get("populated") not in {"0", "1"}:
            raise GuardError(f"invalid cgroup.events in {cgroup}")
        return fields["populated"] == "1"

    def cores(self, cpus: frozenset[int]) -> dict[frozenset[int], Core]:
        result: dict[frozenset[int], Core] = {}
        for cpu in sorted(cpus):
            topology = self.sys_cpu_root / f"cpu{cpu}" / "topology"
            siblings = parse_cpu_list(_read_text_nofollow(topology / "thread_siblings_list"))
            signature_parts = [str(len(siblings))]
            for relative in (
                "core_type",
                "../cpu_capacity",
                "../cpufreq/cpuinfo_min_freq",
                "../cpufreq/cpuinfo_max_freq",
                "../cpufreq/base_frequency",
            ):
                path = topology / relative
                try:
                    signature_parts.append(_read_text_nofollow(path))
                except FileNotFoundError:
                    signature_parts.append("-")
            core = Core(cpus=siblings, signature=tuple(signature_parts))
            prior = result.get(siblings)
            if prior is not None and prior != core:
                raise GuardError(f"inconsistent topology for CPUs {format_cpu_list(siblings)}")
            result[siblings] = core
        return result

    def sample_busy(self, cpus: frozenset[int], seconds: float) -> dict[int, float]:
        before = parse_proc_stat(_read_text_nofollow(self.proc_root / "stat"))
        self.sleeper(seconds)
        after = parse_proc_stat(_read_text_nofollow(self.proc_root / "stat"))
        return busy_percentages(before, after, cpus)

    def pinned_threads(
        self, reserved: frozenset[int], available: frozenset[int]
    ) -> list[dict[str, object]]:
        if not available or not reserved <= available:
            raise GuardError("pinned-thread scan received an invalid CPU availability snapshot")
        blocked: list[dict[str, object]] = []
        own_pid, own_tid = os.getpid(), getattr(os, "gettid", lambda: -1)()
        with os.scandir(self.proc_root) as processes:
            for process in processes:
                if (
                    re.fullmatch(r"[0-9]+", process.name) is None
                    or not process.is_dir(follow_symlinks=False)
                ):
                    continue
                task_root = Path(process.path) / "task"
                try:
                    with os.scandir(task_root) as task_entries:
                        tasks = list(task_entries)
                except OSError as error:
                    if error.errno in {errno.ENOENT, errno.ESRCH}:
                        continue
                    raise GuardError(
                        f"cannot inspect process task directory {task_root}: {error}"
                    ) from error
                for task in tasks:
                    if re.fullmatch(r"[0-9]+", task.name) is None:
                        continue
                    pid, tid = int(process.name), int(task.name)
                    if pid == own_pid and tid == own_tid:
                        continue
                    try:
                        raw = _read_text_nofollow(Path(task.path) / "status")
                    except OSError as error:
                        if error.errno in {errno.ENOENT, errno.ESRCH}:
                            continue
                        raise GuardError(
                            f"cannot inspect status for TID {tid}: {error}"
                        ) from error
                    values: dict[str, str] = {}
                    for line in raw.splitlines():
                        key, separator, value = line.partition(":")
                        if separator:
                            values[key] = value.strip()
                    if values.get("State", "").startswith("Z"):
                        continue
                    allowed_raw = values.get("Cpus_allowed_list")
                    if not allowed_raw:
                        continue
                    allowed = parse_cpu_list(allowed_raw)
                    eligible = allowed & available
                    if not eligible:
                        raise GuardError(
                            f"TID {tid} has no runnable CPU in the stable host snapshot"
                        )
                    if eligible <= reserved:
                        try:
                            stat_raw = _read_text_nofollow(Path(task.path) / "stat")
                        except OSError as error:
                            if error.errno in {errno.ENOENT, errno.ESRCH}:
                                continue
                            raise GuardError(
                                f"cannot inspect stat flags for TID {tid}: {error}"
                            ) from error
                        if proc_stat_is_kernel_thread(stat_raw, tid):
                            continue
                        uid_field = values.get("Uid", "?").split()[0]
                        blocked.append(
                            {
                                "pid": pid,
                                "tid": tid,
                                "uid": uid_field,
                                "name": values.get("Name", "?"),
                                "allowed_cpus": format_cpu_list(allowed),
                                "eligible_cpus": format_cpu_list(eligible),
                            }
                        )
        return blocked

    def pin_self(self, cpus: frozenset[int]) -> None:
        try:
            os.sched_setaffinity(0, cpus)
        except OSError as error:
            raise GuardError(f"cannot move the guard itself off requested CPUs: {error}") from error

    def verify_launch_cgroup(
        self, unit: str, slot_index: int, cpus: frozenset[int]
    ) -> Path:
        completed = _safe_run(
            [SYSTEMCTL, "show", "--property=ControlGroup", "--value", "--", unit]
        )
        control_group = completed.stdout.strip()
        service_unit = unit if unit.endswith(".service") else f"{unit}.service"
        expected_control_group = (
            f"/{GUARD_SLICE}/{self.slot_unit(slot_index)}/{service_unit}"
        )
        if control_group != expected_control_group:
            raise GuardError(
                f"measured unit escaped its system CPU slice: {control_group!r}"
            )
        relative = expected_control_group.removeprefix("/")
        cgroup = self.cgroup_root / relative
        observed = parse_cpu_list(_read_text_nofollow(cgroup / "cpuset.cpus.effective"))
        if observed != cpus:
            raise GuardError(
                f"measured unit effective CPUs are {format_cpu_list(observed)}, "
                f"expected {format_cpu_list(cpus)}"
            )
        return cgroup

    def wait_for_launch_cgroup_gone(
        self, cgroup: Path, *, timeout_seconds: float = 5.0
    ) -> None:
        """Wait read-only for systemd's collected service cgroup to vanish."""

        deadline = time.monotonic() + timeout_seconds
        while True:
            try:
                metadata = cgroup.lstat()
            except FileNotFoundError:
                return
            except OSError as error:
                raise GuardError(
                    f"cannot attest measured service cgroup collection: {error}"
                ) from error
            if cgroup.is_symlink() or not stat.S_ISDIR(metadata.st_mode):
                raise GuardError("measured service cgroup path changed type")
            if time.monotonic() >= deadline:
                populated = self.populated(cgroup)
                state = "populated" if populated else "present but empty"
                raise GuardError(
                    "measured service cgroup was not collected after systemd-run "
                    f"({state}): {cgroup}"
                )
            time.sleep(0.02)

    def launch(
        self,
        config: Configuration,
        *,
        unit: str,
        slot_index: int,
        cpus: frozenset[int],
        campaign_cpus: frozenset[int],
        working_directory: Path,
        proof_file: Path,
        command: Sequence[str],
        controller_pin: Mapping[str, object],
        guard_effective_mems: frozenset[int],
        slot_effective_mems: frozenset[int],
        lifetime_lock_fd: int,
    ) -> int:
        if not command or not os.path.isabs(command[0]):
            raise GuardError("measured command executable must be an absolute path")
        if (
            not isinstance(lifetime_lock_fd, int)
            or isinstance(lifetime_lock_fd, bool)
            or lifetime_lock_fd < 0
        ):
            raise GuardError("campaign lifetime lock descriptor is invalid")
        try:
            lock_identity = os.fstat(lifetime_lock_fd)
        except OSError as error:
            raise GuardError(
                f"cannot inspect campaign lifetime lock descriptor: {error}"
            ) from error
        if not stat.S_ISREG(lock_identity.st_mode):
            raise GuardError("campaign lifetime lock descriptor is not a regular file")
        systemd_cpus = format_cpu_list(cpus).replace(",", " ")
        verified_command = [
            str(config.python_executable),
            str(config.resources_script),
            "_verify-and-exec",
            "--expected-cpus",
            format_cpu_list(cpus),
            "--proof-file",
            str(proof_file),
            "--",
            *command,
        ]
        argv = [
            SYSTEMD_RUN,
            "--system",
            "--wait",
            "--pipe",
            "--collect",
            "--service-type=exec",
            f"--unit={unit}",
            f"--slice={self.slot_unit(slot_index)}",
            f"--uid={config.run_uid}",
            f"--gid={config.run_gid}",
            f"--working-directory={working_directory}",
            "--setenv=PATH=/usr/bin:/bin",
            "--setenv=LANG=C",
            "--setenv=LC_ALL=C",
            "--setenv=HIGHAMBENCH_LIFETIME_LOCK_STDIN=1",
            "--property=SupplementaryGroups=",
            "--property=NoNewPrivileges=yes",
            "--property=CapabilityBoundingSet=",
            "--property=AmbientCapabilities=",
            "--property=UMask=0077",
            "--property=Delegate=memory",
            "--property=MemoryAccounting=yes",
            "--property=MemoryMax=infinity",
            "--property=MemoryHigh=infinity",
            "--property=MemorySwapMax=0",
            "--property=CPUAccounting=yes",
            f"--property=CPUAffinity={systemd_cpus}",
            "--property=KillMode=control-group",
            "--property=OOMPolicy=kill",
            "--property=SystemCallArchitectures=native",
            "--property=SystemCallFilter=~sched_setaffinity",
            "--property=SystemCallErrorNumber=EPERM",
            "--",
            *verified_command,
        ]
        try:
            # ``--pipe`` transfers fd 0 through StartTransientUnit.  The
            # descriptor carries the shared campaign flock into systemd-run,
            # the manager's queued request, and the service.  Thus an abrupt
            # helper death cannot let release overtake a late service start.
            process = subprocess.Popen(
                argv,
                cwd="/",
                env=SAFE_ENV,
                stdin=lifetime_lock_fd,
            )
        except OSError as error:
            raise GuardError(f"cannot execute fixed systemd-run: {error}") from error
        verification_error: GuardError | None = None
        launched_cgroup: Path | None = None
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            try:
                launched_cgroup = self.verify_launch_cgroup(
                    unit, slot_index, cpus
                )
                self.verify_slot_boundary(
                    slot_index,
                    cpus,
                    campaign_cpus,
                    controller_pin,
                    guard_effective_mems,
                    slot_effective_mems,
                    expected_service=launched_cgroup,
                )
                verification_error = None
                break
            except GuardError as error:
                verification_error = error
                if process.poll() is not None:
                    break
                time.sleep(0.02)
        else:
            verification_error = GuardError("timed out verifying measured unit cgroup")
        return_code = process.wait()
        if verification_error is not None:
            raise verification_error
        if launched_cgroup is None:
            raise GuardError("measured service cgroup was never authenticated")
        self.wait_for_launch_cgroup_gone(launched_cgroup)
        self.verify_slot_boundary(
            slot_index,
            cpus,
            campaign_cpus,
            controller_pin,
            guard_effective_mems,
            slot_effective_mems,
            expected_service=None,
        )
        return return_code


def _validate_lease_id(lease_id: str) -> str:
    if LEASE_RE.fullmatch(lease_id) is None:
        raise GuardError(
            "lease ID must match the fixed VSCLReuse ASCII identifier grammar"
        )
    return lease_id


def _slot_payload(
    slot_id: int,
    physical_slot: int,
    cpus: frozenset[int],
    cores: Sequence[Core],
) -> dict[str, object]:
    return {
        "slot_id": slot_id,
        "physical_slot": physical_slot,
        "cpus": format_cpu_list(cpus),
        "physical_cores": [format_cpu_list(core.cpus) for core in sorted(cores, key=lambda c: min(c.cpus))],
    }


def _validate_unit_name(unit: str) -> str:
    if UNIT_RE.fullmatch(unit) is None or not unit.startswith("highambench-"):
        raise GuardError("measured unit name does not match the fixed safe grammar")
    forbidden_suffixes = (
        ".automount",
        ".device",
        ".mount",
        ".path",
        ".scope",
        ".slice",
        ".socket",
        ".swap",
        ".target",
        ".timer",
    )
    if unit.endswith(forbidden_suffixes):
        raise GuardError("measured unit must be a transient service, not another unit type")
    return unit


def _real_directory(path: Path, *, label: str) -> Path:
    if not path.is_absolute() or path != Path(os.path.normpath(path)):
        raise GuardError(f"{label} must be an absolute normalized path")
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise GuardError(f"cannot resolve {label}: {error}") from error
    if resolved != path or not resolved.is_dir():
        raise GuardError(f"{label} must be a real directory without symlinks")
    return resolved


def _fresh_user_output(path: Path, config: Configuration, *, label: str) -> Path:
    if not path.is_absolute() or path != Path(os.path.normpath(path)):
        raise GuardError(f"{label} must be an absolute normalized path")
    _check_no_symlink_components(path)
    if path.exists() or path.is_symlink():
        raise GuardError(f"{label} must be a fresh path")
    parent = path.parent
    info = os.lstat(parent)
    if (
        not stat.S_ISDIR(info.st_mode)
        or stat.S_ISLNK(info.st_mode)
        or info.st_uid != config.operator_uid
        or stat.S_IMODE(info.st_mode) != 0o700
    ):
        raise GuardError(f"{label} parent must be operator-owned with exact mode 0700")
    return path


class CpuGuard:
    def __init__(
        self,
        config: Configuration,
        *,
        platform: LinuxPlatform | None = None,
        store: StateStore | None = None,
    ) -> None:
        self.config = config
        self.platform = platform or LinuxPlatform()
        self.store = store or StateStore()

    def _controller_pin_identity(self, index: int) -> dict[str, object]:
        pin = self.platform.controller_pin_path(index)
        identity = self.platform.controller_pin_identity(index)
        if (
            "cpuset" not in self.platform.subtree_controllers(pin)
            or self.platform.direct_processes(pin)
            or self.platform.children(pin)
            or self.platform.populated(pin)
        ):
            raise GuardError(
                f"VSCLReuse slot {index} controller pin is not empty and stable"
            )
        return identity

    def _pin_relay_to_host_complement(self, applied: Mapping[str, object]) -> None:
        host_raw = applied.get("host_cpus")
        if not isinstance(host_raw, str):
            raise GuardError("stored host CPU complement is malformed")
        self.platform.pin_self(parse_cpu_list(host_raw))

    def _memory_state_matches(
        self, cgroup: Path, unit: str, prior: Mapping[str, object]
    ) -> bool:
        effective_raw = prior.get("effective_mems")
        if not isinstance(effective_raw, str):
            return False
        try:
            expected_effective = parse_cpu_list(effective_raw)
        except GuardError:
            return False
        return (
            self.platform.mems(cgroup) == prior.get("mems") == ""
            and self.platform.unit_allowed_memory_nodes(unit)
            == prior.get("systemd_allowed_memory_nodes")
            == ""
            and self.platform.effective_mems(cgroup) == expected_effective
        )

    def _assert_empty_managed_hierarchy(self) -> None:
        expected_slots = {
            self.platform.slot_path(index).name for index in range(self.config.maximum_slots)
        }
        actual_slots = {path.name for path in self.platform.children(self.platform.guard_path)}
        if actual_slots != expected_slots:
            raise GuardError(
                "VSCLReuse slice has unexpected or missing child cgroups: "
                f"expected={sorted(expected_slots)}, actual={sorted(actual_slots)}"
            )
        if self.platform.direct_processes(self.platform.guard_path):
            raise GuardError("VSCLReuse parent slice contains direct processes")
        for index in range(self.config.maximum_slots):
            cgroup = self.platform.slot_path(index)
            if self.platform.direct_processes(cgroup):
                raise GuardError(f"VSCLReuse slot {index} contains direct processes")
            children = {path.name for path in self.platform.children(cgroup)}
            if children != {CONTROLLER_PIN} or self.platform.populated(cgroup):
                raise GuardError(
                    f"VSCLReuse slot {index} is not empty before acquisition"
                )
            self._controller_pin_identity(index)
        if self.platform.populated(self.platform.guard_path):
            raise GuardError("VSCLReuse parent hierarchy is populated before acquisition")

    def _validated_slots(
        self, raw_slots: Sequence[str]
    ) -> tuple[
        list[str],
        list[dict[str, object]],
        dict[int, frozenset[int]],
        frozenset[int],
    ]:
        if not raw_slots:
            raise GuardError("acquire requires at least one repeated --slot CPU list")
        if len(raw_slots) > self.config.maximum_slots:
            raise GuardError("requested slot count exceeds the installed maximum")
        effective = self.platform.root_effective_cpus()
        online = self.platform.online_cpus()
        available = effective & online
        permitted = available & self.config.allowed_cpus
        all_cores = self.platform.cores(permitted)
        canonical_slots: list[str] = []
        bindings: list[dict[str, object]] = []
        slot_sets: dict[int, frozenset[int]] = {}
        union: set[int] = set()
        campaign_signatures: set[tuple[str, ...]] = set()
        for slot_id, raw in enumerate(raw_slots):
            cpus = parse_cpu_list(raw)
            if not cpus <= permitted:
                unavailable = cpus - permitted
                raise GuardError(
                    f"slot {slot_id} includes unavailable CPUs {format_cpu_list(unavailable)}"
                )
            if union & cpus:
                raise GuardError(
                    f"slot {slot_id} overlaps an earlier slot on {format_cpu_list(union & cpus)}"
                )
            selected_cores = [core for siblings, core in all_cores.items() if siblings <= cpus]
            reconstructed = frozenset(cpu for core in selected_cores for cpu in core.cpus)
            if reconstructed != cpus:
                partial = cpus - reconstructed
                raise GuardError(
                    f"slot {slot_id} does not contain complete SMT sibling groups; "
                    f"partial CPUs={format_cpu_list(partial)}"
                )
            if len(selected_cores) != self.config.physical_cores_per_slot:
                raise GuardError(
                    f"slot {slot_id} has {len(selected_cores)} physical cores; "
                    f"exactly {self.config.physical_cores_per_slot} are required"
                )
            signatures = {core.signature for core in selected_cores}
            if len(signatures) != 1:
                raise GuardError(f"slot {slot_id} mixes CPU topology/types")
            campaign_signatures.update(signatures)
            union.update(cpus)
            slot_sets[slot_id] = cpus
            canonical_slots.append(format_cpu_list(cpus))
            bindings.append(_slot_payload(slot_id, slot_id, cpus, selected_cores))
        reserved = frozenset(union)
        if len(campaign_signatures) != 1:
            raise GuardError("campaign slots do not share one homogeneous CPU topology/type")
        if not (effective - reserved):
            raise GuardError("reservation must leave at least one host CPU unreserved")
        return canonical_slots, bindings, slot_sets, available

    def _capture_baseline(self) -> dict[str, object]:
        siblings: dict[str, dict[str, str]] = {}
        for cgroup in self.platform.root_siblings():
            partition = self.platform.partition(cgroup)
            if partition != "member":
                raise GuardError(
                    f"refusing to alter existing top-level partition {cgroup.name}: {partition}"
                )
            siblings[cgroup.name] = {
                "cpus": self.platform.cpus(cgroup),
                "partition": partition,
                "device": cgroup.stat().st_dev,
                "inode": cgroup.stat().st_ino,
            }
        self.platform.verify_guard_unit()
        guard_cpus = self.platform.cpus(self.platform.guard_path)
        guard_allowed = self.platform.unit_allowed_cpus(GUARD_SLICE)
        guard_effective = self.platform.effective_cpus(self.platform.guard_path)
        guard_mems = self.platform.mems(self.platform.guard_path)
        guard_allowed_mems = self.platform.unit_allowed_memory_nodes(GUARD_SLICE)
        guard_effective_mems = self.platform.effective_mems(self.platform.guard_path)
        if (
            not guard_effective
            or guard_cpus != guard_allowed
            or guard_mems != ""
            or guard_allowed_mems != ""
            or not guard_effective_mems
        ):
            raise GuardError(
                "VSCLReuse parent CPU/memory-node baseline is not pristine"
            )
        guard = {
            "cpus": guard_cpus,
            "partition": self.platform.partition(self.platform.guard_path),
            "effective_cpus": format_cpu_list(guard_effective),
            "systemd_allowed_cpus": guard_allowed,
            "mems": guard_mems,
            "effective_mems": format_cpu_list(guard_effective_mems),
            "systemd_allowed_memory_nodes": guard_allowed_mems,
            "device": self.platform.guard_path.stat().st_dev,
            "inode": self.platform.guard_path.stat().st_ino,
        }
        slots: dict[str, dict[str, object]] = {}
        for index in range(self.config.maximum_slots):
            self.platform.verify_slot_unit(index)
            path = self.platform.slot_path(index)
            cpus = self.platform.cpus(path)
            allowed = self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
            effective = self.platform.effective_cpus(path)
            mems = self.platform.mems(path)
            allowed_mems = self.platform.unit_allowed_memory_nodes(
                self.platform.slot_unit(index)
            )
            effective_mems = self.platform.effective_mems(path)
            if (
                not effective
                or cpus != allowed
                or mems != ""
                or allowed_mems != ""
                or not effective_mems
            ):
                raise GuardError(
                    f"VSCLReuse slot {index} CPU/memory-node baseline is not pristine"
                )
            slots[str(index)] = {
                "cpus": cpus,
                "partition": self.platform.partition(path),
                "effective_cpus": format_cpu_list(effective),
                "systemd_allowed_cpus": allowed,
                "mems": mems,
                "effective_mems": format_cpu_list(effective_mems),
                "systemd_allowed_memory_nodes": allowed_mems,
                "device": path.stat().st_dev,
                "inode": path.stat().st_ino,
                "controller_pin": self._controller_pin_identity(index),
            }
        if guard["partition"] != "member" or any(
            value["partition"] != "member" for value in slots.values()
        ):
            raise GuardError("VSCLReuse slice already has an unmanaged CPU partition")
        return {"siblings": siblings, "guard": guard, "slots": slots}

    def _build_application_plan(
        self, slot_sets: Mapping[int, frozenset[int]]
    ) -> dict[str, object]:
        root_cpus = self.platform.root_effective_cpus()
        reserved = frozenset(cpu for cpus in slot_sets.values() for cpu in cpus)
        if not reserved or not reserved <= root_cpus:
            raise GuardError("CPU partition plan is outside the root effective CPU set")
        host = root_cpus - reserved
        if not host:
            raise GuardError("CPU partition would leave the host with no CPU")
        siblings = self.platform.root_siblings()
        return {
            "host_cpus": format_cpu_list(host),
            "reserved_cpus": format_cpu_list(reserved),
            "sibling_names": [path.name for path in siblings],
            "slot_cpus": {
                str(index): format_cpu_list(cpus) for index, cpus in slot_sets.items()
            },
            # A partition parent has no effective CPUs after its complete union
            # has been handed to its disjoint child partition roots.
            "guard_effective_cpus_after_slot_partitioning": "",
        }

    def _parse_application_plan(
        self, applied: Mapping[str, object]
    ) -> tuple[frozenset[int], frozenset[int], dict[int, frozenset[int]]]:
        expected_keys = {
            "host_cpus",
            "reserved_cpus",
            "sibling_names",
            "slot_cpus",
            "guard_effective_cpus_after_slot_partitioning",
        }
        if set(applied) != expected_keys:
            raise GuardError("stored CPU-partition application plan is malformed")
        host_raw = applied.get("host_cpus")
        reserved_raw = applied.get("reserved_cpus")
        sibling_names = applied.get("sibling_names")
        slot_cpus_raw = applied.get("slot_cpus")
        guard_effective = applied.get("guard_effective_cpus_after_slot_partitioning")
        if (
            not isinstance(host_raw, str)
            or not isinstance(reserved_raw, str)
            or not isinstance(sibling_names, list)
            or not isinstance(slot_cpus_raw, dict)
            or guard_effective != ""
        ):
            raise GuardError("stored CPU-partition application plan is malformed")
        host = parse_cpu_list(host_raw)
        reserved = parse_cpu_list(reserved_raw)
        self.platform.verify_guard_unit()
        if format_cpu_list(host) != host_raw or format_cpu_list(reserved) != reserved_raw:
            raise GuardError("stored CPU-partition plan uses a non-canonical CPU list")
        if host & reserved:
            raise GuardError("stored host and reserved CPU sets overlap")
        if (
            any(not isinstance(name, str) or not name for name in sibling_names)
            or len(set(sibling_names)) != len(sibling_names)
        ):
            raise GuardError("stored top-level sibling list is malformed")
        slot_sets: dict[int, frozenset[int]] = {}
        for key, raw in slot_cpus_raw.items():
            if (
                not isinstance(key, str)
                or re.fullmatch(r"0|[1-9][0-9]*", key) is None
                or not isinstance(raw, str)
            ):
                raise GuardError("stored slot CPU plan is malformed")
            index = int(key)
            if index >= self.config.maximum_slots:
                raise GuardError("stored slot CPU plan exceeds the installed maximum")
            cpus = parse_cpu_list(raw)
            if format_cpu_list(cpus) != raw:
                raise GuardError("stored slot CPU plan is not canonical")
            if any(cpus & prior for prior in slot_sets.values()):
                raise GuardError("stored slot CPU plan contains overlapping slots")
            slot_sets[index] = cpus
        if not slot_sets:
            raise GuardError("stored CPU-partition plan has no slots")
        planned_union = frozenset(cpu for cpus in slot_sets.values() for cpu in cpus)
        if planned_union != reserved:
            raise GuardError("stored slot CPU union does not match reserved CPUs")
        return host, reserved, slot_sets

    def _validate_transaction_layout(
        self,
        baseline: Mapping[str, object],
        applied: Mapping[str, object],
        *,
        allow_partial: bool,
        strict_foreign_siblings: bool = False,
    ) -> tuple[dict[str, object], dict[str, object], dict[int, frozenset[int]]]:
        """Validate every identity and CAS value before a managed write.

        During a durable recovery, each managed cpuset may be at its baseline,
        at its fully applied target, or at the one-write ``member,target``
        transition produced by this helper.  No other value is adopted.
        """

        if set(baseline) != {"siblings", "guard", "slots"}:
            raise GuardError("stored CPU-partition baseline is malformed")
        slots_raw = baseline.get("slots")
        guard_raw = baseline.get("guard")
        siblings_raw = baseline.get("siblings")
        if (
            not isinstance(slots_raw, dict)
            or not isinstance(guard_raw, dict)
            or not isinstance(siblings_raw, dict)
        ):
            raise GuardError("stored CPU-partition baseline is malformed")
        host, reserved, slot_sets = self._parse_application_plan(applied)
        del host

        self._assert_empty_managed_hierarchy()
        if strict_foreign_siblings:
            sibling_names = applied.get("sibling_names")
            if (
                any(not isinstance(name, str) for name in siblings_raw)
                or sibling_names != sorted(siblings_raw)
            ):
                raise GuardError(
                    "stored application sibling list does not match its baseline"
                )
            current_siblings = {
                path.name: path for path in self.platform.root_siblings()
            }
            if set(current_siblings) != set(siblings_raw):
                raise GuardError("top-level cgroup set changed during CPU admission")
            for name, prior_value in siblings_raw.items():
                if not isinstance(prior_value, dict) or set(prior_value) != {
                    "cpus",
                    "partition",
                    "device",
                    "inode",
                }:
                    raise GuardError("stored sibling baseline is malformed")
                cgroup = current_siblings[name]
                info = cgroup.stat()
                if (
                    info.st_dev != prior_value.get("device")
                    or info.st_ino != prior_value.get("inode")
                ):
                    raise GuardError(
                        f"top-level cgroup {name} was replaced during CPU admission"
                    )
                if self.platform.cpus(cgroup) != prior_value.get("cpus"):
                    raise GuardError(
                        f"top-level cgroup {name} CPU request changed during CPU admission"
                    )
                if self.platform.partition(cgroup) != prior_value.get("partition"):
                    raise GuardError(
                        f"top-level cgroup {name} partition changed during CPU admission"
                    )

        prior_guard_cpus = guard_raw.get("cpus")
        prior_guard_effective_raw = guard_raw.get("effective_cpus")
        if (
            set(guard_raw)
            != {
                "cpus",
                "partition",
                "effective_cpus",
                "systemd_allowed_cpus",
                "mems",
                "effective_mems",
                "systemd_allowed_memory_nodes",
                "device",
                "inode",
            }
            or prior_guard_cpus is None
            or not isinstance(prior_guard_cpus, str)
            or not isinstance(prior_guard_effective_raw, str)
            or not isinstance(guard_raw.get("systemd_allowed_cpus"), str)
            or guard_raw.get("systemd_allowed_cpus") != prior_guard_cpus
            or guard_raw.get("mems") != ""
            or guard_raw.get("systemd_allowed_memory_nodes") != ""
            or not isinstance(guard_raw.get("effective_mems"), str)
        ):
            raise GuardError("stored guard baseline is malformed")
        prior_guard_effective = parse_cpu_list(prior_guard_effective_raw)
        if format_cpu_list(prior_guard_effective) != prior_guard_effective_raw:
            raise GuardError("stored guard effective CPU baseline is not canonical")
        prior_guard_effective_mems = parse_cpu_list(guard_raw["effective_mems"])
        if format_cpu_list(prior_guard_effective_mems) != guard_raw["effective_mems"]:
            raise GuardError("stored guard effective memory-node baseline is not canonical")
        if guard_raw.get("partition") != "member":
            raise GuardError("stored guard baseline was not a partition member")
        guard_info = self.platform.guard_path.stat()
        if guard_info.st_dev != guard_raw.get("device") or guard_info.st_ino != guard_raw.get("inode"):
            raise GuardError("VSCLReuse parent cgroup was replaced")
        self.platform.verify_guard_unit()
        current_guard = (
            self.platform.partition(self.platform.guard_path),
            self.platform.cpus(self.platform.guard_path),
        )
        allowed_guard = {("member", prior_guard_cpus)}
        if allow_partial:
            reserved_raw = format_cpu_list(reserved)
            allowed_guard.update({("member", reserved_raw), ("root", reserved_raw)})
        if current_guard not in allowed_guard:
            raise GuardError("VSCLReuse parent is outside its recoverable CAS states")
        current_guard_property = self.platform.unit_allowed_cpus(GUARD_SLICE)
        allowed_guard_properties = {guard_raw["systemd_allowed_cpus"]}
        if allow_partial:
            allowed_guard_properties.add(format_cpu_list(reserved))
        if current_guard_property not in allowed_guard_properties:
            raise GuardError(
                "VSCLReuse parent systemd AllowedCPUs is outside its recoverable CAS states"
            )
        if (
            self.platform.unit_allowed_memory_nodes(GUARD_SLICE) != ""
            or self.platform.mems(self.platform.guard_path) != ""
            or self.platform.effective_mems(self.platform.guard_path)
            != prior_guard_effective_mems
        ):
            raise GuardError("VSCLReuse parent memory-node state changed")
        current_guard_effective = self.platform.effective_cpus(
            self.platform.guard_path
        )
        if (
            not allow_partial
            and current_guard_effective != prior_guard_effective
        ):
            raise GuardError("VSCLReuse parent effective CPU baseline changed")

        expected_slot_keys = {
            str(index) for index in range(self.config.maximum_slots)
        }
        if set(slots_raw) != expected_slot_keys:
            raise GuardError("stored slot baseline does not match the installed slot set")
        for index in range(self.config.maximum_slots):
            cgroup = self.platform.slot_path(index)
            prior = slots_raw.get(str(index))
            if (
                not isinstance(prior, dict)
                or set(prior)
                != {
                    "cpus",
                    "partition",
                    "effective_cpus",
                    "systemd_allowed_cpus",
                    "mems",
                    "effective_mems",
                    "systemd_allowed_memory_nodes",
                    "device",
                    "inode",
                    "controller_pin",
                }
                or not isinstance(prior.get("cpus"), str)
                or not isinstance(prior.get("effective_cpus"), str)
                or not isinstance(prior.get("systemd_allowed_cpus"), str)
                or prior.get("systemd_allowed_cpus") != prior.get("cpus")
                or prior.get("mems") != ""
                or prior.get("systemd_allowed_memory_nodes") != ""
                or not isinstance(prior.get("effective_mems"), str)
                or not isinstance(prior.get("controller_pin"), dict)
            ):
                raise GuardError(f"stored slot {index} baseline is malformed")
            if prior.get("partition") != "member":
                raise GuardError(f"stored slot {index} baseline was not a partition member")
            info = cgroup.stat()
            if info.st_dev != prior.get("device") or info.st_ino != prior.get("inode"):
                raise GuardError(f"slot {index} cgroup was replaced")
            self.platform.verify_slot_unit(index)
            prior_effective = parse_cpu_list(prior["effective_cpus"])
            if format_cpu_list(prior_effective) != prior["effective_cpus"]:
                raise GuardError(
                    f"stored slot {index} effective CPU baseline is not canonical"
                )
            prior_effective_mems = parse_cpu_list(prior["effective_mems"])
            if format_cpu_list(prior_effective_mems) != prior["effective_mems"]:
                raise GuardError(
                    f"stored slot {index} effective memory-node baseline is not canonical"
                )
            if self._controller_pin_identity(index) != prior["controller_pin"]:
                raise GuardError(f"slot {index} controller pin was replaced")
            current = (self.platform.partition(cgroup), self.platform.cpus(cgroup))
            allowed = {("member", prior["cpus"])}
            if allow_partial and index in slot_sets:
                target = format_cpu_list(slot_sets[index])
                allowed.update({("member", target), ("root", target)})
            if current not in allowed:
                raise GuardError(f"slot {index} is outside its recoverable CAS states")
            current_property = self.platform.unit_allowed_cpus(
                self.platform.slot_unit(index)
            )
            allowed_properties = {prior["systemd_allowed_cpus"]}
            if allow_partial and index in slot_sets:
                allowed_properties.add(format_cpu_list(slot_sets[index]))
            if current_property not in allowed_properties:
                raise GuardError(
                    f"slot {index} systemd AllowedCPUs is outside its recoverable CAS states"
                )
            if (
                self.platform.unit_allowed_memory_nodes(
                    self.platform.slot_unit(index)
                )
                != ""
                or self.platform.mems(cgroup) != ""
                or self.platform.effective_mems(cgroup) != prior_effective_mems
            ):
                raise GuardError(f"slot {index} memory-node state changed")
            if (
                not allow_partial
                and self.platform.effective_cpus(cgroup) != prior_effective
            ):
                raise GuardError(f"slot {index} effective CPU baseline changed")
        return guard_raw, slots_raw, slot_sets

    def _apply(
        self,
        baseline: Mapping[str, object],
        applied: Mapping[str, object],
    ) -> dict[str, object]:
        host, reserved, slot_sets = self._parse_application_plan(applied)
        guard_raw, slots_raw, _ = self._validate_transaction_layout(
            baseline,
            applied,
            allow_partial=False,
            strict_foreign_siblings=True,
        )
        if self.platform.root_effective_cpus() != host | reserved:
            raise GuardError("root effective CPUs changed after the durable plan was recorded")
        reserved_raw = format_cpu_list(reserved)
        siblings = self.platform.root_siblings()
        if [path.name for path in siblings] != applied.get("sibling_names"):
            raise GuardError("top-level cgroup set changed before partition application")
        # Empty requested masks inherit the parent partition's complement.
        # Never write a foreign cgroup.  An explicit sibling mask must already
        # be disjoint or acquisition fails without changing it.
        for cgroup in siblings:
            requested = _parse_optional_cpu_list(self.platform.cpus(cgroup))
            overlap = requested & reserved
            if overlap:
                raise GuardError(
                    f"top-level cgroup {cgroup.name} explicitly requests reserved CPUs "
                    f"{format_cpu_list(overlap)}"
                )
        # Bind systemd's own desired mask before making either cgroup a
        # partition root.  On systemd v252, later unit realization can reapply
        # this property; an explicit exact value prevents an unset property
        # from clobbering the helper-owned cpuset.cpus files.
        self.platform.set_unit_allowed_cpus(GUARD_SLICE, reserved_raw)
        if (
            self.platform.unit_allowed_cpus(GUARD_SLICE) != reserved_raw
            or self.platform.cpus(self.platform.guard_path) != reserved_raw
            or self.platform.partition(self.platform.guard_path) != "member"
            or self.platform.effective_cpus(self.platform.guard_path) != reserved
            or not self._memory_state_matches(
                self.platform.guard_path, GUARD_SLICE, guard_raw
            )
        ):
            raise GuardError(
                "systemd did not apply the parent AllowedCPUs mask before partitioning"
            )
        for index, cpus in slot_sets.items():
            cgroup = self.platform.slot_path(index)
            cpus_raw = format_cpu_list(cpus)
            self.platform.set_unit_allowed_cpus(
                self.platform.slot_unit(index), cpus_raw
            )
            if (
                self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
                != cpus_raw
                or self.platform.cpus(cgroup) != cpus_raw
                or self.platform.partition(cgroup) != "member"
                or self.platform.effective_cpus(cgroup) != cpus
                or not self._memory_state_matches(
                    cgroup, self.platform.slot_unit(index), slots_raw[str(index)]
                )
            ):
                raise GuardError(
                    f"systemd did not apply slot {index} AllowedCPUs before partitioning"
                )
        # No partition root exists until every systemd property and every raw
        # member mask has been read back exactly.  This avoids a window where
        # PID 1 could re-realize a later slot with an unset target while the
        # parent is already a live partition.
        self._assert_empty_managed_hierarchy()
        for index, cpus in slot_sets.items():
            cgroup = self.platform.slot_path(index)
            cpus_raw = format_cpu_list(cpus)
            if (
                self.platform.partition(cgroup) != "member"
                or self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
                != cpus_raw
                or self.platform.cpus(cgroup) != cpus_raw
                or self.platform.effective_cpus(cgroup) != cpus
                or not self._memory_state_matches(
                    cgroup, self.platform.slot_unit(index), slots_raw[str(index)]
                )
            ):
                raise GuardError(
                    f"slot {index} member mask drifted before partition commit"
                )
        # This is the authoritative commit-edge affinity scan.  Earlier scans
        # protect admission, but state fsync and systemd property commits take
        # time.  Re-read the host snapshot and reject a foreign thread that was
        # pinned during that interval immediately before the first partition
        # root can remove its eligibility.
        available_now = (
            self.platform.root_effective_cpus() & self.platform.online_cpus()
        )
        if available_now != host | reserved:
            raise GuardError("host CPU availability changed at partition commit")
        pinned_at_commit = self.platform.pinned_threads(reserved, available_now)
        if pinned_at_commit:
            raise GuardError(
                "a pinned foreign thread appeared at partition commit: "
                + json.dumps(pinned_at_commit, sort_keys=True)
            )
        self.platform.set_partition(self.platform.guard_path, "root")
        if (
            self.platform.unit_allowed_cpus(GUARD_SLICE) != reserved_raw
            or self.platform.cpus(self.platform.guard_path) != reserved_raw
            or self.platform.partition(self.platform.guard_path) != "root"
            or self.platform.effective_cpus(self.platform.guard_path) != reserved
            or not self._memory_state_matches(
                self.platform.guard_path, GUARD_SLICE, guard_raw
            )
        ):
            raise GuardError(
                "VSCLReuse parent did not receive the reserved union before slot partitioning"
            )
        for index, cpus in slot_sets.items():
            cgroup = self.platform.slot_path(index)
            cpus_raw = format_cpu_list(cpus)
            self.platform.set_partition(cgroup, "root")
            if (
                self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
                != cpus_raw
                or self.platform.cpus(cgroup) != cpus_raw
                or self.platform.partition(cgroup) != "root"
                or self.platform.effective_cpus(cgroup) != cpus
                or not self._memory_state_matches(
                    cgroup, self.platform.slot_unit(index), slots_raw[str(index)]
                )
            ):
                raise GuardError(
                    f"slot {index} did not become an exact partition root"
                )
        if (
            self.platform.cpus(self.platform.guard_path) != reserved_raw
            or self.platform.partition(self.platform.guard_path) != "root"
        ):
            raise GuardError("VSCLReuse parent requested partition drifted during apply")
        for index, cpus in slot_sets.items():
            cgroup = self.platform.slot_path(index)
            if self.platform.partition(cgroup) != "root":
                raise GuardError(f"slot {index} did not become a valid partition root")
            if self.platform.effective_cpus(cgroup) != cpus:
                raise GuardError(f"slot {index} effective CPUs do not match its lease")
        if self.platform.effective_cpus(self.platform.guard_path):
            raise GuardError("VSCLReuse parent retained CPUs assigned to child slots")
        final_siblings = self.platform.root_siblings()
        for cgroup in final_siblings:
            overlap = self.platform.effective_cpus(cgroup) & reserved
            if overlap:
                raise GuardError(
                    f"top-level cgroup {cgroup.name} remains eligible on reserved CPUs "
                    f"{format_cpu_list(overlap)}"
                )
        if [path.name for path in final_siblings] != applied.get("sibling_names"):
            raise GuardError("top-level cgroup set changed during partition application")
        self._validate_transaction_layout(
            baseline,
            applied,
            allow_partial=True,
            strict_foreign_siblings=True,
        )
        return dict(applied)

    def _restore(
        self,
        baseline: Mapping[str, object],
        applied: Mapping[str, object],
    ) -> None:
        guard_raw, slots_raw, slot_sets = self._validate_transaction_layout(
            baseline, applied, allow_partial=True
        )
        # All hierarchy, emptiness, identity, and compare-and-swap checks finish
        # before the first restoring write.  Each write is idempotent, so a hard
        # interruption can be retried from the durable RELEASING state.
        def member_effective_is_exact(
            cgroup: Path,
            requested_raw: str,
            parent_effective: frozenset[int],
        ) -> bool:
            requested = _parse_optional_cpu_list(requested_raw)
            granted = requested & parent_effective
            # cgroup v2 falls back to the parent's effective set when an empty
            # request is inherited *or* a nonempty request has no online grant.
            expected = granted if granted else parent_effective
            return self.platform.effective_cpus(cgroup) == expected

        def restore_raw_mask(
            cgroup: Path,
            *,
            applied_raw: str,
            baseline_raw: str,
            label: str,
        ) -> None:
            # Re-read immediately before the direct cgroup write.  systemd may
            # have moved the raw mask from the applied value to the baseline;
            # any third value is concurrent or abnormal drift and must not be
            # overwritten by recovery.
            current_raw = self.platform.cpus(cgroup)
            if current_raw not in {applied_raw, baseline_raw}:
                raise GuardError(
                    f"{label} raw cpuset changed before baseline reconciliation"
                )
            if current_raw != baseline_raw:
                self.platform.set_cpus(cgroup, baseline_raw)

        for index in sorted(slot_sets):
            cgroup = self.platform.slot_path(index)
            prior = slots_raw[str(index)]
            if self.platform.partition(cgroup) != "member":
                self.platform.set_partition(cgroup, "member")
            target = format_cpu_list(slot_sets[index])
            current_property = self.platform.unit_allowed_cpus(
                self.platform.slot_unit(index)
            )
            current_requested = self.platform.cpus(cgroup)
            if (
                self.platform.partition(cgroup) != "member"
                or current_property
                not in {target, prior["systemd_allowed_cpus"]}
                or current_requested not in {target, prior["cpus"]}
                # A top-level partition removes its CPUs from the cgroup-v2
                # mount root's effective mask.  Once this nested slot becomes
                # a member, validate it against its immediate parent instead
                # of that deliberately disjoint mount-root complement.
                or not member_effective_is_exact(
                    cgroup,
                    current_requested,
                    self.platform.effective_cpus(self.platform.guard_path),
                )
                or not self._memory_state_matches(
                    cgroup, self.platform.slot_unit(index), prior
                )
            ):
                raise GuardError(
                    f"slot {index} did not leave its partition root exactly"
                )
        prior_guard_cpus = guard_raw.get("cpus")
        if not isinstance(prior_guard_cpus, str):
            raise GuardError("stored guard baseline is malformed")
        if self.platform.partition(self.platform.guard_path) != "member":
            self.platform.set_partition(self.platform.guard_path, "member")
        reserved_raw = applied.get("reserved_cpus")
        current_guard_property = self.platform.unit_allowed_cpus(GUARD_SLICE)
        current_guard_requested = self.platform.cpus(self.platform.guard_path)
        root_effective = self.platform.root_effective_cpus()
        if (
            not isinstance(reserved_raw, str)
            or self.platform.partition(self.platform.guard_path) != "member"
            or current_guard_property
            not in {reserved_raw, guard_raw["systemd_allowed_cpus"]}
            or current_guard_requested not in {reserved_raw, prior_guard_cpus}
            or not member_effective_is_exact(
                self.platform.guard_path,
                current_guard_requested,
                root_effective,
            )
            or not self._memory_state_matches(
                self.platform.guard_path, GUARD_SLICE, guard_raw
            )
        ):
            raise GuardError("VSCLReuse parent did not leave its partition root exactly")
        # Restore systemd's desired values only after all managed partition
        # roots are members again.  A systemd write cannot then accidentally
        # invalidate a live partition tree.
        for index in sorted(slot_sets):
            cgroup = self.platform.slot_path(index)
            prior = slots_raw[str(index)]
            target = format_cpu_list(slot_sets[index])
            self.platform.set_unit_allowed_cpus(
                self.platform.slot_unit(index), prior["systemd_allowed_cpus"]
            )
            # systemd 252 may commit an empty AllowedCPUs= property without
            # clearing the already-realized slice's raw cpuset.cpus file.  Once
            # all managed partitions are members, reconcile only our empty,
            # authenticated cgroup to the saved raw baseline.  A later systemd
            # realization now has the same desired property and cannot undo it.
            restore_raw_mask(
                cgroup,
                applied_raw=target,
                baseline_raw=prior["cpus"],
                label=f"slot {index}",
            )
            if (
                self.platform.partition(cgroup) != "member"
                or self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
                != prior["systemd_allowed_cpus"]
                or self.platform.cpus(cgroup) != prior["cpus"]
                or not member_effective_is_exact(
                    cgroup,
                    prior["cpus"],
                    self.platform.effective_cpus(self.platform.guard_path),
                )
                or not self._memory_state_matches(
                    cgroup, self.platform.slot_unit(index), prior
                )
            ):
                raise GuardError(
                    f"slot {index} did not restore its systemd/cpuset member state"
                )
        self.platform.set_unit_allowed_cpus(
            GUARD_SLICE, guard_raw["systemd_allowed_cpus"]
        )
        restore_raw_mask(
            self.platform.guard_path,
            applied_raw=reserved_raw,
            baseline_raw=prior_guard_cpus,
            label="VSCLReuse parent",
        )
        if (
            self.platform.partition(self.platform.guard_path) != "member"
            or self.platform.unit_allowed_cpus(GUARD_SLICE)
            != guard_raw["systemd_allowed_cpus"]
            or self.platform.cpus(self.platform.guard_path) != prior_guard_cpus
            or self.platform.effective_cpus(self.platform.guard_path)
            != parse_cpu_list(guard_raw["effective_cpus"])
            or not self._memory_state_matches(
                self.platform.guard_path, GUARD_SLICE, guard_raw
            )
        ):
            raise GuardError(
                "VSCLReuse parent did not restore its systemd/cpuset member state"
            )
        self._validate_transaction_layout(baseline, applied, allow_partial=False)

    def _attest_active_layout(
        self,
        lease: Mapping[str, object],
        applied: Mapping[str, object],
        baseline: Mapping[str, object],
    ) -> None:
        reserved_raw = applied.get("reserved_cpus")
        bindings = lease.get("slot_bindings")
        baseline_slots = baseline.get("slots")
        baseline_guard = baseline.get("guard")
        if (
            not isinstance(reserved_raw, str)
            or not isinstance(bindings, list)
            or not isinstance(baseline_slots, dict)
            or not isinstance(baseline_guard, dict)
        ):
            raise GuardError("active lease attestation state is malformed")
        reserved = parse_cpu_list(reserved_raw)
        self.platform.verify_guard_unit()
        expected_slot_names = {
            self.platform.slot_path(index).name for index in range(self.config.maximum_slots)
        }
        actual_slot_names = {
            path.name for path in self.platform.children(self.platform.guard_path)
        }
        if actual_slot_names != expected_slot_names:
            raise GuardError("VSCLReuse parent gained an unexpected child cgroup")
        if self.platform.direct_processes(self.platform.guard_path):
            raise GuardError("VSCLReuse parent contains unexpected direct processes")
        if (
            self.platform.partition(self.platform.guard_path) != "root"
            or self.platform.cpus(self.platform.guard_path) != reserved_raw
            or self.platform.unit_allowed_cpus(GUARD_SLICE) != reserved_raw
            or self.platform.effective_cpus(self.platform.guard_path)
            or self.platform.mems(self.platform.guard_path)
            != baseline_guard.get("mems")
            or self.platform.unit_allowed_memory_nodes(GUARD_SLICE)
            != baseline_guard.get("systemd_allowed_memory_nodes")
            or self.platform.effective_mems(self.platform.guard_path)
            != parse_cpu_list(str(baseline_guard.get("effective_mems")))
            or "cpuset" not in self.platform.subtree_controllers(
                self.platform.guard_path
            )
        ):
            raise GuardError(
                "VSCLReuse parent CPU/memory-node partition failed live attestation"
            )
        active_physical_slots: set[int] = set()
        active_units = lease.get("active_units")
        if not isinstance(active_units, dict):
            raise GuardError("active-unit attestation state is malformed")
        for binding in bindings:
            if not isinstance(binding, dict):
                raise GuardError("active slot attestation state is malformed")
            physical_slot = binding.get("physical_slot")
            cpus_raw = binding.get("cpus")
            if (
                not isinstance(physical_slot, int)
                or physical_slot < 0
                or physical_slot >= self.config.maximum_slots
                or physical_slot in active_physical_slots
                or not isinstance(cpus_raw, str)
            ):
                raise GuardError("active slot attestation binding is malformed")
            active_physical_slots.add(physical_slot)
            self.platform.verify_slot_unit(physical_slot)
            cgroup = self.platform.slot_path(physical_slot)
            expected = parse_cpu_list(cpus_raw)
            prior = baseline_slots.get(str(physical_slot))
            if (
                not isinstance(prior, dict)
                or self.platform.partition(cgroup) != "root"
                or self.platform.cpus(cgroup) != cpus_raw
                or self.platform.unit_allowed_cpus(
                    self.platform.slot_unit(physical_slot)
                )
                != cpus_raw
                or self.platform.effective_cpus(cgroup) != expected
                or self.platform.mems(cgroup) != prior.get("mems")
                or self.platform.unit_allowed_memory_nodes(
                    self.platform.slot_unit(physical_slot)
                )
                != prior.get("systemd_allowed_memory_nodes")
                or self.platform.effective_mems(cgroup)
                != parse_cpu_list(str(prior.get("effective_mems")))
                or "cpuset" not in self.platform.subtree_controllers(cgroup)
                or self._controller_pin_identity(physical_slot)
                != prior.get("controller_pin")
            ):
                raise GuardError(
                    f"slot {physical_slot} failed live cpuset partition attestation"
                )
            if self.platform.direct_processes(cgroup):
                raise GuardError(f"slot {physical_slot} contains unexpected direct processes")
            recorded_unit = active_units.get(cpus_raw)
            expected_children: set[str] = {CONTROLLER_PIN}
            if isinstance(recorded_unit, str):
                expected_children.add(
                    recorded_unit
                    if recorded_unit.endswith(".service")
                    else recorded_unit + ".service"
                )
            unexpected_children = {
                path.name for path in self.platform.children(cgroup)
            } - expected_children
            if unexpected_children:
                raise GuardError(
                    f"slot {physical_slot} contains unrecorded child cgroups: "
                    + ", ".join(sorted(unexpected_children))
                )
        lease_slots = lease.get("slots")
        if (
            not isinstance(lease_slots, list)
            or set(active_units) - set(lease_slots)
            or any(not isinstance(unit, str) for unit in active_units.values())
        ):
            raise GuardError("active-unit attestation state is malformed")
        for index in range(self.config.maximum_slots):
            if index in active_physical_slots:
                continue
            cgroup = self.platform.slot_path(index)
            self.platform.verify_slot_unit(index)
            prior = baseline_slots.get(str(index))
            if (
                not isinstance(prior, dict)
                or self._controller_pin_identity(index)
                != prior.get("controller_pin")
                or self.platform.partition(cgroup) != prior.get("partition")
                or self.platform.cpus(cgroup) != prior.get("cpus")
                or self.platform.unit_allowed_cpus(self.platform.slot_unit(index))
                != prior.get("systemd_allowed_cpus")
                or self.platform.mems(cgroup) != prior.get("mems")
                or self.platform.unit_allowed_memory_nodes(
                    self.platform.slot_unit(index)
                )
                != prior.get("systemd_allowed_memory_nodes")
                or self.platform.effective_mems(cgroup)
                != parse_cpu_list(str(prior.get("effective_mems")))
                or self.platform.direct_processes(cgroup)
                or {path.name for path in self.platform.children(cgroup)}
                != {CONTROLLER_PIN}
                or self.platform.populated(cgroup)
            ):
                raise GuardError(f"inactive slot {index} contains an unexpected workload")
        for sibling in self.platform.root_siblings():
            overlap = self.platform.effective_cpus(sibling) & reserved
            if overlap:
                raise GuardError(
                    f"outside cgroup {sibling.name} regained reserved CPUs "
                    f"{format_cpu_list(overlap)}"
                )

    @staticmethod
    def _clear_transaction_state(state: dict[str, object]) -> None:
        state.update(
            {
                "generation": int(state.get("generation", 0)) + 1,
                "phase": "inactive",
                "active_lease": None,
                "baseline": None,
                "applied": None,
            }
        )

    def acquire(self, lease_id: str, raw_slots: Sequence[str]) -> dict[str, object]:
        lease_id = _validate_lease_id(lease_id)
        with self.store.lease_lock(shared=False):
            with self.store.state_lock() as state:
                if state.get("active_lease") is not None:
                    raise GuardError("another campaign lease is already active")
                self.platform.prepare_slices(self.config.maximum_slots)
                self._assert_empty_managed_hierarchy()
                slots, slot_bindings, slot_sets, available = self._validated_slots(
                    raw_slots
                )
                reserved = frozenset(cpu for values in slot_sets.values() for cpu in values)
                self.platform.pin_self(self.platform.root_effective_cpus() - reserved)
                pre_partition_percentages = self.platform.sample_busy(
                    reserved, self.config.idle_sample_seconds
                )
                busy = {
                    str(cpu): percent
                    for cpu, percent in pre_partition_percentages.items()
                    if percent > self.config.maximum_busy_percent
                }
                if busy:
                    raise GuardError(
                        "requested lease is not idle; per-CPU busy percentages="
                        + json.dumps(busy, sort_keys=True)
                    )
                pinned = self.platform.pinned_threads(reserved, available)
                if pinned:
                    raise GuardError(
                        "requested lease contains pinned foreign threads: "
                        + json.dumps(pinned, sort_keys=True)
                    )
                # Close topology/hotplug and affinity races immediately before
                # the first cgroup write.  Every explicit slot must still map
                # to exactly the same canonical full-core set.
                (
                    slots_again,
                    bindings_again,
                    slot_sets_again,
                    available_again,
                ) = self._validated_slots(raw_slots)
                if (
                    slots_again != slots
                    or bindings_again != slot_bindings
                    or slot_sets_again != slot_sets
                    or available_again != available
                ):
                    raise GuardError("CPU topology changed during idle admission")
                pinned_again = self.platform.pinned_threads(
                    reserved, available_again
                )
                if pinned_again:
                    raise GuardError(
                        "a pinned foreign thread appeared immediately before partitioning: "
                        + json.dumps(pinned_again, sort_keys=True)
                    )
                self._assert_empty_managed_hierarchy()
                baseline = self._capture_baseline()
                applied = self._build_application_plan(slot_sets)
                generation = int(state.get("generation", 0)) + 1
                lease = {
                    "lease_id": lease_id,
                    "slots": slots,
                    "slot_bindings": slot_bindings,
                    "reserved_cpus": applied["reserved_cpus"],
                    "active_units": {},
                    "acquired_monotonic_ns": time.monotonic_ns(),
                }
                # This fsync occurs before the first cgroup write.  A hard
                # interruption therefore leaves enough root-only information
                # for `release --lease-id` to restore any known partial state.
                state.update(
                    {
                        "generation": generation,
                        "phase": "preparing",
                        "active_lease": lease,
                        "baseline": baseline,
                        "applied": applied,
                    }
                )
                self.store.save(state)
                try:
                    self._apply(baseline, applied)
                    self._assert_empty_managed_hierarchy()
                    # The pre-partition sample proves we only attempted to take
                    # idle CPUs.  This second full-duration sample occurs after
                    # all outside userspace has lost eligibility, providing an
                    # exclusive cooldown window immediately before any provider
                    # process can be launched.
                    post_partition_percentages = self.platform.sample_busy(
                        reserved, self.config.idle_sample_seconds
                    )
                    post_partition_busy = {
                        str(cpu): percent
                        for cpu, percent in post_partition_percentages.items()
                        if percent > self.config.maximum_busy_percent
                    }
                    if post_partition_busy:
                        raise GuardError(
                            "requested lease was active during its exclusive "
                            "post-partition idle sample; per-CPU busy percentages="
                            + json.dumps(post_partition_busy, sort_keys=True)
                        )
                    self._assert_empty_managed_hierarchy()
                    self._attest_active_layout(lease, applied, baseline)
                except Exception as apply_error:
                    try:
                        self._restore(baseline, applied)
                        self._clear_transaction_state(state)
                        self.store.save(state)
                    except Exception as rollback_error:
                        raise GuardError(
                            "partition application failed; the durable PREPARING "
                            "transaction remains recoverable with release, but the "
                            f"immediate rollback failed: apply={apply_error}; "
                            f"rollback={rollback_error}"
                        ) from rollback_error
                    raise
                state["phase"] = "active"
                try:
                    self.store.save(state)
                except Exception as save_error:
                    raise GuardError(
                        "activation-state save failed after the partition was fully "
                        "applied; it remains fail-closed and release-recoverable from "
                        f"either the durable PREPARING or ACTIVE state: {save_error}"
                    ) from save_error
                return {
                    "schema_version": EVIDENCE_SCHEMA,
                    "kind": "highambench-cpu-guard-acquire",
                    "verified": True,
                    "lease_id": lease_id,
                    "slots": slots,
                    "slot_details": slot_bindings,
                    "reserved_cpus": applied["reserved_cpus"],
                    "host_cpus": applied["host_cpus"],
                    "idle_sample_seconds": self.config.idle_sample_seconds,
                    "maximum_busy_percent": self.config.maximum_busy_percent,
                    "observed_busy_percent": {
                        str(cpu): pre_partition_percentages[cpu]
                        for cpu in sorted(pre_partition_percentages)
                    },
                    "pre_partition_observed_busy_percent": {
                        str(cpu): pre_partition_percentages[cpu]
                        for cpu in sorted(pre_partition_percentages)
                    },
                    "exclusive_post_partition_observed_busy_percent": {
                        str(cpu): post_partition_percentages[cpu]
                        for cpu in sorted(post_partition_percentages)
                    },
                    "pinned_foreign_threads": [],
                }

    def status(self) -> dict[str, object]:
        with self.store.state_lock() as state:
            lease = state.get("active_lease")
            applied = state.get("applied")
            baseline = state.get("baseline")
            phase = state.get("phase")
            if phase == "active":
                if (
                    not isinstance(lease, dict)
                    or not isinstance(applied, dict)
                    or not isinstance(baseline, dict)
                ):
                    raise GuardError("active lease status state is malformed")
                self._pin_relay_to_host_complement(applied)
                self._attest_active_layout(lease, applied, baseline)
            elif phase in {"preparing", "releasing"}:
                if (
                    not isinstance(lease, dict)
                    or not isinstance(baseline, dict)
                    or not isinstance(applied, dict)
                ):
                    raise GuardError("recoverable transaction status state is malformed")
                self._validate_transaction_layout(
                    baseline, applied, allow_partial=True
                )
            return {
                "schema_version": EVIDENCE_SCHEMA,
                "kind": "highambench-cpu-guard-status",
                "verified": True,
                "generation": state.get("generation", 0),
                "phase": phase,
                "recovery_required": phase in {"preparing", "releasing"},
                "active_lease": lease,
                "applied": applied,
                "idle_sample_seconds": self.config.idle_sample_seconds,
                "maximum_busy_percent": self.config.maximum_busy_percent,
                "allowed_cpus": format_cpu_list(self.config.allowed_cpus),
                "maximum_slots": self.config.maximum_slots,
            }

    def launch(
        self,
        lease_id: str,
        unit: str,
        slot_cpu_list: str,
        working_directory: Path,
        proof_file: Path,
        command: Sequence[str],
    ) -> int:
        lease_id = _validate_lease_id(lease_id)
        unit = _validate_unit_name(unit)
        requested_cpus = parse_cpu_list(slot_cpu_list)
        canonical_slot = format_cpu_list(requested_cpus)
        cwd = _real_directory(working_directory, label="working directory")
        proof = _fresh_user_output(proof_file, self.config, label="proof file")
        # Shared for the whole measured service lifetime.  Other slot launches
        # can coexist; release takes the exclusive form and therefore waits.
        with self.store.lease_lock(shared=True) as lifetime_lock_fd:
            with self.store.slot_lock(canonical_slot):
                with self.store.state_lock() as state:
                    lease = state.get("active_lease")
                    if state.get("phase") != "active":
                        raise GuardError("campaign lease is not in its launchable active phase")
                    if not isinstance(lease, dict) or lease.get("lease_id") != lease_id:
                        raise GuardError("requested campaign lease is not active")
                    slots = lease.get("slots")
                    bindings = lease.get("slot_bindings")
                    active_units = lease.get("active_units")
                    applied = state.get("applied")
                    baseline = state.get("baseline")
                    if (
                        not isinstance(slots, list)
                        or not isinstance(bindings, list)
                        or not isinstance(active_units, dict)
                        or not isinstance(applied, dict)
                        or not isinstance(baseline, dict)
                    ):
                        raise GuardError("active lease state is malformed")
                    self._pin_relay_to_host_complement(applied)
                    self._attest_active_layout(lease, applied, baseline)
                    if canonical_slot not in slots:
                        raise GuardError("requested CPU set is not exactly one recorded lease slot")
                    slot_id = slots.index(canonical_slot)
                    binding = bindings[slot_id]
                    if not isinstance(binding, dict):
                        raise GuardError("active slot binding is malformed")
                    physical_slot = binding.get("physical_slot")
                    if not isinstance(physical_slot, int):
                        raise GuardError("active slot binding is malformed")
                    baseline_slots = baseline.get("slots")
                    baseline_guard = baseline.get("guard")
                    if (
                        not isinstance(baseline_slots, dict)
                        or not isinstance(baseline_guard, dict)
                    ):
                        raise GuardError("active lease baseline is malformed")
                    prior_slot = baseline_slots.get(str(physical_slot))
                    controller_pin = (
                        prior_slot.get("controller_pin")
                        if isinstance(prior_slot, dict)
                        else None
                    )
                    reserved_raw = applied.get("reserved_cpus")
                    guard_effective_mems_raw = baseline_guard.get("effective_mems")
                    slot_effective_mems_raw = (
                        prior_slot.get("effective_mems")
                        if isinstance(prior_slot, dict)
                        else None
                    )
                    if (
                        not isinstance(controller_pin, dict)
                        or not isinstance(reserved_raw, str)
                        or not isinstance(guard_effective_mems_raw, str)
                        or not isinstance(slot_effective_mems_raw, str)
                    ):
                        raise GuardError("active lease boundary identity is malformed")
                    campaign_cpus = parse_cpu_list(reserved_raw)
                    guard_effective_mems = parse_cpu_list(guard_effective_mems_raw)
                    slot_effective_mems = parse_cpu_list(slot_effective_mems_raw)
                    self.platform.verify_slot_unit(physical_slot)
                    if canonical_slot in active_units:
                        raise GuardError(f"slot {canonical_slot} already has an active measured unit")
                    if unit in active_units.values():
                        raise GuardError("measured unit name is already active in another slot")
                    active_units[canonical_slot] = unit
                    self.store.save(state)
                return_code = self.platform.launch(
                    self.config,
                    unit=unit,
                    slot_index=physical_slot,
                    cpus=requested_cpus,
                    campaign_cpus=campaign_cpus,
                    working_directory=cwd,
                    proof_file=proof,
                    command=command,
                    controller_pin=controller_pin,
                    guard_effective_mems=guard_effective_mems,
                    slot_effective_mems=slot_effective_mems,
                    lifetime_lock_fd=lifetime_lock_fd,
                )
                # LinuxPlatform returns only after the exact service cgroup has
                # disappeared.  On any launch/GC exception retain the record so
                # release remains fail-closed and performs its own empty checks.
                with self.store.state_lock() as state:
                    lease = state.get("active_lease")
                    if (
                        state.get("phase") != "active"
                        or not isinstance(lease, dict)
                        or lease.get("lease_id") != lease_id
                    ):
                        raise GuardError(
                            "campaign lease changed while measured service ran"
                        )
                    active_units = lease.get("active_units")
                    baseline = state.get("baseline")
                    applied = state.get("applied")
                    if (
                        not isinstance(active_units, dict)
                        or active_units.get(canonical_slot) != unit
                        or not isinstance(baseline, dict)
                        or not isinstance(applied, dict)
                    ):
                        raise GuardError(
                            "measured service state record changed while running"
                        )
                    self._attest_active_layout(lease, applied, baseline)
                    del active_units[canonical_slot]
                    self.store.save(state)
                return return_code

    def release(self, lease_id: str) -> dict[str, object]:
        lease_id = _validate_lease_id(lease_id)
        with self.store.lease_lock(shared=False):
            with self.store.state_lock() as state:
                lease = state.get("active_lease")
                phase = state.get("phase")
                if phase == "inactive" and lease is None:
                    return {
                        "schema_version": EVIDENCE_SCHEMA,
                        "kind": "highambench-cpu-guard-release",
                        "verified": True,
                        "lease_id": lease_id,
                        "slots": [],
                        "released": True,
                        "already_inactive": True,
                    }
                if phase not in {"preparing", "active", "releasing"}:
                    raise GuardError("CPU-guard transaction phase is invalid")
                if not isinstance(lease, dict) or lease.get("lease_id") != lease_id:
                    raise GuardError("requested campaign lease is not active")
                slots = lease.get("slots")
                bindings = lease.get("slot_bindings")
                active_units = lease.get("active_units")
                if (
                    not isinstance(slots, list)
                    or not isinstance(bindings, list)
                    or not isinstance(active_units, dict)
                ):
                    raise GuardError("active lease state is malformed")
                # The shared flock is transferred through systemd-run's stdin.
                # Holding its exclusive form therefore proves that no helper,
                # queued StartTransientUnit request, or not-yet-cgrouped
                # service retains the launch handoff.  A service wrapper
                # detaches the fd only after systemd places it in the measured
                # cgroup, so the authoritative populated checks below cover
                # that later phase.  No process is ever stopped to recover a
                # stale record.
                stale_launch_records = dict(active_units)
                applied = state.get("applied")
                baseline = state.get("baseline")
                if not isinstance(applied, dict) or not isinstance(baseline, dict):
                    raise GuardError("active lease partition transaction is incomplete")
                self._pin_relay_to_host_complement(applied)
                recovery_from_phase = phase
                if phase == "active":
                    self._attest_active_layout(lease, applied, baseline)
                    for binding in bindings:
                        if (
                            not isinstance(binding, dict)
                            or not isinstance(binding.get("physical_slot"), int)
                        ):
                            raise GuardError("active slot state is malformed")
                        physical_slot = binding["physical_slot"]
                        if self.platform.populated(self.platform.slot_path(physical_slot)):
                            raise GuardError(
                                f"slot {physical_slot} remains populated; release refuses to stop it"
                            )
                # This read-only check guarantees that transitioning to
                # RELEASING never adopts an unknown cpuset value or a populated
                # hierarchy.  The phase is fsynced before the first restore
                # write, making every subsequent step safely retryable.
                self._validate_transaction_layout(
                    baseline, applied, allow_partial=True
                )
                if phase != "releasing":
                    state["phase"] = "releasing"
                    self.store.save(state)
                self._restore(baseline, applied)
                released_slots = slots
                self._clear_transaction_state(state)
                try:
                    self.store.save(state)
                except Exception as save_error:
                    raise GuardError(
                        "release restored the host but could not persist inactive state; "
                        f"administrator recovery is required and CPUs were not re-reserved: {save_error}"
                    ) from save_error
                return {
                    "schema_version": EVIDENCE_SCHEMA,
                    "kind": "highambench-cpu-guard-release",
                    "verified": True,
                    "lease_id": lease_id,
                    "slots": released_slots,
                    "released": True,
                    "recovered_from_phase": recovery_from_phase,
                    "stale_launch_records": stale_launch_records,
                }


def _check_no_symlink_components(path: Path) -> None:
    if not path.is_absolute():
        raise GuardError("evidence path must be absolute")
    current = Path("/")
    for component in path.parts[1:]:
        current /= component
        if current == path and not current.exists():
            break
        info = os.lstat(current)
        if stat.S_ISLNK(info.st_mode):
            raise GuardError(f"evidence path traverses a symlink: {current}")


def _open_directory_chain(path: Path) -> int:
    """Open an absolute directory one non-symlink component at a time."""

    if not path.is_absolute():
        raise GuardError("directory path must be absolute")
    descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        for component in path.parts[1:]:
            next_descriptor = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW,
                dir_fd=descriptor,
            )
            os.close(descriptor)
            descriptor = next_descriptor
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def write_evidence(path: Path, payload: Mapping[str, object], config: Configuration) -> None:
    if not path.is_absolute() or path.name in {"", ".", ".."}:
        raise GuardError("evidence path must be an absolute leaf path")
    parent_descriptor = _open_directory_chain(path.parent)
    encoded = (json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n").encode()
    try:
        info = os.fstat(parent_descriptor)
        if info.st_uid != config.operator_uid or stat.S_IMODE(info.st_mode) != 0o700:
            raise GuardError("evidence parent must be operator-owned with exact mode 0700")
        descriptor = os.open(
            path.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
            dir_fd=parent_descriptor,
        )
        try:
            offset = 0
            while offset < len(encoded):
                offset += os.write(descriptor, encoded[offset:])
            os.fchown(descriptor, config.operator_uid, config.run_gid)
            os.fchmod(descriptor, 0o600)
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.fsync(parent_descriptor)
    finally:
        os.close(parent_descriptor)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    subparsers = parser.add_subparsers(dest="action", required=True)
    acquire = subparsers.add_parser(
        "acquire", help="atomically reserve all campaign slots", allow_abbrev=False
    )
    acquire.add_argument("--lease-id", required=True)
    acquire.add_argument("--slot", action="append", required=True, metavar="CPULIST")
    acquire.add_argument("--evidence", type=Path, required=True)
    status = subparsers.add_parser(
        "status", help="print root guard state without mutation", allow_abbrev=False
    )
    status.add_argument("--lease-id")
    launch = subparsers.add_parser(
        "launch", help="run one command in one leased slot", allow_abbrev=False
    )
    launch.add_argument("--lease-id", required=True)
    launch.add_argument("--unit", required=True)
    launch.add_argument("--slot", required=True, metavar="CPULIST")
    launch.add_argument("--working-directory", type=Path, required=True)
    launch.add_argument("--proof-file", type=Path, required=True)
    launch.add_argument("command", nargs=argparse.REMAINDER)
    release = subparsers.add_parser(
        "release",
        help="restore host CPUs after all launches finish",
        allow_abbrev=False,
    )
    release.add_argument("--lease-id", required=True)
    release.add_argument("--evidence", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    # The host service independently retains the shared generation lock.  If
    # the sudo/frontend client disappears, an installer still cannot replace
    # code or configuration underneath this already-running operation.
    with installation_generation_lock():
        config = load_configuration()
        authorize(config)
        platform = LinuxPlatform()
        platform.assert_host_pid_namespace()
        guard = CpuGuard(config, platform=platform)
        if arguments.action == "acquire":
            payload = guard.acquire(arguments.lease_id, arguments.slot)
            write_evidence(arguments.evidence, payload, config)
            print(json.dumps(payload, sort_keys=True, separators=(",", ":")), flush=True)
            return 0
        if arguments.action == "status":
            payload = guard.status()
            if arguments.lease_id is not None:
                _validate_lease_id(arguments.lease_id)
                active = payload.get("active_lease")
                if not isinstance(active, dict) or active.get("lease_id") != arguments.lease_id:
                    raise GuardError("requested campaign lease is not active")
            print(json.dumps(payload, sort_keys=True, separators=(",", ":")), flush=True)
            return 0
        if arguments.action == "launch":
            command = list(arguments.command)
            if command and command[0] == "--":
                command = command[1:]
            return guard.launch(
                arguments.lease_id,
                arguments.unit,
                arguments.slot,
                arguments.working_directory,
                arguments.proof_file,
                command,
            )
        if arguments.action == "release":
            payload = guard.release(arguments.lease_id)
            write_evidence(arguments.evidence, payload, config)
            print(json.dumps(payload, sort_keys=True, separators=(",", ":")), flush=True)
            return 0
        raise GuardError("unreachable command")


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (GuardError, OSError) as error:
        print(f"highambench CPU guard: {error}", file=sys.stderr)
        raise SystemExit(2)
