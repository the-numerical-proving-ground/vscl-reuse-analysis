#!/bin/sh
# Install the narrowly privileged VSCLReuse CPU guard.
#
# This installer creates only root-owned configuration, slice definitions, the
# helper executable, and one exact sudoers entry. It never starts, stops,
# signals, or moves a workload and it never creates a CPU lease.

set -eu
umask 077
PATH=/usr/sbin:/usr/bin:/sbin:/bin
export PATH

if [ "$(id -u)" -ne 0 ]; then
    echo "install_cpu_guard.sh must be run through sudo" >&2
    exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
source_helper="$script_dir/highambench_cpu_guard.py"
source_frontend="$script_dir/highambench_cpu_guard_frontend.py"
resources_script=$(readlink -f -- "$script_dir/../scripts/resources.py")
repository_root=$(CDPATH= cd -- "$script_dir/../.." && pwd -P)
python_executable="$repository_root/.venv/bin/python"
operator_name=${SUDO_USER:-}
allowed_cpus=$(tr -d '\n' < /sys/fs/cgroup/cpuset.cpus.effective)
maximum_slots=8
idle_sample_seconds=2.0
maximum_busy_percent=0.0

usage() {
    echo "usage: sudo sh $0 [--operator USER] [--allowed-cpus LIST] [--maximum-slots N]" >&2
    echo "       [--idle-sample-seconds N] [--maximum-busy-percent N]" >&2
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --operator)
            [ "$#" -ge 2 ] || { usage; exit 2; }
            operator_name=$2
            shift 2
            ;;
        --allowed-cpus)
            [ "$#" -ge 2 ] || { usage; exit 2; }
            allowed_cpus=$2
            shift 2
            ;;
        --maximum-slots)
            [ "$#" -ge 2 ] || { usage; exit 2; }
            maximum_slots=$2
            shift 2
            ;;
        --idle-sample-seconds)
            [ "$#" -ge 2 ] || { usage; exit 2; }
            idle_sample_seconds=$2
            shift 2
            ;;
        --maximum-busy-percent)
            [ "$#" -ge 2 ] || { usage; exit 2; }
            maximum_busy_percent=$2
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            usage
            exit 2
            ;;
    esac
done

[ -n "$operator_name" ] || {
    echo "cannot infer the non-root operator; pass --operator USER" >&2
    exit 2
}
case "$operator_name" in
    *[!A-Za-z0-9_.-]*|'') echo "invalid operator name" >&2; exit 2 ;;
    [Aa][Ll][Ll]) echo "reserved sudoers operator name is forbidden" >&2; exit 2 ;;
esac
case "$allowed_cpus" in
    *[!0-9,-]*|'') echo "invalid allowed CPU list" >&2; exit 2 ;;
esac
case "$maximum_slots" in
    *[!0-9]*|'') echo "invalid maximum slot count" >&2; exit 2 ;;
esac
[ "$maximum_slots" -ge 1 ] && [ "$maximum_slots" -le 64 ] || {
    echo "maximum slot count must be between 1 and 64" >&2
    exit 2
}
[ -f "$source_helper" ] && [ ! -L "$source_helper" ] \
    && [ -f "$source_frontend" ] && [ ! -L "$source_frontend" ] \
    && [ -f "$resources_script" ] && [ ! -L "$resources_script" ] \
    && [ -f "$python_executable" ] && [ -x "$python_executable" ] || {
    echo "regular helper, tracked resources.py, or project .venv Python is missing" >&2
    exit 2
}

operator_uid=$(id -u -- "$operator_name")
operator_gid=$(id -g -- "$operator_name")
case "$operator_uid:$operator_gid" in
    *[!0-9:]*|:*|*:) echo "cannot resolve numeric operator identity" >&2; exit 2 ;;
esac
[ "$operator_uid" -ne 0 ] || {
    echo "the benchmark operator must not be root" >&2
    exit 2
}

# Refuse to traverse a pre-existing symlink or an insecure managed directory.
ensure_managed_directory() {
    managed_path=$1
    managed_mode=$2
    /usr/bin/python3 -I -c '
import os, pathlib, stat, sys
path, expected = pathlib.Path(sys.argv[1]), int(sys.argv[2], 8)
current = pathlib.Path("/")
for component in path.parts[1:-1]:
    current /= component
    info = os.lstat(current)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise SystemExit(f"managed path traverses a non-directory or symlink: {current}")
    if info.st_uid != 0 or info.st_gid != 0 or stat.S_IMODE(info.st_mode) & 0o022:
        raise SystemExit(f"managed path traverses an insecure directory: {current}")
if os.path.lexists(path):
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise SystemExit(f"managed path is not a real directory: {path}")
    if info.st_uid != 0 or info.st_gid != 0 or stat.S_IMODE(info.st_mode) != expected:
        raise SystemExit(
            f"managed directory must be root:root mode {expected:04o}: {path}"
        )
' "$managed_path" "$managed_mode"
    if [ ! -e "$managed_path" ] && [ ! -L "$managed_path" ]; then
        install -d -o root -g root -m "$managed_mode" "$managed_path"
    fi
    /usr/bin/python3 -I -c '
import os, stat, sys
path, expected = sys.argv[1], int(sys.argv[2], 8)
info = os.lstat(path)
if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
    raise SystemExit(f"managed path is not a real directory: {path}")
if info.st_uid != 0 or info.st_gid != 0 or stat.S_IMODE(info.st_mode) != expected:
    raise SystemExit(f"managed directory must be root:root mode {expected:04o}: {path}")
' "$managed_path" "$managed_mode"
}

verify_secure_parent() {
    parent_path=$1
    /usr/bin/python3 -I -c '
import os, pathlib, stat, sys
path = pathlib.Path(sys.argv[1])
current = pathlib.Path("/")
for component in path.parts[1:]:
    current /= component
    info = os.lstat(current)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        raise SystemExit(f"installation path traverses a non-directory or symlink: {current}")
    if info.st_uid != 0 or info.st_gid != 0 or stat.S_IMODE(info.st_mode) & 0o022:
        raise SystemExit(f"installation path traverses an insecure directory: {current}")
' "$parent_path"
}

# Lock order is generation then campaign, matching frontend/host operations.
# The generation lock prevents an old loaded helper/config from resuming after
# replacement; the campaign lock proves no acquire/release/launch is active.
persistent_root=/var/lib/highambench-cpu-guard
ensure_managed_directory "$persistent_root" 0700
install_lock="$persistent_root/relay-install.lock"
if [ ! -e "$install_lock" ] && [ ! -L "$install_lock" ]; then
    (umask 077; : > "$install_lock")
fi
[ -f "$install_lock" ] && [ ! -L "$install_lock" ] || {
    echo "installation generation lock is not a regular non-symlink file" >&2
    exit 2
}
exec 8<> "$install_lock"
/usr/bin/python3 -I -c '
import os, stat, sys
path = sys.argv[1]
opened = os.fstat(8)
named = os.lstat(path)
if ((opened.st_dev, opened.st_ino) != (named.st_dev, named.st_ino)
        or not stat.S_ISREG(opened.st_mode)
        or opened.st_uid != 0 or opened.st_gid != 0
        or stat.S_IMODE(opened.st_mode) != 0o600 or opened.st_nlink != 1):
    raise SystemExit("installation generation lock is not root:root mode 0600")
' "$install_lock"
/usr/bin/flock --exclusive 8

runtime_root=/run/highambench-cpu-guard
ensure_managed_directory "$runtime_root" 0700
campaign_lock="$runtime_root/campaign.lock"
if [ -e "$campaign_lock" ] || [ -L "$campaign_lock" ]; then
    /usr/bin/python3 -I -c '
import os, stat, sys
info = os.lstat(sys.argv[1])
if (stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode)
        or info.st_uid != 0 or info.st_gid != 0
        or stat.S_IMODE(info.st_mode) != 0o600):
    raise SystemExit("campaign lock must be a root:root mode 0600 regular file")
' "$campaign_lock"
fi
exec 9<>"$campaign_lock"
chmod 0600 "$campaign_lock"
/usr/bin/flock --exclusive 9

temporary_root=$(mktemp -d /tmp/highambench-cpu-guard-install.XXXXXX)
transaction_tool="$temporary_root/install_transaction.py"
install_started=0
install_committed=0
journal_root="$persistent_root/install-transaction"

cleanup() {
    saved_status=$?
    trap - EXIT HUP INT TERM
    set +e
    if [ "$install_started" -eq 1 ] && [ "$install_committed" -ne 1 ]; then
        if recover_transaction; then
            echo "CPU-guard installation failed; the prior files were restored and verified" >&2
        else
            echo "CPU-guard installation failed and automatic rollback was not provably complete" >&2
            echo "durable recovery data was preserved at $journal_root" >&2
            saved_status=1
        fi
    fi
    rm -rf -- "$temporary_root"
    exit "$saved_status"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

# BEGIN TRANSACTION_PY
cat > "$transaction_tool" <<'PY'
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import re
import secrets
import shutil
import stat
import sys


JOURNAL_SCHEMA = 1
STATE_SCHEMA = 2
MAXIMUM_BYTES = 1_048_576
ROOT_UID = 0
ROOT_GID = 0
HELPER_DIRECTORY = "/usr/local/libexec/highambench"
CONFIG_DIRECTORY = "/etc/highambench"
SYSTEMD_DIRECTORY = "/etc/systemd/system"
SUDOERS_DIRECTORY = "/etc/sudoers.d"
HELPER = HELPER_DIRECTORY + "/highambench-cpu-guard"
HOST_HELPER = HELPER_DIRECTORY + "/highambench-cpu-guard-host"
CONFIG = CONFIG_DIRECTORY + "/cpu-guard.json"
PARENT_SLICE = SYSTEMD_DIRECTORY + "/highambench.slice"
SLOT_TEMPLATE = SYSTEMD_DIRECTORY + "/highambench-slot{}.slice"
SUDOERS_TEMPLATE = SUDOERS_DIRECTORY + "/highambench-cpu-guard-uid-{}"
SUDOERS_STEM = "highambench-cpu-guard"
SUDOERS_PREFIX = "highambench-cpu-guard-uid-"
CGROUP_GUARD_ROOT = "/sys/fs/cgroup/highambench.slice"
RUNTIME_SYSTEM_CONTROL = "/run/systemd/system.control"
PERSISTENT_SYSTEM_CONTROL = "/etc/systemd/system.control"
CONTROLLER_PIN = "highambench-cpuset-pin"
TRANSACTION_ID = re.compile(r"[0-9a-f]{32}")
SLOT_UNIT = re.compile(r"highambench-slot([0-9]+)[.]slice")
SUDOERS_UNIT = re.compile(r"highambench-cpu-guard-uid-([0-9]+)")


def fail(message: str) -> "None":
    raise SystemExit(message)


def strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def finite_float(value: str) -> float:
    result = float(value)
    if not math.isfinite(result):
        raise ValueError("non-finite JSON number")
    return result


def reject_constant(value: str) -> "None":
    raise ValueError(f"invalid JSON constant: {value}")


def strict_json(raw: bytes) -> object:
    if len(raw) > MAXIMUM_BYTES:
        raise ValueError("JSON document is oversized")
    return json.loads(
        raw.decode("utf-8"), object_pairs_hook=strict_object,
        parse_float=finite_float, parse_constant=reject_constant,
    )


def fsync_directory(path: str | Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def secure_directory(path: Path, exact_mode: int = 0o700) -> None:
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        fail(f"transaction path is not a real directory: {path}")
    if (info.st_uid != ROOT_UID or info.st_gid != ROOT_GID
            or stat.S_IMODE(info.st_mode) != exact_mode):
        fail(f"transaction directory is not root:root mode {exact_mode:04o}: {path}")


def read_regular(path: Path, mode: int | None = None) -> tuple[bytes, os.stat_result]:
    info = os.lstat(path)
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        fail(f"expected a regular non-symlink file: {path}")
    if info.st_uid != ROOT_UID or info.st_gid != ROOT_GID:
        fail(f"expected a root:root-owned file: {path}")
    if mode is not None and stat.S_IMODE(info.st_mode) != mode:
        fail(f"file has the wrong mode (expected {mode:04o}): {path}")
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino) != (info.st_dev, info.st_ino):
            fail(f"file changed while it was opened: {path}")
        chunks: list[bytes] = []
        size = 0
        while True:
            chunk = os.read(descriptor, 131_072)
            if not chunk:
                break
            size += len(chunk)
            if size > MAXIMUM_BYTES:
                fail(f"managed file is oversized: {path}")
            chunks.append(chunk)
        return b"".join(chunks), opened
    finally:
        os.close(descriptor)


def metadata(path: Path) -> dict[str, object] | None:
    if not os.path.lexists(path):
        return None
    raw, info = read_regular(path)
    return {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "mode": stat.S_IMODE(info.st_mode), "uid": info.st_uid, "gid": info.st_gid,
    }


def expected_metadata(path: Path, mode: int) -> dict[str, object]:
    raw, _ = read_regular(path)
    return {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "mode": mode, "uid": ROOT_UID, "gid": ROOT_GID,
    }


def validate_metadata(value: object, label: str) -> dict[str, object] | None:
    if value is None:
        return None
    if not isinstance(value, dict) or set(value) != {"sha256", "mode", "uid", "gid"}:
        fail(f"invalid {label} metadata in installation journal")
    digest, mode, uid, gid = (
        value.get("sha256"), value.get("mode"), value.get("uid"), value.get("gid")
    )
    if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        fail(f"invalid {label} digest in installation journal")
    for name, item in (("mode", mode), ("uid", uid), ("gid", gid)):
        if isinstance(item, bool) or not isinstance(item, int) or item < 0:
            fail(f"invalid {label} {name} in installation journal")
    if mode > 0o7777 or uid != ROOT_UID or gid != ROOT_GID:
        fail(f"unsafe {label} ownership or mode in installation journal")
    return value


def atomic_json(path: Path, value: object) -> None:
    temporary = path.parent / f".journal.{os.getpid()}.{secrets.token_hex(8)}"
    payload = (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()
    descriptor = -1
    try:
        descriptor = os.open(
            temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        os.replace(temporary, path)
        fsync_directory(path.parent)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def managed_destination(path: str, maximum_slots: int, operator_uid: int) -> bool:
    if path in {
        HELPER, HOST_HELPER, CONFIG, PARENT_SLICE,
        SUDOERS_TEMPLATE.format(operator_uid),
    }:
        return True
    slot = re.fullmatch(
        re.escape(SYSTEMD_DIRECTORY) + r"/highambench-slot([0-9]+)[.]slice", path
    )
    if slot is not None:
        return int(slot.group(1)) < maximum_slots
    return re.fullmatch(
        re.escape(SUDOERS_DIRECTORY) + r"/highambench-cpu-guard-uid-[0-9]+", path
    ) is not None


def load_journal(journal_root: Path) -> dict[str, object]:
    secure_directory(journal_root)
    secure_directory(journal_root / "backup")
    raw, _ = read_regular(journal_root / "journal.json", mode=0o600)
    try:
        value = strict_json(raw)
    except (UnicodeError, ValueError, json.JSONDecodeError) as error:
        fail(f"cannot parse durable installation journal: {error}")
    expected_keys = {
        "schema_version", "transaction_id", "maximum_slots", "operator_uid", "targets",
    }
    if not isinstance(value, dict) or set(value) != expected_keys:
        fail("durable installation journal has unexpected or missing keys")
    schema = value.get("schema_version")
    transaction_id = value.get("transaction_id")
    maximum_slots = value.get("maximum_slots")
    operator_uid = value.get("operator_uid")
    if isinstance(schema, bool) or not isinstance(schema, int) or schema != JOURNAL_SCHEMA:
        fail("unsupported durable installation journal schema")
    if not isinstance(transaction_id, str) or TRANSACTION_ID.fullmatch(transaction_id) is None:
        fail("invalid durable installation transaction identifier")
    if (isinstance(maximum_slots, bool) or not isinstance(maximum_slots, int)
            or not 1 <= maximum_slots <= 64):
        fail("invalid maximum slot count in installation journal")
    if isinstance(operator_uid, bool) or not isinstance(operator_uid, int) or operator_uid <= 0:
        fail("invalid operator UID in installation journal")
    targets = value.get("targets")
    if not isinstance(targets, list) or not targets:
        fail("installation journal has no targets")
    destinations: set[str] = set()
    backups: set[str] = set()
    required = {
        HELPER, HOST_HELPER, CONFIG, PARENT_SLICE,
        SUDOERS_TEMPLATE.format(operator_uid),
    }
    required.update(SLOT_TEMPLATE.format(index) for index in range(maximum_slots))
    for target in targets:
        if not isinstance(target, dict) or set(target) != {
            "destination", "backup", "prior", "intended",
        }:
            fail("invalid target record in installation journal")
        destination, backup = target.get("destination"), target.get("backup")
        if not isinstance(destination, str) or not managed_destination(
            destination, maximum_slots, operator_uid
        ):
            fail("installation journal contains an unmanaged destination")
        if destination in destinations:
            fail("installation journal repeats a destination")
        destinations.add(destination)
        if not isinstance(backup, str) or re.fullmatch(r"target-[0-9]{3}", backup) is None:
            fail("installation journal contains an invalid backup name")
        if backup in backups:
            fail("installation journal repeats a backup name")
        backups.add(backup)
        prior = validate_metadata(target.get("prior"), "prior")
        intended = validate_metadata(target.get("intended"), "intended")
        backup_path = journal_root / "backup" / backup
        if prior is not None:
            backup_raw, _ = read_regular(backup_path, mode=0o600)
            if hashlib.sha256(backup_raw).hexdigest() != prior.get("sha256"):
                fail(f"durable backup does not match its journal record: {destination}")
        elif os.path.lexists(backup_path):
            fail(f"unexpected durable backup for absent prior target: {destination}")
        if destination == SUDOERS_TEMPLATE.format(operator_uid):
            if intended is None or intended.get("mode") != 0o440:
                fail("current operator sudoers target is not an installation action")
        elif destination.startswith(SUDOERS_DIRECTORY + "/") and intended is not None:
            fail("stale operator sudoers target is not a removal action")
        elif destination in {HELPER, HOST_HELPER} and (
                intended is None or intended.get("mode") != 0o755):
            fail("helper target is not an executable installation action")
        elif destination == CONFIG and (intended is None or intended.get("mode") != 0o600):
            fail("config target is not a private installation action")
        elif (destination == PARENT_SLICE or destination.startswith(
                SYSTEMD_DIRECTORY + "/highambench-slot")) and (
                    intended is None or intended.get("mode") != 0o644):
            fail("slice target is not a mode 0644 installation action")
    if not required <= destinations:
        fail("installation journal omits a required target")
    value["targets"] = targets
    return value


def write_backup(source: Path, destination: Path, expected: dict[str, object]) -> None:
    source_descriptor = os.open(source, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    destination_descriptor = -1
    digest = hashlib.sha256()
    try:
        source_info = os.fstat(source_descriptor)
        if not stat.S_ISREG(source_info.st_mode):
            fail(f"backup source ceased to be regular: {source}")
        destination_descriptor = os.open(
            destination, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        while True:
            chunk = os.read(source_descriptor, 131_072)
            if not chunk:
                break
            digest.update(chunk)
            offset = 0
            while offset < len(chunk):
                offset += os.write(destination_descriptor, chunk[offset:])
        os.fsync(destination_descriptor)
    finally:
        os.close(source_descriptor)
        if destination_descriptor >= 0:
            os.close(destination_descriptor)
    if digest.hexdigest() != expected.get("sha256"):
        fail(f"backup source changed while it was copied: {source}")


def begin(journal_root: Path, stage: Path, maximum_slots: int, operator_uid: int, txid: str) -> None:
    if TRANSACTION_ID.fullmatch(txid) is None:
        fail("invalid new installation transaction identifier")
    if os.path.lexists(journal_root):
        fail("an installation transaction already exists")
    secure_directory(stage)
    replacements: dict[str, tuple[Path, int]] = {
        HELPER: (stage / "highambench-cpu-guard", 0o755),
        HOST_HELPER: (stage / "highambench-cpu-guard-host", 0o755),
        CONFIG: (stage / "cpu-guard.json", 0o600),
        PARENT_SLICE: (stage / "highambench.slice", 0o644),
        SUDOERS_TEMPLATE.format(operator_uid): (stage / "sudoers", 0o440),
    }
    for index in range(maximum_slots):
        replacements[SLOT_TEMPLATE.format(index)] = (
            stage / f"highambench-slot{index}.slice", 0o644,
        )
    for entry in os.scandir(SUDOERS_DIRECTORY):
        if not entry.name.startswith(SUDOERS_STEM):
            continue
        if SUDOERS_UNIT.fullmatch(entry.name) is None:
            fail(f"unexpected managed sudoers filename: {entry.path}")
        replacements.setdefault(entry.path, (Path(), 0))
    if len(replacements) > 256:
        fail("too many managed installation targets")
    targets: list[dict[str, object]] = []
    for index, destination_text in enumerate(sorted(replacements)):
        prior = metadata(Path(destination_text))
        staged, mode = replacements[destination_text]
        prior_mode = 0o440 if destination_text.startswith(SUDOERS_DIRECTORY + "/") else mode
        if prior is not None and prior.get("mode") != prior_mode:
            fail(
                f"managed target has unsafe mode; expected {prior_mode:04o}: "
                f"{destination_text}"
            )
        targets.append({
            "destination": destination_text,
            "backup": f"target-{index:03d}",
            "prior": prior,
            "intended": expected_metadata(staged, mode) if mode else None,
        })
    try:
        journal_root.mkdir(mode=0o700)
        secure_directory(journal_root)
        backup_root = journal_root / "backup"
        backup_root.mkdir(mode=0o700)
        for target in targets:
            if target["prior"] is not None:
                write_backup(
                    Path(str(target["destination"])),
                    backup_root / str(target["backup"]),
                    target["prior"],
                )
        fsync_directory(backup_root)
        # Prove the entire snapshot is still current before publishing it.
        for target in targets:
            if metadata(Path(str(target["destination"]))) != target["prior"]:
                fail(f"managed target changed during durable snapshot: {target['destination']}")
        atomic_json(journal_root / "journal.json", {
            "schema_version": JOURNAL_SCHEMA,
            "transaction_id": txid,
            "maximum_slots": maximum_slots,
            "operator_uid": operator_uid,
            "targets": targets,
        })
        fsync_directory(journal_root.parent)
    except BaseException:
        # Destinations are not mutated until begin() returns successfully.
        try:
            shutil.rmtree(journal_root)
            fsync_directory(journal_root.parent)
        except OSError:
            pass
        raise


def find_target(journal: dict[str, object], destination: str) -> dict[str, object]:
    for target in journal["targets"]:
        if target["destination"] == destination:
            return target
    fail(f"destination is not covered by durable transaction: {destination}")


def require_current(target: dict[str, object], field: str) -> None:
    if metadata(Path(str(target["destination"]))) != target[field]:
        fail(f"managed destination changed unexpectedly: {target['destination']}")


def temporary_destination(target: dict[str, object], transaction_id: str) -> Path:
    return Path(str(target["destination"]) + ".highambench-new-" + transaction_id)


def clear_temporary(path: Path) -> None:
    if not os.path.lexists(path):
        return
    info = os.lstat(path)
    if (stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode)
            or info.st_uid != ROOT_UID or info.st_gid != ROOT_GID):
        fail(f"refusing unexpected installation temporary: {path}")
    path.unlink()
    fsync_directory(path.parent)


def prepare_install(journal_root: Path, destination: str) -> Path:
    journal = load_journal(journal_root)
    target = find_target(journal, destination)
    if target["intended"] is None:
        fail(f"destination is a removal, not an installation: {destination}")
    require_current(target, "prior")
    temporary = temporary_destination(target, str(journal["transaction_id"]))
    clear_temporary(temporary)
    return temporary


def verify_temporary(journal_root: Path, destination: str, temporary_text: str) -> None:
    journal = load_journal(journal_root)
    target = find_target(journal, destination)
    temporary = temporary_destination(target, str(journal["transaction_id"]))
    if str(temporary) != temporary_text:
        fail("installer supplied the wrong temporary destination")
    descriptor = os.open(temporary, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    if metadata(temporary) != target["intended"]:
        fail(f"installation temporary does not match intended bytes: {destination}")


def replaced(journal_root: Path, destination: str) -> None:
    journal = load_journal(journal_root)
    target = find_target(journal, destination)
    fsync_directory(Path(destination).parent)
    require_current(target, "intended")


def prune_sudoers(journal_root: Path, retained: str) -> None:
    journal = load_journal(journal_root)
    expected_existing: set[str] = set()
    stale: list[dict[str, object]] = []
    for target in journal["targets"]:
        destination = str(target["destination"])
        if not destination.startswith(SUDOERS_DIRECTORY + "/"):
            continue
        if target["prior"] is not None:
            expected_existing.add(destination)
        if destination != retained:
            if target["intended"] is not None:
                fail("journal attempts to install a stale sudoers entry")
            stale.append(target)
    actual_existing: set[str] = set()
    for entry in os.scandir(SUDOERS_DIRECTORY):
        if not entry.name.startswith(SUDOERS_STEM):
            continue
        if SUDOERS_UNIT.fullmatch(entry.name) is None:
            fail(f"unexpected managed sudoers filename: {entry.path}")
        actual_existing.add(entry.path)
    if actual_existing != expected_existing:
        fail("managed sudoers files changed after the durable snapshot")
    for target in stale:
        require_current(target, "prior")
    for target in stale:
        Path(str(target["destination"])).unlink()
    if stale:
        fsync_directory(SUDOERS_DIRECTORY)


def copy_backup_atomic(journal_root: Path, target: dict[str, object], txid: str) -> None:
    destination = Path(str(target["destination"]))
    prior = target["prior"]
    if prior is None:
        if os.path.lexists(destination):
            info = os.lstat(destination)
            if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
                fail(f"refusing to remove unexpected rollback target: {destination}")
            destination.unlink()
            fsync_directory(destination.parent)
        return
    source = journal_root / "backup" / str(target["backup"])
    temporary = temporary_destination(target, txid)
    clear_temporary(temporary)
    source_descriptor = os.open(source, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    destination_descriptor = -1
    try:
        destination_descriptor = os.open(
            temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | os.O_NOFOLLOW,
            0o600,
        )
        while True:
            chunk = os.read(source_descriptor, 131_072)
            if not chunk:
                break
            offset = 0
            while offset < len(chunk):
                offset += os.write(destination_descriptor, chunk[offset:])
        os.fchown(destination_descriptor, int(prior["uid"]), int(prior["gid"]))
        os.fchmod(destination_descriptor, int(prior["mode"]))
        os.fsync(destination_descriptor)
    finally:
        os.close(source_descriptor)
        if destination_descriptor >= 0:
            os.close(destination_descriptor)
    if metadata(temporary) != prior:
        fail(f"rollback temporary failed verification: {destination}")
    os.replace(temporary, destination)
    fsync_directory(destination.parent)


def recover(journal_root: Path) -> str:
    secure_directory(journal_root)
    journal_path = journal_root / "journal.json"
    if not os.path.lexists(journal_path):
        # journal.json is published only before begin() returns, and the shell
        # mutates no destination until that return.
        shutil.rmtree(journal_root)
        fsync_directory(journal_root.parent)
        return "incomplete"
    journal = load_journal(journal_root)
    targets = journal["targets"]
    # Validate all targets before restoring the first, so an administrator or
    # package-manager edit is never silently overwritten.
    for target in targets:
        current = metadata(Path(str(target["destination"])))
        if current != target["prior"] and current != target["intended"]:
            fail(f"rollback target has unknown bytes: {target['destination']}")
    txid = str(journal["transaction_id"])
    for target in targets:
        copy_backup_atomic(journal_root, target, txid)
    for target in targets:
        require_current(target, "prior")
        clear_temporary(temporary_destination(target, txid))
    return "restored"


def verify_intended(journal_root: Path) -> None:
    journal = load_journal(journal_root)
    for target in journal["targets"]:
        require_current(target, "intended")
    operator_path = SUDOERS_TEMPLATE.format(journal["operator_uid"])
    managed_sudoers: set[str] = set()
    for entry in os.scandir(SUDOERS_DIRECTORY):
        if entry.name.startswith(SUDOERS_STEM):
            if SUDOERS_UNIT.fullmatch(entry.name) is None:
                fail(f"unexpected managed sudoers filename: {entry.path}")
            managed_sudoers.add(entry.path)
    if managed_sudoers != {operator_path}:
        fail("installation did not leave exactly one managed sudoers entry")


def finish(journal_root: Path) -> None:
    journal = load_journal(journal_root)
    completed = journal_root.parent / (
        ".install-transaction-complete-" + str(journal["transaction_id"])
    )
    if os.path.lexists(completed):
        fail(f"completed-transaction path already exists: {completed}")
    os.replace(journal_root, completed)
    fsync_directory(completed.parent)
    # The rename is the durable completion point; debris can be reclaimed later.
    try:
        shutil.rmtree(completed)
        fsync_directory(completed.parent)
    except OSError:
        pass


def cleanup_orphans(persistent_root: Path) -> None:
    secure_directory(persistent_root)
    for entry in os.scandir(persistent_root):
        if not entry.name.startswith(".install-transaction-complete-"):
            continue
        suffix = entry.name.removeprefix(".install-transaction-complete-")
        if TRANSACTION_ID.fullmatch(suffix) is None:
            fail(f"unexpected transaction artifact: {entry.path}")
        info = os.lstat(entry.path)
        if (stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
                or info.st_uid != ROOT_UID or info.st_gid != ROOT_GID):
            fail(f"unexpected completed-transaction artifact: {entry.path}")
        shutil.rmtree(entry.path)
        fsync_directory(persistent_root)
    patterns = (
        (Path(HELPER_DIRECTORY), re.compile(r"highambench-cpu-guard(?:-host)?[.]highambench-new-(?:[0-9a-f]{32}|[0-9]+)")),
        (Path(CONFIG_DIRECTORY), re.compile(r"cpu-guard[.]json[.]highambench-new-(?:[0-9a-f]{32}|[0-9]+)")),
        (Path(SYSTEMD_DIRECTORY), re.compile(r"highambench(?:-slot[0-9]+)?[.]slice[.]highambench-new-(?:[0-9a-f]{32}|[0-9]+)")),
        (Path(SUDOERS_DIRECTORY), re.compile(r"highambench-cpu-guard-uid-[0-9]+[.]highambench-new-(?:[0-9a-f]{32}|[0-9]+)")),
    )
    for directory, pattern in patterns:
        if not os.path.lexists(directory):
            continue
        info = os.lstat(directory)
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            fail(f"installation temporary parent is not a real directory: {directory}")
        for entry in os.scandir(directory):
            if pattern.fullmatch(entry.name) is not None:
                clear_temporary(Path(entry.path))


def parse_events(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    try:
        lines = path.read_text(encoding="ascii").splitlines()
    except OSError as error:
        fail(f"cannot read cgroup events at {path}: {error}")
    for line in lines:
        fields = line.split()
        if len(fields) != 2 or fields[0] in result:
            fail(f"malformed cgroup events at {path}")
        result[fields[0]] = fields[1]
    return result


def exact_inactive_state(state_path: Path) -> None:
    if not os.path.lexists(state_path):
        return
    raw, _ = read_regular(state_path, mode=0o600)
    try:
        value = strict_json(raw)
    except (UnicodeError, ValueError, json.JSONDecodeError) as error:
        fail(f"cannot prove inactive CPU-guard state: {error}")
    if not isinstance(value, dict):
        fail("CPU-guard state is not an object")
    schema = value.get("schema_version")
    generation = value.get("generation")
    if isinstance(generation, bool) or not isinstance(generation, int) or generation < 0:
        fail("CPU-guard state generation is invalid")
    if isinstance(schema, bool) or not isinstance(schema, int):
        fail("CPU-guard state schema is not an integer")
    if schema == 1:
        expected = {"schema_version", "generation", "active_lease", "baseline", "applied"}
        if set(value) != expected:
            fail("legacy CPU-guard state has unexpected or missing keys")
    elif schema == STATE_SCHEMA:
        expected = {
            "schema_version", "generation", "phase", "active_lease", "baseline", "applied",
        }
        if set(value) != expected:
            fail("CPU-guard state has unexpected or missing keys")
        if value.get("phase") != "inactive":
            fail("CPU-guard state is not in the inactive phase")
    else:
        fail("installer requires exact CPU-guard state schema 1 or 2")
    if any(value.get(key) is not None for key in ("active_lease", "baseline", "applied")):
        fail("inactive CPU-guard state retains transaction data")


def validate_cgroups(maximum_slots: int | None) -> None:
    root = Path(CGROUP_GUARD_ROOT)
    if not os.path.lexists(root):
        return
    root_info = os.lstat(root)
    if stat.S_ISLNK(root_info.st_mode) or not stat.S_ISDIR(root_info.st_mode):
        fail("VSCLReuse cgroup root is not a real directory")
    slots: list[Path] = []
    with os.scandir(root) as entries:
        for entry in entries:
            if entry.is_symlink():
                fail(f"VSCLReuse cgroup contains a symlink: {entry.path}")
            if not entry.is_dir(follow_symlinks=False):
                continue
            child = Path(entry.path)
            match = SLOT_UNIT.fullmatch(child.name)
            if match is None:
                fail(f"VSCLReuse cgroup has an unmanaged child: {child}")
            if maximum_slots is not None and int(match.group(1)) >= maximum_slots:
                fail(f"requested slot count would strand a stale cgroup: {child}")
            slots.append(child)
    directories = [root, *slots]
    for slot in slots:
        pin: Path | None = None
        with os.scandir(slot) as entries:
            for entry in entries:
                if entry.is_symlink():
                    fail(f"VSCLReuse slot contains a symlink: {entry.path}")
                if not entry.is_dir(follow_symlinks=False):
                    continue
                child = Path(entry.path)
                if child.name != CONTROLLER_PIN or pin is not None:
                    fail(f"VSCLReuse slot has an unmanaged child: {child}")
                pin = child
        if pin is None:
            continue
        info = os.lstat(pin)
        if (not stat.S_ISDIR(info.st_mode) or info.st_uid != ROOT_UID
                or info.st_gid != ROOT_GID or stat.S_IMODE(info.st_mode) != 0o755):
            fail(f"VSCLReuse controller pin is not root:root mode 0755: {pin}")
        with os.scandir(pin) as entries:
            nested = [entry.path for entry in entries
                      if entry.is_dir(follow_symlinks=False) or entry.is_symlink()]
        if nested:
            fail(f"VSCLReuse controller pin has a nested child: {nested[0]}")
        if (pin / "cgroup.type").read_text(encoding="ascii").strip() != "domain":
            fail(f"VSCLReuse controller pin is not a domain cgroup: {pin}")
        if (pin / "cgroup.procs").read_text(encoding="ascii").strip():
            fail(f"VSCLReuse controller pin contains a direct process: {pin}")
        if parse_events(pin / "cgroup.events").get("populated") != "0":
            fail(f"VSCLReuse controller pin is populated: {pin}")
        subtree = set(
            (pin / "cgroup.subtree_control").read_text(encoding="ascii").split()
        )
        if "cpuset" not in subtree:
            fail(f"VSCLReuse controller pin does not retain cpuset: {pin}")
        directories.append(pin)
    for directory in directories:
        if parse_events(directory / "cgroup.events").get("populated") != "0":
            fail(f"VSCLReuse cgroup is populated: {directory}")
        partition = directory / "cpuset.cpus.partition"
        if not partition.is_file():
            fail(f"cpuset partition state is unavailable: {directory}")
        if partition.read_text(encoding="ascii").strip() != "member":
            fail(f"VSCLReuse cgroup has an active or invalid partition: {directory}")


def validate_system_control(maximum_slots: int) -> None:
    persistent = Path(PERSISTENT_SYSTEM_CONTROL)
    if persistent.is_dir():
        with os.scandir(persistent) as entries:
            for entry in entries:
                if entry.name.startswith("highambench"):
                    fail(f"unexpected persistent VSCLReuse system-control override: {entry.path}")
    runtime = Path(RUNTIME_SYSTEM_CONTROL)
    if not runtime.is_dir():
        return
    with os.scandir(runtime) as entries:
        for entry in entries:
            if not entry.name.startswith("highambench"):
                continue
            unit_name = entry.name.removesuffix(".d")
            allowed_unit = unit_name == "highambench.slice"
            match = SLOT_UNIT.fullmatch(unit_name)
            if match is not None and int(match.group(1)) < maximum_slots:
                allowed_unit = True
            info = os.lstat(entry.path)
            if (not allowed_unit or not entry.name.endswith(".d")
                    or stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode)
                    or info.st_uid != ROOT_UID or info.st_gid != ROOT_GID
                    or stat.S_IMODE(info.st_mode) != 0o755):
                fail(f"unexpected VSCLReuse runtime system-control override: {entry.path}")
            with os.scandir(entry.path) as dropins:
                children = list(dropins)
            if len(children) != 1 or children[0].name != "50-AllowedCPUs.conf":
                fail(f"unexpected VSCLReuse runtime system-control drop-in: {entry.path}")
            path = Path(children[0].path)
            raw, file_info = read_regular(path, mode=0o644)
            del file_info
            try:
                lines = [line.strip() for line in raw.decode("utf-8").splitlines()
                         if line.strip() and not line.lstrip().startswith(("#", ";"))]
            except UnicodeError as error:
                fail(f"invalid VSCLReuse runtime AllowedCPUs drop-in: {path}: {error}")
            if lines != ["[Slice]", "AllowedCPUs="]:
                fail(f"VSCLReuse runtime AllowedCPUs override is not empty: {path}")


def validate_old_configuration(maximum_slots: int) -> None:
    path = Path(CONFIG)
    if not os.path.lexists(path):
        return
    raw, _ = read_regular(path, mode=0o600)
    try:
        value = strict_json(raw)
    except (UnicodeError, ValueError, json.JSONDecodeError) as error:
        fail(f"cannot validate installed CPU-guard configuration: {error}")
    if not isinstance(value, dict):
        fail("installed CPU-guard configuration is not an object")
    old_maximum = value.get("maximum_slots")
    if (isinstance(old_maximum, bool) or not isinstance(old_maximum, int)
            or not 1 <= old_maximum <= 64):
        fail("installed CPU-guard maximum_slots is invalid")
    if maximum_slots < old_maximum:
        fail(f"refusing slot shrink from {old_maximum} to {maximum_slots}")


def validate_unit_files(maximum_slots: int) -> None:
    directories = (
        Path("/etc/systemd/system"), Path("/run/systemd/system"),
        Path("/run/systemd/transient"), Path("/usr/local/lib/systemd/system"),
        Path("/usr/lib/systemd/system"), Path("/lib/systemd/system"),
    )
    for directory in directories:
        if not directory.is_dir():
            continue
        for entry in os.scandir(directory):
            if not entry.name.startswith("highambench"):
                continue
            allowed = False
            if directory == Path("/etc/systemd/system"):
                if entry.name == "highambench.slice":
                    allowed = True
                else:
                    match = SLOT_UNIT.fullmatch(entry.name)
                    if match is not None:
                        if int(match.group(1)) >= maximum_slots:
                            fail(f"requested slot count would strand a stale unit: {entry.path}")
                        allowed = True
            if not allowed:
                fail(f"unexpected VSCLReuse systemd unit or drop-in: {entry.path}")
            info = os.lstat(entry.path)
            if (stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode)
                    or info.st_uid != ROOT_UID or info.st_gid != ROOT_GID):
                fail(f"managed systemd unit is not a root:root regular file: {entry.path}")


def preflight(runtime_root: Path, maximum_slots: int | None) -> None:
    secure_directory(runtime_root)
    exact_inactive_state(runtime_root / "state.json")
    validate_cgroups(maximum_slots)
    if maximum_slots is not None:
        validate_old_configuration(maximum_slots)
        validate_unit_files(maximum_slots)
        validate_system_control(maximum_slots)


def positive_integer(raw: str, label: str, maximum: int | None = None) -> int:
    if re.fullmatch(r"[0-9]+", raw) is None:
        fail(f"invalid {label}")
    value = int(raw)
    if value <= 0 or maximum is not None and value > maximum:
        fail(f"invalid {label}")
    return value


def main(arguments: list[str]) -> None:
    if not arguments:
        fail("missing installer transaction command")
    command, *items = arguments
    if command == "preflight-runtime" and len(items) == 1:
        preflight(Path(items[0]), None)
    elif command == "preflight-full" and len(items) == 2:
        preflight(Path(items[0]), positive_integer(items[1], "maximum slots", 64))
    elif command == "begin" and len(items) == 5:
        begin(Path(items[0]), Path(items[1]),
              positive_integer(items[2], "maximum slots", 64),
              positive_integer(items[3], "operator UID"), items[4])
    elif command == "prepare-install" and len(items) == 2:
        print(prepare_install(Path(items[0]), items[1]))
    elif command == "verify-temporary" and len(items) == 3:
        verify_temporary(Path(items[0]), items[1], items[2])
    elif command == "replaced" and len(items) == 2:
        replaced(Path(items[0]), items[1])
    elif command == "clear-temporary" and len(items) == 2:
        journal = load_journal(Path(items[0]))
        target = find_target(journal, items[1])
        clear_temporary(temporary_destination(target, str(journal["transaction_id"])))
    elif command == "prune-sudoers" and len(items) == 2:
        prune_sudoers(Path(items[0]), items[1])
    elif command == "recover" and len(items) == 1:
        print(recover(Path(items[0])))
    elif command == "verify-intended" and len(items) == 1:
        verify_intended(Path(items[0]))
    elif command == "finish" and len(items) == 1:
        finish(Path(items[0]))
    elif command == "cleanup-orphans" and len(items) == 1:
        cleanup_orphans(Path(items[0]))
    else:
        fail("invalid installer transaction command")


if __name__ == "__main__":
    main(sys.argv[1:])
PY
# END TRANSACTION_PY
chmod 0700 "$transaction_tool"

run_transaction() {
    /usr/bin/python3 -I "$transaction_tool" "$@"
}

verify_secure_parent /etc/systemd/system
verify_secure_parent /etc/sudoers.d

# Recovery is allowed only after the exact inactive state and whole managed
# cgroup hierarchy prove inactive. It restores only bytes known to the journal.
run_transaction preflight-runtime "$runtime_root"

recover_transaction() {
    if [ ! -e "$journal_root" ] && [ ! -L "$journal_root" ]; then
        return 0
    fi
    recovery_result=$(run_transaction recover "$journal_root") || return 1
    case "$recovery_result" in
        incomplete)
            return 0
            ;;
        restored)
            /usr/bin/systemctl daemon-reload >/dev/null 2>&1 || return 1
            /usr/sbin/visudo -cf /etc/sudoers >/dev/null 2>&1 || return 1
            run_transaction finish "$journal_root" || return 1
            return 0
            ;;
        *)
            echo "unexpected installation recovery result" >&2
            return 1
            ;;
    esac
}

if [ -e "$journal_root" ] || [ -L "$journal_root" ]; then
    recover_transaction || {
        echo "cannot safely recover the previous CPU-guard installation" >&2
        echo "durable recovery data remains at $journal_root" >&2
        exit 2
    }
    echo "recovered an interrupted CPU-guard installation" >&2
fi
run_transaction cleanup-orphans "$persistent_root"

# Recovery may change installed files, so check shrink/stale unit state after it.
run_transaction preflight-full "$runtime_root" "$maximum_slots"

ensure_managed_directory /usr/local/libexec 0755
ensure_managed_directory /usr/local/libexec/highambench 0755
ensure_managed_directory /etc/highambench 0755
verify_secure_parent /usr/local/libexec/highambench
verify_secure_parent /etc/highambench

# Stage and validate every replacement before publishing the durable journal.
install -o root -g root -m 0755 "$source_frontend" "$temporary_root/highambench-cpu-guard"
install -o root -g root -m 0755 "$source_helper" "$temporary_root/highambench-cpu-guard-host"
helper_digest=$(sha256sum "$temporary_root/highambench-cpu-guard" | awk '{print $1}')

/usr/bin/python3 -I -c '
import json, pathlib, sys
target = pathlib.Path(sys.argv[1])
value = {
    "schema_version": 1,
    "operator_uid": int(sys.argv[2]), "run_uid": int(sys.argv[2]),
    "run_gid": int(sys.argv[3]), "python_executable": sys.argv[4],
    "resources_script": sys.argv[5], "allowed_cpus": sys.argv[6],
    "physical_cores_per_slot": 4, "maximum_slots": int(sys.argv[7]),
    "idle_sample_seconds": float(sys.argv[8]),
    "maximum_busy_percent": float(sys.argv[9]),
}
target.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8")
' "$temporary_root/cpu-guard.json" "$operator_uid" "$operator_gid" \
  "$python_executable" "$resources_script" "$allowed_cpus" "$maximum_slots" \
  "$idle_sample_seconds" "$maximum_busy_percent"
chmod 0600 "$temporary_root/cpu-guard.json"

{
    echo '[Unit]'
    echo 'Description=VSCLReuse exclusive CPU partition parent'
    echo
    echo '[Slice]'
    echo 'CPUAccounting=yes'
} > "$temporary_root/highambench.slice"
chmod 0644 "$temporary_root/highambench.slice"

slot_index=0
while [ "$slot_index" -lt "$maximum_slots" ]; do
    {
        echo '[Unit]'
        echo "Description=VSCLReuse measured CPU slot $slot_index"
        echo 'Requires=highambench.slice'
        echo 'After=highambench.slice'
        echo
        echo '[Slice]'
        echo 'CPUAccounting=yes'
    } > "$temporary_root/highambench-slot$slot_index.slice"
    chmod 0644 "$temporary_root/highambench-slot$slot_index.slice"
    slot_index=$((slot_index + 1))
done

sudoers_path="/etc/sudoers.d/highambench-cpu-guard-uid-$operator_uid"
{
    echo "# Narrow VSCLReuse CPU-partition interface for $operator_name"
    echo "\"$operator_name\" ALL=(root) NOPASSWD:NOSETENV: sha256:$helper_digest /usr/local/libexec/highambench/highambench-cpu-guard *"
} > "$temporary_root/sudoers"
chmod 0440 "$temporary_root/sudoers"
/usr/sbin/visudo -cf "$temporary_root/sudoers" >/dev/null

/usr/bin/python3 -I -c '
# BEGIN STAGED_GUARD_VALIDATION_PY
import importlib.machinery, importlib.util, pathlib, sys
helper = pathlib.Path(sys.argv[1])
name = "_highambench_installer_guard"
# The installed executable intentionally has no .py suffix.  Automatic
# spec discovery therefore returns None; identify the already-authenticated
# staged regular file explicitly as Python source.
loader = importlib.machinery.SourceFileLoader(name, str(helper))
spec = importlib.util.spec_from_file_location(name, helper, loader=loader)
if spec is None or spec.loader is None:
    raise SystemExit("cannot load staged CPU guard")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
value = module._strict_json_loads(pathlib.Path(sys.argv[2]).read_text(encoding="utf-8"))
if not isinstance(value, dict):
    raise SystemExit("staged CPU-guard configuration is not an object")
module.Configuration.from_mapping(value)
# END STAGED_GUARD_VALIDATION_PY
' "$temporary_root/highambench-cpu-guard-host" "$temporary_root/cpu-guard.json"

transaction_id=$(/usr/bin/python3 -I -c 'import secrets; print(secrets.token_hex(16))')
run_transaction begin "$journal_root" "$temporary_root" "$maximum_slots" \
    "$operator_uid" "$transaction_id"
install_started=1

atomic_install() {
    source=$1
    destination=$2
    mode=$3
    staged_destination=$(run_transaction prepare-install "$journal_root" "$destination")
    if ! install -o root -g root -m "$mode" "$source" "$staged_destination"; then
        run_transaction clear-temporary "$journal_root" "$destination" || true
        return 1
    fi
    if ! run_transaction verify-temporary "$journal_root" "$destination" "$staged_destination"; then
        run_transaction clear-temporary "$journal_root" "$destination" || true
        return 1
    fi
    if ! mv -fT -- "$staged_destination" "$destination"; then
        run_transaction clear-temporary "$journal_root" "$destination" || true
        return 1
    fi
    run_transaction replaced "$journal_root" "$destination"
}

atomic_install "$temporary_root/highambench-cpu-guard" \
    /usr/local/libexec/highambench/highambench-cpu-guard 0755
atomic_install "$temporary_root/highambench-cpu-guard-host" \
    /usr/local/libexec/highambench/highambench-cpu-guard-host 0755
atomic_install "$temporary_root/cpu-guard.json" \
    /etc/highambench/cpu-guard.json 0600
atomic_install "$temporary_root/highambench.slice" \
    /etc/systemd/system/highambench.slice 0644
slot_index=0
while [ "$slot_index" -lt "$maximum_slots" ]; do
    atomic_install "$temporary_root/highambench-slot$slot_index.slice" \
        "/etc/systemd/system/highambench-slot$slot_index.slice" 0644
    slot_index=$((slot_index + 1))
done
/usr/bin/systemctl daemon-reload

# The staged host implementation and configuration were loaded and validated
# before publication.  A frontend status relay cannot be run while this
# installer correctly holds the exclusive generation lock; the first operator
# status call after exit performs the host-namespace/live-layout attestation.

# Remove every stale UID-specific authorization and publish the one exact
# digest-bearing sudoers entry last, all within the same durable transaction.
run_transaction prune-sudoers "$journal_root" "$sudoers_path"
atomic_install "$temporary_root/sudoers" "$sudoers_path" 0440
/usr/sbin/visudo -cf /etc/sudoers >/dev/null
run_transaction verify-intended "$journal_root"

# Renaming the journal is the durable commit point. Before it, the next run
# rolls back; after it, only safely reclaimable backup debris can remain.
run_transaction finish "$journal_root"
install_committed=1

echo "installed VSCLReuse CPU guard for $operator_name"
echo "allowed CPUs: $allowed_cpus; maximum parallel slots: $maximum_slots"
