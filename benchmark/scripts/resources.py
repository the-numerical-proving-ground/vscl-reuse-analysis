#!/usr/bin/env python3
"""Fail-closed CPU and memory isolation for VSCLReuse workers.

The production path always enters a transient user service, fixes scheduler
affinity, prevents the worker from changing that affinity, and verifies the
resulting controls from inside that service before executing the worker.  The
service delegates only the memory controller so that the runner can cap the
attempt manager at 1 GiB and give the attempt an exact 16-GiB limit and fresh
lifetime ``memory.peak`` even on kernels whose peak file is read-only. Each N
or L attempt has an independent service and resource slot.

Only Python's standard library is used so that this module can run during
machine preflight before a benchmark environment is prepared.
"""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import datetime as dt
import errno
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import secrets
import shlex
import shutil
import stat
import subprocess
import sys
import time
from typing import Any, Callable, Iterable, Mapping, Sequence


SCHEMA_VERSION = 2
PHYSICAL_CORES_PER_SLOT = 4
MEMORY_MAX_BYTES = 16 * 1024**3
MANAGER_MEMORY_MAX_BYTES = 1 * 1024**3
MEMORY_SWAP_MAX_BYTES = 0
COORDINATOR_MEMORY_MAX = "max"

SYS_ROOT = Path("/sys")
PROC_ROOT = Path("/proc")
CPU_SYSFS_ROOT = SYS_ROOT / "devices/system/cpu"

_UNIT_NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:@-]{0,180}$")
_CONDITION_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$")
_CPU_GUARD_SLICE = "highambench.slice"
_CPU_GUARD_SLOT_SLICE_RE = re.compile(r"^highambench-slot([0-9]+)\.slice$")
_CPU_GUARD_SERVICE_RE = re.compile(r"^highambench-[A-Za-z0-9_.:@-]+\.service$")
_CACHE_SIZE_RE = re.compile(r"^(\d+)([KMGTPE]?)B?$", re.IGNORECASE)
_MOUNT_ESCAPE_RE = re.compile(r"\\([0-7]{3})")
_DELEGATED_ROOT_ENV = "HIGHAMBENCH_DELEGATED_MEMORY_CGROUP"
_MANAGER_CGROUP_NAME = "manager"
_WORKER_CGROUP_RE = re.compile(
    r"^(?:manager|condition-[A-Za-z0-9_.-]{1,64}-[0-9a-f]{16})$"
)
_CGROUP_EMPTY_TIMEOUT_SECONDS = 5.0
_CGROUP_POLL_SECONDS = 0.01
_CGROUP_RECLAIM_TIMEOUT_SECONDS = 5.0
_RECLAIMABLE_MEMORY_STAT_KEYS = ("anon", "file", "shmem")

# Optional, stable CPU-class capabilities.  These distinguish heterogeneous
# core classes even when two classes happen to expose the same SMT width and
# L1/L2 cache shape.  Runtime policy/current-frequency files and ACPI CPPC
# values are deliberately excluded: firmware may update or round those values
# independently per logical CPU, so they are not a stable physical-core key.
_CORE_CLASS_FILES = {
    "sysfs_core_type": "topology/core_type",
    "cpu_capacity": "cpu_capacity",
    "cpuinfo_min_freq_khz": "cpufreq/cpuinfo_min_freq",
    "cpuinfo_max_freq_khz": "cpufreq/cpuinfo_max_freq",
    "base_frequency_khz": "cpufreq/base_frequency",
}


class ResourceIsolationError(RuntimeError):
    """A hardware inventory or resource-isolation contract failed."""


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def _canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _read_text(path: Path, *, label: str | None = None) -> str:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError as error:
        raise ResourceIsolationError(
            f"cannot read {label or str(path)}: {error}"
        ) from error


def _optional_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def _read_int(path: Path, *, label: str | None = None) -> int:
    raw = _read_text(path, label=label)
    try:
        return int(raw)
    except ValueError as error:
        raise ResourceIsolationError(
            f"{label or str(path)} is not an integer: {raw!r}"
        ) from error


def _core_class_indicators(cpu_root: Path, cpu: int) -> dict[str, str]:
    """Read immutable/nominal core-class indicators exposed for one CPU."""

    base = cpu_root / f"cpu{cpu}"
    result: dict[str, str] = {}
    for name, relative in _CORE_CLASS_FILES.items():
        value = _optional_text(base / relative)
        if value is not None:
            result[name] = value
    return result


def parse_cpu_list(raw: str) -> tuple[int, ...]:
    """Parse Linux cpulist syntax into a sorted, duplicate-free tuple."""

    value = raw.strip()
    if not value:
        return ()
    cpus: set[int] = set()
    for item in value.split(","):
        part = item.strip()
        if not part:
            raise ResourceIsolationError(f"invalid empty cpulist item in {raw!r}")
        if "-" in part:
            bounds = part.split("-")
            if len(bounds) != 2:
                raise ResourceIsolationError(f"invalid CPU range {part!r}")
            try:
                first, last = (int(bound) for bound in bounds)
            except ValueError as error:
                raise ResourceIsolationError(f"invalid CPU range {part!r}") from error
            if first < 0 or last < first:
                raise ResourceIsolationError(f"invalid CPU range {part!r}")
            cpus.update(range(first, last + 1))
        else:
            try:
                cpu = int(part)
            except ValueError as error:
                raise ResourceIsolationError(f"invalid CPU number {part!r}") from error
            if cpu < 0:
                raise ResourceIsolationError(f"invalid CPU number {part!r}")
            cpus.add(cpu)
    return tuple(sorted(cpus))


def format_cpu_list(cpus: Iterable[int]) -> str:
    """Render a CPU set in canonical Linux cpulist syntax."""

    ordered = sorted(set(cpus))
    if not ordered:
        raise ResourceIsolationError("a CPU set cannot be empty")
    if ordered[0] < 0:
        raise ResourceIsolationError("CPU numbers cannot be negative")
    ranges: list[str] = []
    start = previous = ordered[0]
    for cpu in ordered[1:]:
        if cpu == previous + 1:
            previous = cpu
            continue
        ranges.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = cpu
    ranges.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(ranges)


def _parse_cache_size(raw: str, *, path: Path) -> int:
    match = _CACHE_SIZE_RE.fullmatch(raw.strip())
    if match is None:
        raise ResourceIsolationError(f"unsupported cache size in {path}: {raw!r}")
    amount = int(match.group(1))
    unit = match.group(2).upper()
    powers = {"": 0, "K": 1, "M": 2, "G": 3, "T": 4, "P": 5, "E": 6}
    return amount * 1024 ** powers[unit]


def _cpu_identity(cpu_root: Path, cpu: int) -> tuple[int, int, int]:
    topology = cpu_root / f"cpu{cpu}" / "topology"
    package_id = _read_int(topology / "physical_package_id")
    die_raw = _optional_text(topology / "die_id")
    die_id = int(die_raw) if die_raw is not None else 0
    core_id = _read_int(topology / "core_id")
    return package_id, die_id, core_id


def _cache_signature_for_cpu(
    cpu_root: Path,
    cpu: int,
    *,
    online_cpus: set[int],
    identity_by_cpu: Mapping[int, tuple[int, int, int]],
    core_siblings: set[int],
) -> tuple[dict[str, object], ...]:
    cache_root = cpu_root / f"cpu{cpu}" / "cache"
    descriptors: list[dict[str, object]] = []
    for index_path in sorted(
        cache_root.glob("index*"),
        key=lambda path: int(path.name.removeprefix("index")),
    ):
        level = _read_int(index_path / "level")
        if level not in (1, 2):
            continue
        cache_type = _read_text(index_path / "type").lower()
        shared_all = set(
            parse_cpu_list(_read_text(index_path / "shared_cpu_list"))
        )
        if cpu not in shared_all:
            raise ResourceIsolationError(
                f"cache {index_path} does not include its CPU {cpu}"
            )
        shared_online = shared_all & online_cpus
        shared_identities: set[tuple[int, int, int]] = set()
        for shared_cpu in shared_online:
            identity = identity_by_cpu.get(shared_cpu)
            if identity is None:
                identity = _cpu_identity(cpu_root, shared_cpu)
            shared_identities.add(identity)
        descriptor: dict[str, object] = {
            "level": level,
            "type": cache_type,
            "size_bytes": _parse_cache_size(
                _read_text(index_path / "size"), path=index_path / "size"
            ),
            "coherency_line_size_bytes": _read_int(
                index_path / "coherency_line_size"
            ),
            "number_of_sets": _read_int(index_path / "number_of_sets"),
            "ways_of_associativity": _read_int(
                index_path / "ways_of_associativity"
            ),
            "physical_line_partition": _read_int(
                index_path / "physical_line_partition"
            ),
            # Counts and relationships describe topology without embedding CPU,
            # package, die, core, cache-index, or cache-instance identifiers.
            "shared_hardware_logical_cpu_count": len(shared_all),
            "shared_online_logical_cpu_count": len(shared_online),
            "shared_online_physical_core_count": len(shared_identities),
            "shared_with_exactly_one_physical_core": len(shared_identities) == 1,
            "shared_with_this_core_siblings_only": shared_online == core_siblings,
        }
        for optional_name in ("allocation_policy", "write_policy"):
            optional_value = _optional_text(index_path / optional_name)
            if optional_value is not None:
                descriptor[optional_name] = optional_value.lower()
        descriptors.append(descriptor)
    levels = {int(item["level"]) for item in descriptors}
    if levels != {1, 2}:
        raise ResourceIsolationError(
            f"CPU {cpu} does not expose a complete L1/L2 cache topology"
        )
    descriptors.sort(key=_canonical_json)
    return tuple(descriptors)


@dataclass(frozen=True)
class PhysicalCore:
    package_id: int
    die_id: int
    core_id: int
    logical_cpus: tuple[int, ...]
    sysfs_core_type: str | None
    cpu_capacity: str | None
    type_signature: Mapping[str, object]
    type_key: str

    @property
    def identity(self) -> tuple[int, int, int]:
        return self.package_id, self.die_id, self.core_id

    def to_json(self) -> dict[str, object]:
        return {
            "package_id": self.package_id,
            "die_id": self.die_id,
            "core_id": self.core_id,
            "logical_cpus": list(self.logical_cpus),
            "sysfs_core_type": self.sysfs_core_type,
            "cpu_capacity": self.cpu_capacity,
            "type_key": self.type_key,
            "type_signature": dict(self.type_signature),
        }


@dataclass(frozen=True)
class CpuInventory:
    allowed_cpus: tuple[int, ...]
    online_cpus: tuple[int, ...]
    present_cpus: tuple[int, ...]
    possible_cpus: tuple[int, ...]
    cores: tuple[PhysicalCore, ...]
    excluded_partial_cores: tuple[Mapping[str, object], ...]
    logical_cpu_records: tuple[Mapping[str, object], ...]

    def groups_by_type(self) -> dict[str, tuple[PhysicalCore, ...]]:
        groups: dict[str, list[PhysicalCore]] = {}
        for core in self.cores:
            groups.setdefault(core.type_key, []).append(core)
        return {
            key: tuple(sorted(value, key=lambda core: core.identity))
            for key, value in sorted(groups.items())
        }

    def to_json(self) -> dict[str, object]:
        groups = self.groups_by_type()
        return {
            "allowed_cpus": list(self.allowed_cpus),
            "allowed_cpu_list": format_cpu_list(self.allowed_cpus),
            "online_cpus": list(self.online_cpus),
            "present_cpus": list(self.present_cpus),
            "possible_cpus": list(self.possible_cpus),
            "eligible_physical_core_count": len(self.cores),
            "eligible_cores": [core.to_json() for core in self.cores],
            "excluded_partial_cores": [dict(item) for item in self.excluded_partial_cores],
            "logical_cpu_records": [dict(item) for item in self.logical_cpu_records],
            "homogeneous_type_groups": {
                key: {
                    "physical_core_count": len(cores),
                    "physical_core_identities": [
                        {
                            "package_id": core.package_id,
                            "die_id": core.die_id,
                            "core_id": core.core_id,
                        }
                        for core in cores
                    ],
                    "type_signature": dict(cores[0].type_signature),
                }
                for key, cores in groups.items()
            },
        }


def inventory_cpu_topology(
    *,
    cpu_root: Path = CPU_SYSFS_ROOT,
    allowed_cpus: Iterable[int] | None = None,
) -> CpuInventory:
    """Inventory complete physical cores available to this process.

    A physical core is eligible only when every online hardware thread is in
    the process affinity mask.  Partially available cores are logged but never
    allocated.  Homogeneous type keys are derived solely from SMT width and
    normalized L1/L2 cache characteristics/topology, and stable core-class
    capability indicators.  Exact CPU/core/cache identifiers and mutable
    current-frequency policy do not affect matching.
    """

    online = set(parse_cpu_list(_read_text(cpu_root / "online")))
    present_raw = _optional_text(cpu_root / "present")
    possible_raw = _optional_text(cpu_root / "possible")
    present = set(parse_cpu_list(present_raw)) if present_raw else set(online)
    possible = set(parse_cpu_list(possible_raw)) if possible_raw else set(present)
    allowed = (
        set(os.sched_getaffinity(0))
        if allowed_cpus is None
        else {int(cpu) for cpu in allowed_cpus}
    )
    if not allowed:
        raise ResourceIsolationError("the process has no allowed CPUs")
    unavailable = allowed - online
    if unavailable:
        raise ResourceIsolationError(
            "the affinity mask contains offline CPUs: " + format_cpu_list(unavailable)
        )

    identity_by_cpu: dict[int, tuple[int, int, int]] = {}
    siblings_by_cpu: dict[int, set[int]] = {}
    class_indicators_by_cpu: dict[int, dict[str, str]] = {}
    records: list[dict[str, object]] = []
    for cpu in sorted(online):
        identity = _cpu_identity(cpu_root, cpu)
        topology_root = cpu_root / f"cpu{cpu}" / "topology"
        siblings = set(
            parse_cpu_list(_read_text(topology_root / "thread_siblings_list"))
        )
        if cpu not in siblings:
            raise ResourceIsolationError(
                f"CPU {cpu} is absent from its thread_siblings_list"
            )
        identity_by_cpu[cpu] = identity
        siblings_by_cpu[cpu] = siblings
        class_indicators = _core_class_indicators(cpu_root, cpu)
        class_indicators_by_cpu[cpu] = class_indicators
        records.append(
            {
                "cpu": cpu,
                "allowed": cpu in allowed,
                "package_id": identity[0],
                "die_id": identity[1],
                "core_id": identity[2],
                "thread_siblings": sorted(siblings),
                "core_class_indicators": class_indicators,
                "sysfs_core_type": class_indicators.get("sysfs_core_type"),
                "cpu_capacity": class_indicators.get("cpu_capacity"),
            }
        )

    cpus_by_identity: dict[tuple[int, int, int], set[int]] = {}
    for cpu, identity in identity_by_cpu.items():
        cpus_by_identity.setdefault(identity, set()).add(cpu)

    cores: list[PhysicalCore] = []
    excluded: list[dict[str, object]] = []
    for identity, online_siblings in sorted(cpus_by_identity.items()):
        declared_sets = {tuple(sorted(siblings_by_cpu[cpu])) for cpu in online_siblings}
        if len(declared_sets) != 1:
            raise ResourceIsolationError(
                f"inconsistent sibling topology for physical core {identity}"
            )
        declared_siblings = set(next(iter(declared_sets)))
        if declared_siblings != online_siblings:
            reason = (
                "offline_or_missing_sibling"
                if declared_siblings - online
                else "inconsistent_core_identity"
            )
            if online_siblings & allowed:
                excluded.append(
                    {
                        "package_id": identity[0],
                        "die_id": identity[1],
                        "core_id": identity[2],
                        "online_logical_cpus": sorted(online_siblings),
                        "declared_thread_siblings": sorted(declared_siblings),
                        "allowed_logical_cpus": sorted(online_siblings & allowed),
                        "reason": reason,
                    }
                )
            continue
        if not online_siblings <= allowed:
            if online_siblings & allowed:
                excluded.append(
                    {
                        "package_id": identity[0],
                        "die_id": identity[1],
                        "core_id": identity[2],
                        "online_logical_cpus": sorted(online_siblings),
                        "declared_thread_siblings": sorted(declared_siblings),
                        "allowed_logical_cpus": sorted(online_siblings & allowed),
                        "reason": "partial_affinity",
                    }
                )
            continue

        representative = min(online_siblings)
        cache_signatures = {
            _canonical_json(
                _cache_signature_for_cpu(
                    cpu_root,
                    cpu,
                    online_cpus=online,
                    identity_by_cpu=identity_by_cpu,
                    core_siblings=online_siblings,
                )
            )
            for cpu in online_siblings
        }
        if len(cache_signatures) != 1:
            raise ResourceIsolationError(
                f"logical siblings disagree on L1/L2 topology for core {identity}"
            )
        caches = json.loads(next(iter(cache_signatures)))
        class_signatures = {
            _canonical_json(class_indicators_by_cpu[cpu])
            for cpu in online_siblings
        }
        if len(class_signatures) != 1:
            raise ResourceIsolationError(
                f"logical siblings disagree on core-class capabilities for core {identity}"
            )
        class_indicators = json.loads(next(iter(class_signatures)))
        signature: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "smt_width": len(online_siblings),
            "l1_l2_cache_topology": caches,
            "core_class_indicators": class_indicators,
        }
        signature_json = _canonical_json(signature)
        topology_root = cpu_root / f"cpu{representative}" / "topology"
        cores.append(
            PhysicalCore(
                package_id=identity[0],
                die_id=identity[1],
                core_id=identity[2],
                logical_cpus=tuple(sorted(online_siblings)),
                sysfs_core_type=class_indicators.get("sysfs_core_type"),
                cpu_capacity=class_indicators.get("cpu_capacity"),
                type_signature=signature,
                type_key=_sha256_text(signature_json),
            )
        )

    if not cores:
        raise ResourceIsolationError(
            "the affinity mask contains no complete physical cores with L1/L2 topology"
        )
    return CpuInventory(
        allowed_cpus=tuple(sorted(allowed)),
        online_cpus=tuple(sorted(online)),
        present_cpus=tuple(sorted(present)),
        possible_cpus=tuple(sorted(possible)),
        cores=tuple(sorted(cores, key=lambda core: core.identity)),
        excluded_partial_cores=tuple(excluded),
        logical_cpu_records=tuple(records),
    )


@dataclass(frozen=True)
class ResourceSlot:
    index: int
    cores: tuple[PhysicalCore, ...]
    logical_cpus: tuple[int, ...]
    type_key: str
    type_signature: Mapping[str, object]

    def to_json(self) -> dict[str, object]:
        return {
            "slot_index": self.index,
            "physical_core_count": len(self.cores),
            "logical_cpus": list(self.logical_cpus),
            "cpu_list": format_cpu_list(self.logical_cpus),
            "type_key": self.type_key,
            "type_signature": dict(self.type_signature),
            "cores": [core.to_json() for core in self.cores],
            "memory_max_bytes": MEMORY_MAX_BYTES,
            "memory_swap_max_bytes": MEMORY_SWAP_MAX_BYTES,
        }


def allocate_resource_slots(
    inventory: CpuInventory,
    *,
    slot_count: int | None = None,
    profile_id: str | None = None,
    reserve_physical_cores: int = 1,
    slot_offset: int = 0,
) -> tuple[ResourceSlot, ...]:
    """Allocate slots while leaving complete host cores outside the reservation."""

    if slot_count is not None and slot_count <= 0:
        raise ResourceIsolationError("slot_count must be positive")
    if slot_offset < 0:
        raise ResourceIsolationError("slot_offset must be nonnegative")
    if reserve_physical_cores < 0:
        raise ResourceIsolationError("reserve_physical_cores must be nonnegative")
    groups = inventory.groups_by_type()
    if profile_id is not None and profile_id not in groups:
        raise ResourceIsolationError(
            f"unknown homogeneous CPU profile: {profile_id}"
        )
    host_capacity = max(
        0,
        (len(inventory.cores) - reserve_physical_cores)
        // PHYSICAL_CORES_PER_SLOT,
    )
    candidates = [
        (
            min(len(cores) // PHYSICAL_CORES_PER_SLOT, host_capacity),
            key,
            cores,
        )
        for key, cores in groups.items()
        if host_capacity >= 1
        and len(cores) >= PHYSICAL_CORES_PER_SLOT
        and (profile_id is None or key == profile_id)
    ]
    if slot_count is not None:
        candidates = [item for item in candidates if item[0] >= slot_offset + slot_count]
    else:
        candidates = [item for item in candidates if item[0] > slot_offset]
    if not candidates:
        requested = slot_count if slot_count is not None else 1
        raise ResourceIsolationError(
            f"no homogeneous CPU type can supply {requested} disjoint slot(s) of "
            f"{PHYSICAL_CORES_PER_SLOT} physical cores while leaving "
            f"{reserve_physical_cores} complete host core(s) unreserved"
        )
    # Prefer the type with the greatest concurrency.  The key provides a stable
    # tie-break without relying on exact CPU/core identifiers.
    capacity, type_key, selected = sorted(
        candidates, key=lambda item: (-item[0], item[1])
    )[0]
    number = capacity - slot_offset if slot_count is None else slot_count
    slots: list[ResourceSlot] = []
    consumed: set[int] = set()
    for index in range(number):
        first = (slot_offset + index) * PHYSICAL_CORES_PER_SLOT
        cores = selected[first : first + PHYSICAL_CORES_PER_SLOT]
        logical_cpus = tuple(
            sorted(cpu for core in cores for cpu in core.logical_cpus)
        )
        overlap = consumed & set(logical_cpus)
        if overlap:
            raise ResourceIsolationError(
                "internal slot allocation overlap: " + format_cpu_list(overlap)
            )
        consumed.update(logical_cpus)
        slots.append(
            ResourceSlot(
                index=index,
                cores=tuple(cores),
                logical_cpus=logical_cpus,
                type_key=type_key,
                type_signature=cores[0].type_signature,
            )
        )
    return tuple(slots)


def _core_from_json(value: Mapping[str, object]) -> PhysicalCore:
    try:
        type_signature = value["type_signature"]
        if not isinstance(type_signature, Mapping):
            raise TypeError("type_signature is not an object")
        logical_cpus = tuple(int(cpu) for cpu in value["logical_cpus"])  # type: ignore[arg-type]
        return PhysicalCore(
            package_id=int(value["package_id"]),
            die_id=int(value["die_id"]),
            core_id=int(value["core_id"]),
            logical_cpus=logical_cpus,
            sysfs_core_type=(
                None
                if value.get("sysfs_core_type") is None
                else str(value["sysfs_core_type"])
            ),
            cpu_capacity=(
                None if value.get("cpu_capacity") is None else str(value["cpu_capacity"])
            ),
            type_signature=dict(type_signature),
            type_key=str(value["type_key"]),
        )
    except (KeyError, TypeError, ValueError) as error:
        raise ResourceIsolationError(f"invalid physical-core record: {error}") from error


def _inventory_from_public(value: Mapping[str, object]) -> CpuInventory:
    """Rehydrate the JSON-safe object returned by :func:`inventory_host`."""

    inventory_value: object = value
    try:
        hardware = value.get("hardware")
        if isinstance(hardware, Mapping):
            cpu = hardware.get("cpu")
            if isinstance(cpu, Mapping) and isinstance(cpu.get("inventory"), Mapping):
                inventory_value = cpu["inventory"]
        if not isinstance(inventory_value, Mapping):
            raise TypeError("inventory is not an object")
        return CpuInventory(
            allowed_cpus=tuple(  # type: ignore[arg-type]
                int(cpu) for cpu in inventory_value["allowed_cpus"]
            ),
            online_cpus=tuple(  # type: ignore[arg-type]
                int(cpu) for cpu in inventory_value["online_cpus"]
            ),
            present_cpus=tuple(  # type: ignore[arg-type]
                int(cpu) for cpu in inventory_value["present_cpus"]
            ),
            possible_cpus=tuple(  # type: ignore[arg-type]
                int(cpu) for cpu in inventory_value["possible_cpus"]
            ),
            cores=tuple(
                _core_from_json(core)
                for core in inventory_value["eligible_cores"]  # type: ignore[index,union-attr]
                if isinstance(core, Mapping)
            ),
            excluded_partial_cores=tuple(
                dict(item)
                for item in inventory_value.get(  # type: ignore[union-attr]
                    "excluded_partial_cores", []
                )
                if isinstance(item, Mapping)
            ),
            logical_cpu_records=tuple(
                dict(item)
                for item in inventory_value.get(  # type: ignore[union-attr]
                    "logical_cpu_records", []
                )
                if isinstance(item, Mapping)
            ),
        )
    except (KeyError, TypeError, ValueError) as error:
        raise ResourceIsolationError(f"invalid public CPU inventory: {error}") from error


def _slot_from_public(value: ResourceSlot | Mapping[str, object]) -> ResourceSlot:
    if isinstance(value, ResourceSlot):
        _validate_slot(value)
        return value
    try:
        signature = value["type_signature"]
        if not isinstance(signature, Mapping):
            raise TypeError("type_signature is not an object")
        slot = ResourceSlot(
            index=int(value["slot_index"]),
            cores=tuple(
                _core_from_json(core)
                for core in value["cores"]  # type: ignore[index]
                if isinstance(core, Mapping)
            ),
            logical_cpus=tuple(int(cpu) for cpu in value["logical_cpus"]),  # type: ignore[arg-type]
            type_key=str(value.get("profile_id", value["type_key"])),
            type_signature=dict(signature),
        )
    except (KeyError, TypeError, ValueError) as error:
        raise ResourceIsolationError(f"invalid resource-slot record: {error}") from error
    _validate_slot(slot)
    return slot


def inventory_host(
    *, allowed_cpus: Iterable[int] | None = None
) -> dict[str, object]:
    """Return the JSON-safe host inventory for an explicit or current CPU set."""

    inventory = inventory_cpu_topology(allowed_cpus=allowed_cpus)
    return collect_host_facts(inventory)


def allocate_slots(
    inventory: Mapping[str, object],
    jobs: int | None = None,
    profile_id: str | None = None,
    *,
    reserve_physical_cores: int = 1,
    slot_offset: int = 0,
) -> list[dict[str, object]]:
    """Public orchestrator API for homogeneous, disjoint four-core slots."""

    hydrated = _inventory_from_public(inventory)
    slots = allocate_resource_slots(
        hydrated,
        slot_count=jobs,
        profile_id=profile_id,
        reserve_physical_cores=reserve_physical_cores,
        slot_offset=slot_offset,
    )
    result: list[dict[str, object]] = []
    for slot in slots:
        record = slot.to_json()
        record["profile_id"] = slot.type_key
        result.append(record)
    return result


def _decode_mount_field(value: str) -> str:
    return _MOUNT_ESCAPE_RE.sub(lambda match: chr(int(match.group(1), 8)), value)


@dataclass(frozen=True)
class CgroupLocation:
    membership_path: str
    mount_root: Path
    mount_point: Path
    directory: Path

    def to_json(self) -> dict[str, str]:
        return {
            "membership_path": self.membership_path,
            "mount_root": str(self.mount_root),
            "mount_point": str(self.mount_point),
            "directory": str(self.directory),
        }


def _unified_membership(proc_root: Path) -> str:
    raw = _read_text(proc_root / "self/cgroup", label="/proc/self/cgroup")
    memberships: list[str] = []
    unexpected: list[str] = []
    for line in raw.splitlines():
        parts = line.split(":", 2)
        if len(parts) != 3:
            raise ResourceIsolationError(f"invalid cgroup membership line: {line!r}")
        hierarchy, controllers, path = parts
        if hierarchy == "0" and controllers == "":
            memberships.append(path)
        else:
            unexpected.append(line)
    if len(memberships) != 1 or unexpected:
        raise ResourceIsolationError(
            "a single unified cgroup-v2 membership is required"
        )
    membership = memberships[0]
    pure = PurePosixPath(membership)
    if not pure.is_absolute() or ".." in pure.parts:
        raise ResourceIsolationError(f"unsafe cgroup membership path: {membership!r}")
    return membership


def _cgroup2_mounts(proc_root: Path) -> list[tuple[Path, Path]]:
    raw = _read_text(proc_root / "self/mountinfo", label="/proc/self/mountinfo")
    mounts: list[tuple[Path, Path]] = []
    for line in raw.splitlines():
        before, separator, after = line.partition(" - ")
        if not separator:
            continue
        trailing = after.split()
        fields = before.split()
        if len(fields) < 6 or not trailing or trailing[0] != "cgroup2":
            continue
        mount_root = Path(_decode_mount_field(fields[3]))
        mount_point = Path(_decode_mount_field(fields[4]))
        mounts.append((mount_root, mount_point))
    return mounts


def _relative_posix_path(path: str, root: Path) -> Path | None:
    pure_path = PurePosixPath(path)
    pure_root = PurePosixPath(str(root))
    try:
        relative = pure_path.relative_to(pure_root)
    except ValueError:
        return None
    return Path(*relative.parts)


def _resolve_current_cgroup(proc_root: Path) -> CgroupLocation:
    membership = _unified_membership(proc_root)
    candidates: list[CgroupLocation] = []
    for mount_root, mount_point in _cgroup2_mounts(proc_root):
        relative = _relative_posix_path(membership, mount_root)
        if relative is None:
            continue
        directory = mount_point.joinpath(relative)
        if directory.is_dir():
            candidates.append(
                CgroupLocation(
                    membership_path=membership,
                    mount_root=mount_root,
                    mount_point=mount_point,
                    directory=directory,
                )
            )
    if len(candidates) != 1:
        raise ResourceIsolationError(
            f"cannot prove one current cgroup-v2 directory (found {len(candidates)})"
        )
    return candidates[0]


_CGROUP_SNAPSHOT_FILES = (
    "cgroup.controllers",
    "cgroup.events",
    "cgroup.freeze",
    "cgroup.procs",
    "cgroup.stat",
    "cgroup.subtree_control",
    "cgroup.type",
    "cpu.max",
    "cpu.stat",
    "cpuset.cpus",
    "cpuset.cpus.effective",
    "cpuset.cpus.partition",
    "cpuset.mems",
    "cpuset.mems.effective",
    "memory.current",
    "memory.events",
    "memory.events.local",
    "memory.high",
    "memory.low",
    "memory.max",
    "memory.min",
    "memory.numa_stat",
    "memory.oom.group",
    "memory.peak",
    "memory.stat",
    "memory.swap.current",
    "memory.swap.events",
    "memory.swap.high",
    "memory.swap.max",
)


def _snapshot_cgroup(directory: Path) -> dict[str, str | None]:
    return {
        name: _optional_text(directory / name) for name in _CGROUP_SNAPSHOT_FILES
    }


def _parse_limit(raw: str | None, *, name: str) -> int | None:
    if raw is None:
        raise ResourceIsolationError(f"cgroup proof is missing {name}")
    if raw == "max":
        return None
    try:
        value = int(raw)
    except ValueError as error:
        raise ResourceIsolationError(f"invalid cgroup {name}: {raw!r}") from error
    if value < 0:
        raise ResourceIsolationError(f"invalid cgroup {name}: {raw!r}")
    return value


def _ancestor_memory_limits(location: CgroupLocation) -> list[dict[str, object]]:
    """Snapshot every memory-controlled ancestor below the cgroup-v2 mount.

    A cgroup-v2 mount root itself commonly has no ``memory.max``/``memory.high``
    files.  Descendant cgroups do, so the authenticated chain ends at the
    mount's direct child; its parent relation still proves that the recorded
    mount point was reached.
    """

    limits: list[dict[str, object]] = []
    current = location.directory
    while current != location.mount_point:
        try:
            current.relative_to(location.mount_point)
        except ValueError as error:
            raise ResourceIsolationError(
                "current cgroup escaped its cgroup-v2 mount"
            ) from error
        raw = _optional_text(current / "memory.max")
        high_raw = _optional_text(current / "memory.high")
        if raw is None or high_raw is None:
            raise ResourceIsolationError(
                f"cgroup proof is missing memory.max/memory.high in {current}"
            )
        limits.append(
            {
                "directory": str(current),
                "memory_max_raw": raw,
                "memory_max_bytes": _parse_limit(raw, name="memory.max"),
                "memory_high_raw": high_raw,
                "memory_high_bytes": _parse_limit(high_raw, name="memory.high"),
            }
        )
        parent = current.parent
        if parent == current:
            raise ResourceIsolationError("cgroup mount was not reached")
        current = parent
    if not limits:
        raise ResourceIsolationError(
            "worker cgroup cannot be the cgroup-v2 mount root"
        )
    return limits


def _probe_locked_affinity(
    actual: set[int],
    affinity_writer: Callable[[Iterable[int]], None],
) -> dict[str, object]:
    """Prove that the inherited seccomp policy rejects affinity changes.

    Setting the already-observed mask is deliberately harmless when the filter
    is absent, so a successful call is unambiguous evidence that the production
    lock was not installed.  ``EPERM`` is the configured systemd failure mode.
    """

    try:
        affinity_writer(tuple(sorted(actual)))
    except OSError as error:
        if error.errno != errno.EPERM:
            raise ResourceIsolationError(
                "sched_setaffinity lock probe failed with an unexpected errno: "
                f"{error.errno}"
            ) from error
        return {
            "attempted_cpu_list": format_cpu_list(actual),
            "blocked": True,
            "errno": errno.EPERM,
            "errno_name": "EPERM",
        }
    raise ResourceIsolationError(
        "sched_setaffinity unexpectedly succeeded; the affinity lock is absent"
    )


def _cpuset_record(directory: Path) -> dict[str, object]:
    """Authenticate one cpuset directory without trusting a supplied path."""

    requested_raw = _read_text(
        directory / "cpuset.cpus", label=f"{directory} cpuset.cpus"
    )
    effective_raw = _read_text(
        directory / "cpuset.cpus.effective",
        label=f"{directory} cpuset.cpus.effective",
    )
    partition = _read_text(
        directory / "cpuset.cpus.partition",
        label=f"{directory} cpuset.cpus.partition",
    )
    requested = parse_cpu_list(requested_raw)
    effective = parse_cpu_list(effective_raw)
    identity = _cgroup_directory_identity(directory)
    return {
        **identity,
        "cpuset_cpus": requested_raw,
        "cpuset_cpus_parsed": list(requested),
        "cpuset_cpus_effective": effective_raw,
        "cpuset_cpus_effective_parsed": list(effective),
        "cpuset_cpus_partition": partition,
    }


def _verify_cpu_partition(
    location: CgroupLocation, expected: set[int]
) -> dict[str, object]:
    """Prove the worker is inside its exact root-owned VSCLReuse slot.

    The system CPU guard owns the first two cgroup levels.  The campaign slice
    owns the union and each child slot partition owns one exact four-core CPU
    set.  A scheduler-affinity mask alone is not evidence of exclusivity, so
    production verification authenticates both partition ancestors and the
    worker's effective cpuset directly from cgroup v2.
    """

    try:
        relative = location.directory.relative_to(location.mount_point)
    except ValueError as error:
        raise ResourceIsolationError(
            "worker cgroup is outside its cgroup-v2 mount"
        ) from error
    parts = relative.parts
    if (
        len(parts) != 4
        or parts[0] != _CPU_GUARD_SLICE
        or _CPU_GUARD_SLOT_SLICE_RE.fullmatch(parts[1]) is None
        or _CPU_GUARD_SERVICE_RE.fullmatch(parts[2]) is None
        or _WORKER_CGROUP_RE.fullmatch(parts[3]) is None
    ):
        raise ResourceIsolationError(
            "worker cgroup is not beneath the root-owned VSCLReuse slot partition"
        )

    campaign_directory = location.mount_point / parts[0]
    slot_directory = campaign_directory / parts[1]
    service_directory = slot_directory / parts[2]
    campaign = _cpuset_record(campaign_directory)
    slot = _cpuset_record(slot_directory)
    service_effective_raw = _read_text(
        service_directory / "cpuset.cpus.effective",
        label="service cpuset.cpus.effective",
    )
    service_effective = set(parse_cpu_list(service_effective_raw))
    campaign_requested = set(campaign["cpuset_cpus_parsed"])
    slot_requested = set(slot["cpuset_cpus_parsed"])
    slot_effective = set(slot["cpuset_cpus_effective_parsed"])
    if campaign["cpuset_cpus_partition"] != "root":
        raise ResourceIsolationError(
            "VSCLReuse campaign union is not a cpuset partition root"
        )
    if not expected <= campaign_requested:
        raise ResourceIsolationError(
            "VSCLReuse campaign partition does not own the worker CPUs"
        )
    if slot["cpuset_cpus_partition"] != "root":
        raise ResourceIsolationError(
            "VSCLReuse worker slot is not a cpuset partition root"
        )
    if slot_requested != expected or slot_effective != expected:
        raise ResourceIsolationError(
            "VSCLReuse slot cpuset does not exactly match the worker CPUs"
        )
    if service_effective != expected:
        raise ResourceIsolationError(
            "service cpuset.cpus.effective does not exactly match its slot"
        )
    return {
        "verified": True,
        "mode": "root",
        "campaign_partition": campaign,
        "slot_partition": slot,
        "service_cgroup": _cgroup_directory_identity(service_directory),
        "worker_cgroup": _cgroup_directory_identity(location.directory),
        "service_cpuset_cpus_effective": service_effective_raw,
        "service_cpuset_cpus_effective_parsed": sorted(service_effective),
    }


def _verify_resource_contract(
    expected_cpus: Iterable[int],
    *,
    expected_memory_bytes: int,
    proc_root: Path,
    affinity_reader: Callable[[], Iterable[int]],
    affinity_writer: Callable[[Iterable[int]], None],
) -> dict[str, object]:
    expected = set(expected_cpus)
    if not expected:
        raise ResourceIsolationError("expected CPU affinity cannot be empty")
    actual = set(affinity_reader())
    if actual != expected:
        raise ResourceIsolationError(
            "worker affinity mismatch: expected "
            f"{format_cpu_list(expected)}, observed {format_cpu_list(actual)}"
        )
    affinity_lock = _probe_locked_affinity(actual, affinity_writer)

    location = _resolve_current_cgroup(proc_root)
    cpu_partition = _verify_cpu_partition(location, expected)
    snapshot = _snapshot_cgroup(location.directory)
    memory_max = _parse_limit(snapshot["memory.max"], name="memory.max")
    swap_max = _parse_limit(snapshot["memory.swap.max"], name="memory.swap.max")
    if expected_memory_bytes not in (MEMORY_MAX_BYTES, MANAGER_MEMORY_MAX_BYTES):
        raise ResourceIsolationError(
            f"unsupported worker memory contract: {expected_memory_bytes} bytes"
        )
    if memory_max != expected_memory_bytes:
        raise ResourceIsolationError(
            f"memory.max must be exactly {expected_memory_bytes}, observed "
            f"{snapshot['memory.max']!r}"
        )
    if swap_max != MEMORY_SWAP_MAX_BYTES:
        raise ResourceIsolationError(
            f"memory.swap.max must be 0, observed {snapshot['memory.swap.max']!r}"
        )
    if snapshot["memory.oom.group"] != "1":
        raise ResourceIsolationError(
            "memory.oom.group must be exactly 1, observed "
            f"{snapshot['memory.oom.group']!r}"
        )
    if snapshot["memory.high"] != COORDINATOR_MEMORY_MAX:
        raise ResourceIsolationError(
            "memory.high must be nonbinding, observed "
            f"{snapshot['memory.high']!r}"
        )

    ancestor_limits = _ancestor_memory_limits(location)
    if (
        len(ancestor_limits) < 2
        or ancestor_limits[1].get("directory") != str(location.directory.parent)
        or ancestor_limits[1].get("memory_max_raw") != COORDINATOR_MEMORY_MAX
        or ancestor_limits[1].get("memory_max_bytes") is not None
    ):
        raise ResourceIsolationError(
            "the immediate coordinator cgroup must be uncapped so one "
            "condition cannot reduce the next condition's headroom"
        )
    parent_controls = _exact_memory_controls(
        location.directory.parent,
        label="coordinator cgroup",
        expected_memory_max=COORDINATOR_MEMORY_MAX,
    )
    binding_ancestors = [
        item
        for item in ancestor_limits[1:]
        if item["memory_max_raw"] != COORDINATOR_MEMORY_MAX
        or item["memory_high_raw"] != COORDINATOR_MEMORY_MAX
    ]
    if binding_ancestors:
        raise ResourceIsolationError(
            "every condition ancestor must have nonbinding memory.max and "
            "memory.high controls"
        )
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-resource-proof",
        "verified": True,
        "verified_at": _utc_now(),
        "pid": os.getpid(),
        "expected": {
            "physical_cores_per_slot": PHYSICAL_CORES_PER_SLOT,
            "logical_cpus": sorted(expected),
            "cpu_list": format_cpu_list(expected),
            "memory_max_bytes": expected_memory_bytes,
            "memory_swap_max_bytes": MEMORY_SWAP_MAX_BYTES,
            "memory_oom_group": True,
            "affinity_change_errno": "EPERM",
            "cpuset_effective_cpu_list": format_cpu_list(expected),
            "cpuset_partition_mode": "root",
        },
        "observed": {
            "sched_getaffinity": sorted(actual),
            "sched_setaffinity_probe": affinity_lock,
            "cgroup": location.to_json(),
            "cgroup_files": snapshot,
            "cpu_partition": cpu_partition,
            "pair_parent_cgroup": _cgroup_directory_identity(
                location.directory.parent
            ),
            "pair_parent_memory_controls": parent_controls,
            "ancestor_memory_limits": ancestor_limits,
        },
    }


def verify_resource_contract(
    expected_cpus: Iterable[int],
    *,
    expected_memory_bytes: int = MEMORY_MAX_BYTES,
) -> dict[str, object]:
    """Verify the production worker contract using kernel-owned paths only."""

    return _verify_resource_contract(
        expected_cpus,
        expected_memory_bytes=expected_memory_bytes,
        proc_root=PROC_ROOT,
        affinity_reader=lambda: os.sched_getaffinity(0),
        affinity_writer=lambda cpus: os.sched_setaffinity(0, cpus),
    )


def verify_resource_contract_for_test(
    expected_cpus: Iterable[int],
    *,
    proc_root: Path,
    observed_affinity: Iterable[int],
    expected_memory_bytes: int = MEMORY_MAX_BYTES,
    affinity_writer: Callable[[Iterable[int]], None] | None = None,
) -> dict[str, object]:
    """Exercise verification against a fixture; never used by production CLI."""

    frozen_affinity = tuple(observed_affinity)

    def blocked_writer(_cpus: Iterable[int]) -> None:
        raise PermissionError(errno.EPERM, "fixture affinity lock")

    return _verify_resource_contract(
        expected_cpus,
        expected_memory_bytes=expected_memory_bytes,
        proc_root=proc_root,
        affinity_reader=lambda: frozen_affinity,
        affinity_writer=affinity_writer or blocked_writer,
    )


def verify_current_worker(
    slot: ResourceSlot | Mapping[str, object],
    expected_memory_bytes: int = MEMORY_MAX_BYTES,
) -> dict[str, object]:
    """Public orchestrator API for fail-closed in-worker kernel verification."""

    if expected_memory_bytes not in (MEMORY_MAX_BYTES, MANAGER_MEMORY_MAX_BYTES):
        raise ResourceIsolationError(
            "the production worker memory contract must be the exact manager "
            f"({MANAGER_MEMORY_MAX_BYTES}) or condition ({MEMORY_MAX_BYTES}) limit"
        )
    hydrated = _slot_from_public(slot)
    return verify_resource_contract(
        hydrated.logical_cpus,
        expected_memory_bytes=expected_memory_bytes,
    )


def _write_cgroup_value(path: Path, value: str, *, label: str) -> None:
    """Write one cgroup control without following links or creating files."""

    flags = os.O_WRONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        fd = os.open(path, flags)
    except OSError as error:
        raise ResourceIsolationError(f"cannot open {label} for writing: {error}") from error
    payload = (value + "\n").encode("ascii")
    try:
        written = os.write(fd, payload)
        if written != len(payload):
            raise ResourceIsolationError(f"short write to {label}")
    except OSError as error:
        raise ResourceIsolationError(f"cannot write {label}: {error}") from error
    finally:
        try:
            os.close(fd)
        except OSError as error:
            raise ResourceIsolationError(f"cannot close {label}: {error}") from error


def _cgroup_directory_identity(directory: Path) -> dict[str, object]:
    try:
        metadata = directory.stat(follow_symlinks=False)
    except OSError as error:
        raise ResourceIsolationError(
            f"cannot stat cgroup directory {directory}: {error}"
        ) from error
    if not stat.S_ISDIR(metadata.st_mode) or directory.is_symlink():
        raise ResourceIsolationError(f"cgroup path is not a real directory: {directory}")
    return {
        "directory": str(directory),
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
    }


def _same_cgroup_identity(
    directory: Path, expected: Mapping[str, object]
) -> bool:
    actual = _cgroup_directory_identity(directory)
    return (
        actual["directory"] == expected.get("directory")
        and actual["device"] == expected.get("device")
        and actual["inode"] == expected.get("inode")
    )


def _parse_keyed_cgroup_integers(raw: str | None, *, label: str) -> dict[str, int]:
    if raw is None:
        raise ResourceIsolationError(f"cgroup proof is missing {label}")
    result: dict[str, int] = {}
    for line in raw.splitlines():
        fields = line.split()
        if len(fields) != 2 or fields[0] in result:
            raise ResourceIsolationError(f"invalid {label}: {raw!r}")
        try:
            value = int(fields[1])
        except ValueError as error:
            raise ResourceIsolationError(f"invalid {label}: {raw!r}") from error
        if value < 0:
            raise ResourceIsolationError(f"invalid {label}: {raw!r}")
        result[fields[0]] = value
    if not result:
        raise ResourceIsolationError(f"empty {label}")
    return result


def _cgroup_is_populated(directory: Path) -> bool:
    events = _parse_keyed_cgroup_integers(
        _optional_text(directory / "cgroup.events"), label="cgroup.events"
    )
    populated = events.get("populated")
    if populated not in (0, 1):
        raise ResourceIsolationError("cgroup.events lacks a boolean populated field")
    return populated == 1


def _wait_for_empty_cgroup(
    directory: Path, *, timeout_seconds: float = _CGROUP_EMPTY_TIMEOUT_SECONDS
) -> bool:
    deadline = time.monotonic() + timeout_seconds
    while True:
        if not _cgroup_is_populated(directory):
            return True
        if time.monotonic() >= deadline:
            return False
        time.sleep(_CGROUP_POLL_SECONDS)


def _reclaimable_memory_stat(directory: Path) -> dict[str, int]:
    values = _parse_keyed_cgroup_integers(
        _optional_text(directory / "memory.stat"), label="memory.stat"
    )
    missing = [key for key in _RECLAIMABLE_MEMORY_STAT_KEYS if key not in values]
    if missing:
        raise ResourceIsolationError(
            f"memory.stat lacks reclaim accounting: {', '.join(missing)}"
        )
    return {key: values[key] for key in _RECLAIMABLE_MEMORY_STAT_KEYS}


def _request_memory_reclaim(path: Path, requested_bytes: int) -> str | None:
    """Request numeric memcg reclaim; EAGAIN means a valid partial reclaim."""

    if requested_bytes <= 0:
        raise ResourceIsolationError("memory reclaim request must be positive")
    flags = os.O_WRONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise ResourceIsolationError(
            f"cannot open condition memory.reclaim: {error}"
        ) from error
    try:
        payload = f"{requested_bytes}\n".encode("ascii")
        try:
            written = os.write(descriptor, payload)
        except OSError as error:
            if error.errno == errno.EAGAIN:
                return "EAGAIN"
            raise ResourceIsolationError(
                f"condition memory.reclaim failed: {error}"
            ) from error
        if written != len(payload):
            raise ResourceIsolationError("condition memory.reclaim write was partial")
        return None
    finally:
        os.close(descriptor)


def _best_effort_condition_reclaim(
    directory: Path,
    *,
    timeout_seconds: float = _CGROUP_RECLAIM_TIMEOUT_SECONDS,
) -> dict[str, object]:
    """Drop condition-owned cache before cgroup removal when the kernel can.

    Linux may retain a few KiB of kernel accounting and may return ``EAGAIN``
    after performing a partial reclaim.  Neither is a quota problem because
    the coordinator parent is nonbinding, so this routine records rather than
    demands exact zero.
    """

    reclaim_path = directory / "memory.reclaim"
    try:
        status = reclaim_path.stat()
    except OSError as error:
        raise ResourceIsolationError(
            f"condition memory.reclaim is unavailable: {error}"
        ) from error
    if not stat.S_ISREG(status.st_mode):
        raise ResourceIsolationError("condition memory.reclaim is not a file")
    before_current = _parse_limit(
        _optional_text(directory / "memory.current"), name="condition memory.current"
    )
    if before_current is None:
        raise ResourceIsolationError("condition memory.current cannot be max")
    before_stat = _reclaimable_memory_stat(directory)
    attempts = 0
    eagain_count = 0
    deadline = time.monotonic() + timeout_seconds
    current = before_current
    current_stat = before_stat
    while any(current_stat.values()) and time.monotonic() < deadline:
        attempts += 1
        outcome = _request_memory_reclaim(reclaim_path, max(current, 4096))
        if outcome == "EAGAIN":
            eagain_count += 1
        current = _parse_limit(
            _optional_text(directory / "memory.current"),
            name="condition memory.current",
        )
        if current is None:
            raise ResourceIsolationError("condition memory.current cannot be max")
        current_stat = _reclaimable_memory_stat(directory)
        if any(current_stat.values()):
            time.sleep(_CGROUP_POLL_SECONDS)
    return {
        "method": "numeric-memory.reclaim",
        "exact_zero_required": False,
        "eagain_is_partial_success": True,
        "attempt_count": attempts,
        "eagain_count": eagain_count,
        "memory_current_before_bytes": before_current,
        "memory_current_after_bytes": current,
        "reclaimable_before_bytes": before_stat,
        "reclaimable_after_bytes": current_stat,
        "reclaimable_zero_after": not any(current_stat.values()),
    }


def _parent_residue_diagnostics(directory: Path) -> dict[str, object]:
    """Record non-normative parent charge/dying-cgroup diagnostics.

    Empty cgroups may retain small kernel charges and dying descendants after
    removal.  These values are useful for auditing and capacity diagnosis, but
    correctness never depends on reaching exact zero.
    """

    current = _parse_limit(
        _optional_text(directory / "memory.current"),
        name="coordinator memory.current",
    )
    if current is None:
        raise ResourceIsolationError("coordinator memory.current cannot be max")
    cgroup_stat = _parse_keyed_cgroup_integers(
        _optional_text(directory / "cgroup.stat"), label="coordinator cgroup.stat"
    )
    for key in ("nr_descendants", "nr_dying_descendants"):
        if key not in cgroup_stat:
            raise ResourceIsolationError(
                f"coordinator cgroup.stat lacks {key}"
            )
    return {
        "memory_current_bytes": current,
        "reclaimable_memory_stat_bytes": _reclaimable_memory_stat(directory),
        "cgroup_stat": cgroup_stat,
    }


def _configure_memory_cgroup(
    directory: Path, *, memory_max_bytes: int = MEMORY_MAX_BYTES
) -> None:
    if memory_max_bytes not in (MEMORY_MAX_BYTES, MANAGER_MEMORY_MAX_BYTES):
        raise ResourceIsolationError(
            f"unsupported cgroup memory contract: {memory_max_bytes} bytes"
        )
    _write_cgroup_value(
        directory / "memory.max", str(memory_max_bytes), label="memory.max"
    )
    _write_cgroup_value(
        directory / "memory.high",
        COORDINATOR_MEMORY_MAX,
        label="memory.high",
    )
    _write_cgroup_value(
        directory / "memory.swap.max",
        str(MEMORY_SWAP_MAX_BYTES),
        label="memory.swap.max",
    )
    _write_cgroup_value(
        directory / "memory.oom.group", "1", label="memory.oom.group"
    )
    snapshot = _snapshot_cgroup(directory)
    if (
        snapshot["memory.max"] != str(memory_max_bytes)
        or snapshot["memory.high"] != COORDINATOR_MEMORY_MAX
        or snapshot["memory.swap.max"] != str(MEMORY_SWAP_MAX_BYTES)
        or snapshot["memory.oom.group"] != "1"
    ):
        raise ResourceIsolationError(
            f"cgroup memory controls did not take effect in {directory}"
        )


def _exact_memory_controls(
    directory: Path,
    *,
    label: str,
    expected_memory_max: str = str(MEMORY_MAX_BYTES),
) -> dict[str, str]:
    snapshot = _snapshot_cgroup(directory)
    controls = {
        "memory.max": snapshot["memory.max"],
        "memory.high": snapshot["memory.high"],
        "memory.swap.max": snapshot["memory.swap.max"],
        "memory.oom.group": snapshot["memory.oom.group"],
    }
    if controls != {
        "memory.max": expected_memory_max,
        "memory.high": COORDINATOR_MEMORY_MAX,
        "memory.swap.max": str(MEMORY_SWAP_MAX_BYTES),
        "memory.oom.group": "1",
    }:
        raise ResourceIsolationError(f"{label} memory/OOM controls changed")
    return {name: str(value) for name, value in controls.items()}


def _delegated_memory_context() -> tuple[Path, dict[str, object], CgroupLocation]:
    raw = os.environ.get(_DELEGATED_ROOT_ENV)
    if raw is None:
        raise ResourceIsolationError("delegated memory cgroup identity is unavailable")
    try:
        record = json.loads(raw)
    except json.JSONDecodeError as error:
        raise ResourceIsolationError(
            "delegated memory cgroup identity is invalid"
        ) from error
    if not isinstance(record, Mapping) or not isinstance(record.get("directory"), str):
        raise ResourceIsolationError("delegated memory cgroup identity is incomplete")
    root = Path(str(record["directory"]))
    if not root.is_absolute() or not _same_cgroup_identity(root, record):
        raise ResourceIsolationError("delegated memory cgroup identity changed")
    current = _resolve_current_cgroup(PROC_ROOT)
    if current.directory.parent != root or current.directory.name != _MANAGER_CGROUP_NAME:
        raise ResourceIsolationError(
            "condition cgroups may only be managed from the authenticated manager leaf"
        )
    return root, dict(record), current


def _prepare_delegated_memory_layout() -> dict[str, object]:
    """Move the service main process to a manager leaf and delegate memory below it."""

    root_location = _resolve_current_cgroup(PROC_ROOT)
    root = root_location.directory
    root_snapshot = _snapshot_cgroup(root)
    if (
        root_snapshot["memory.max"] != COORDINATOR_MEMORY_MAX
        or root_snapshot["memory.high"] != COORDINATOR_MEMORY_MAX
        or root_snapshot["memory.swap.max"] != str(MEMORY_SWAP_MAX_BYTES)
        or root_snapshot["memory.oom.group"] != "1"
    ):
        raise ResourceIsolationError(
            "the transient coordinator root lacks the uncapped memory/OOM contract"
        )
    required_controllers = {"memory"}
    controllers_raw = root_snapshot["cgroup.controllers"]
    controllers = set(controllers_raw.split()) if controllers_raw is not None else set()
    if not required_controllers <= controllers:
        raise ResourceIsolationError(
            "the service did not delegate the memory controller"
        )

    manager = root / _MANAGER_CGROUP_NAME
    try:
        manager.mkdir(mode=0o700)
    except OSError as error:
        raise ResourceIsolationError(
            f"cannot create delegated manager cgroup: {error}"
        ) from error
    try:
        _write_cgroup_value(
            manager / "cgroup.procs", "0", label="manager cgroup.procs"
        )
        moved = _resolve_current_cgroup(PROC_ROOT)
        if moved.directory != manager:
            raise ResourceIsolationError("worker did not enter its manager cgroup")
        subtree = _optional_text(root / "cgroup.subtree_control")
        if subtree is None:
            raise ResourceIsolationError("cgroup.subtree_control is unavailable")
        enabled_controllers = set(subtree.split())
        if enabled_controllers != required_controllers:
            _write_cgroup_value(
                root / "cgroup.subtree_control",
                "+memory",
                label="cgroup.subtree_control",
            )
        enabled_raw = _optional_text(root / "cgroup.subtree_control")
        enabled_controllers = (
            set(enabled_raw.split()) if enabled_raw is not None else set()
        )
        if enabled_controllers != required_controllers:
            raise ResourceIsolationError(
                "the service root did not enable exactly the memory controller"
            )
        _configure_memory_cgroup(
            manager, memory_max_bytes=MANAGER_MEMORY_MAX_BYTES
        )
    except Exception:
        # Once self has moved into manager, systemd will remove the delegated
        # subtree when the transient service fails.  Trying to move back would
        # obscure the original failure and is therefore deliberately avoided.
        raise

    root_identity = _cgroup_directory_identity(root)
    os.environ[_DELEGATED_ROOT_ENV] = _canonical_json(root_identity)
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-delegated-memory-layout",
        "verified": True,
        "verified_at": _utc_now(),
        "required_controllers": sorted(required_controllers),
        "root_controllers": sorted(controllers),
        "root_subtree_control": sorted(enabled_controllers),
        "root": root_identity,
        "manager": _cgroup_directory_identity(manager),
        "root_memory_controls": _exact_memory_controls(
            root,
            label="delegated coordinator root",
            expected_memory_max=COORDINATOR_MEMORY_MAX,
        ),
        "manager_memory_controls": _exact_memory_controls(
            manager,
            label="delegated manager",
            expected_memory_max=str(MANAGER_MEMORY_MAX_BYTES),
        ),
    }


def _create_unique_condition_directory(root: Path, condition_id: str) -> Path:
    for _attempt in range(16):
        directory = root / f"condition-{condition_id}-{secrets.token_hex(8)}"
        try:
            directory.mkdir(mode=0o700)
        except FileExistsError:
            continue
        except OSError as error:
            raise ResourceIsolationError(
                f"cannot create fresh condition cgroup: {error}"
            ) from error
        return directory
    raise ResourceIsolationError("cannot allocate a unique condition cgroup")


def _initial_condition_snapshot(directory: Path) -> dict[str, object]:
    snapshot = _snapshot_cgroup(directory)
    try:
        reclaim_status = (directory / "memory.reclaim").stat()
    except OSError as error:
        raise ResourceIsolationError(
            f"fresh condition cgroup lacks memory.reclaim: {error}"
        ) from error
    if not stat.S_ISREG(reclaim_status.st_mode):
        raise ResourceIsolationError(
            "fresh condition cgroup memory.reclaim is not a file"
        )
    events = _parse_keyed_cgroup_integers(
        snapshot["cgroup.events"], label="condition cgroup.events"
    )
    current = _parse_limit(snapshot["memory.current"], name="memory.current")
    peak = _parse_limit(snapshot["memory.peak"], name="memory.peak")
    if snapshot["cgroup.procs"] != "" or events.get("populated") != 0:
        raise ResourceIsolationError("fresh condition cgroup is unexpectedly populated")
    if current != 0 or peak != 0:
        raise ResourceIsolationError(
            "fresh condition cgroup does not start with zero current/peak memory"
        )
    if (
        snapshot["memory.max"] != str(MEMORY_MAX_BYTES)
        or snapshot["memory.high"] != COORDINATOR_MEMORY_MAX
        or snapshot["memory.swap.max"] != str(MEMORY_SWAP_MAX_BYTES)
        or snapshot["memory.oom.group"] != "1"
    ):
        raise ResourceIsolationError("fresh condition cgroup limits are incorrect")
    if snapshot["memory.events"] is None or snapshot["memory.events.local"] is None:
        raise ResourceIsolationError("fresh condition memory event files are unavailable")
    return {
        "cgroup_procs": snapshot["cgroup.procs"],
        "cgroup_events": snapshot["cgroup.events"],
        "memory_current_bytes": current,
        "memory_peak_bytes": peak,
        "memory_max": snapshot["memory.max"],
        "memory_high": snapshot["memory.high"],
        "memory_swap_max": snapshot["memory.swap.max"],
        "memory_oom_group": snapshot["memory.oom.group"],
        "memory_events": snapshot["memory.events"],
        "memory_events_local": snapshot["memory.events.local"],
    }


@dataclass
class FreshConditionCgroup:
    """A unique, single-use condition cgroup with a lifetime memory peak."""

    condition_id: str
    _directory: Path
    _parent_identity: dict[str, object]
    _identity: dict[str, object]
    _expected_cpus: tuple[int, ...]
    _begin_evidence: dict[str, object]
    _begin_digest: str
    _wrapped: bool = False
    _closed: bool = False

    @property
    def begin_evidence(self) -> dict[str, object]:
        return copy.deepcopy(self._begin_evidence)

    @property
    def closed(self) -> bool:
        return self._closed

    def wrap_command(
        self,
        worker_command: Sequence[str],
        *,
        proof_file: Path | None = None,
    ) -> list[str]:
        """Return the one command allowed to enter and use this fresh leaf."""

        if self._closed:
            raise ResourceIsolationError("condition cgroup is already closed")
        if self._wrapped:
            raise ResourceIsolationError("condition cgroup is single-use")
        worker = _validate_worker_command(worker_command)
        command = [
            sys.executable,
            str(Path(__file__).resolve()),
            "_enter-condition-cgroup-and-exec",
            "--cgroup-directory",
            str(self._directory),
            "--expected-device",
            str(self._identity["device"]),
            "--expected-inode",
            str(self._identity["inode"]),
            "--expected-cpus",
            format_cpu_list(self._expected_cpus),
        ]
        if proof_file is not None:
            command.extend(["--proof-file", str(proof_file.resolve())])
        command.extend(["--", *worker])
        self._wrapped = True
        return command

    def _remove(self) -> None:
        try:
            os.rmdir(self._directory)
        except OSError as error:
            raise ResourceIsolationError(
                f"cannot remove condition cgroup {self._directory}: {error}"
            ) from error

    def _require_identity(self) -> None:
        if not _same_cgroup_identity(self._directory, self._identity):
            raise ResourceIsolationError("condition cgroup identity changed")

    def _force_empty(self) -> bool:
        # Never signal through a path until its device/inode identity has been
        # re-authenticated.  A delegated subtree is writable by the service
        # user, so path equality alone is not sufficient for safe cleanup.
        self._require_identity()
        if not _cgroup_is_populated(self._directory):
            return False
        _write_cgroup_value(
            self._directory / "cgroup.kill", "1", label="condition cgroup.kill"
        )
        if not _wait_for_empty_cgroup(self._directory):
            raise ResourceIsolationError("condition cgroup remained populated after kill")
        return True

    def finish(self) -> dict[str, object]:
        """Read the lifetime high-water mark and remove the now-empty cgroup."""

        if self._closed:
            raise ResourceIsolationError("condition cgroup is already closed")
        if not self._wrapped:
            raise ResourceIsolationError("condition cgroup command was never wrapped")
        self._require_identity()
        if not _wait_for_empty_cgroup(self._directory):
            forced = self._force_empty()
            if forced:
                try:
                    self._remove()
                finally:
                    self._closed = True
                raise ResourceIsolationError(
                    "condition cgroup required forced process cleanup"
                )
        self._require_identity()
        snapshot = _snapshot_cgroup(self._directory)
        current_end = _parse_limit(
            snapshot["memory.current"], name="condition memory.current"
        )
        peak_end = _parse_limit(snapshot["memory.peak"], name="condition memory.peak")
        if current_end is None or peak_end is None or peak_end < current_end:
            raise ResourceIsolationError(
                "condition lifetime memory.peak is below final memory.current"
            )
        events = _parse_keyed_cgroup_integers(
            snapshot["cgroup.events"], label="condition cgroup.events"
        )
        if events.get("populated") != 0:
            raise ResourceIsolationError("condition cgroup repopulated during telemetry")
        if snapshot["memory.events"] is None or snapshot["memory.events.local"] is None:
            raise ResourceIsolationError("condition memory event files are unavailable")
        condition_controls = _exact_memory_controls(
            self._directory, label="condition cgroup"
        )
        if not _same_cgroup_identity(
            Path(str(self._parent_identity["directory"])), self._parent_identity
        ):
            raise ResourceIsolationError("pair-parent cgroup identity changed")
        parent_controls = _exact_memory_controls(
            Path(str(self._parent_identity["directory"])),
            label="coordinator cgroup",
            expected_memory_max=COORDINATOR_MEMORY_MAX,
        )
        post_measurement_reclaim = _best_effort_condition_reclaim(
            self._directory
        )
        parent_residue_before_removal = _parent_residue_diagnostics(
            Path(str(self._parent_identity["directory"]))
        )
        evidence: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-fresh-condition-cgroup-finish",
            "verified": True,
            "verified_at": _utc_now(),
            "scope_id": self._begin_evidence["scope_id"],
            "condition_id": self.condition_id,
            "begin_evidence_sha256": self._begin_digest,
            "measurement_scope": "fresh_condition_cgroup_lifetime",
            "memory_peak_reset_used": False,
            "same_cgroup_device_inode": True,
            "parent_cgroup": copy.deepcopy(self._parent_identity),
            "cgroup": copy.deepcopy(self._identity),
            "cgroup_events": snapshot["cgroup.events"],
            "memory_events": snapshot["memory.events"],
            "memory_events_local": snapshot["memory.events.local"],
            "memory_current_end_bytes": current_end,
            "memory_peak_lifetime_bytes": peak_end,
            "condition_memory_controls_at_finish": condition_controls,
            "pair_parent_memory_controls_at_finish": parent_controls,
            "post_measurement_reclaim": post_measurement_reclaim,
            "pair_parent_residue_diagnostics": {
                "diagnostic_only": True,
                "exact_zero_required": False,
                "before_condition_cgroup_removal": parent_residue_before_removal,
                "after_condition_cgroup_removal": None,
            },
            "cleanup": {"cgroup_kill_used": False, "removed": True},
        }
        try:
            self._remove()
        finally:
            self._closed = True
        parent_residue_after_removal = _parent_residue_diagnostics(
            Path(str(self._parent_identity["directory"]))
        )
        before_descendants = parent_residue_before_removal["cgroup_stat"][
            "nr_descendants"
        ]
        after_descendants = parent_residue_after_removal["cgroup_stat"][
            "nr_descendants"
        ]
        if before_descendants < 2 or after_descendants != before_descendants - 1:
            raise ResourceIsolationError(
                "condition removal did not produce the exact one-descendant "
                "coordinator transition"
            )
        evidence["pair_parent_residue_diagnostics"][
            "after_condition_cgroup_removal"
        ] = parent_residue_after_removal
        return evidence

    def close(self) -> None:
        """Kill any remaining descendants and remove the condition cgroup."""

        if self._closed:
            return
        try:
            self._force_empty()
            self._remove()
        finally:
            self._closed = True

    def __enter__(self) -> "FreshConditionCgroup":
        if self._closed:
            raise ResourceIsolationError("condition cgroup is already closed")
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> bool:
        try:
            self.close()
        except ResourceIsolationError:
            if exc_type is None:
                raise
        return False


def begin_fresh_condition_cgroup(
    slot: ResourceSlot | Mapping[str, object],
    condition_id: str,
) -> FreshConditionCgroup:
    """Create and authenticate one unused condition leaf below the pair root."""

    if _CONDITION_ID_RE.fullmatch(condition_id) is None:
        raise ResourceIsolationError(f"invalid condition cgroup id: {condition_id!r}")
    hydrated = _slot_from_public(slot)
    manager_contract = verify_resource_contract(
        hydrated.logical_cpus,
        expected_memory_bytes=MANAGER_MEMORY_MAX_BYTES,
    )
    root, root_identity, _manager = _delegated_memory_context()
    directory = _create_unique_condition_directory(root, condition_id)
    try:
        _configure_memory_cgroup(directory)
        initial = _initial_condition_snapshot(directory)
        identity = _cgroup_directory_identity(directory)
        begin_evidence: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-fresh-condition-cgroup-begin",
            "verified": True,
            "verified_at": _utc_now(),
            "scope_id": secrets.token_hex(16),
            "condition_id": condition_id,
            "measurement_scope": "fresh_condition_cgroup_lifetime",
            "memory_peak_reset_used": False,
            "parent_cgroup": root_identity,
            "cgroup": identity,
            "expected_logical_cpus": list(hydrated.logical_cpus),
            "manager_resource_contract": manager_contract,
            "initial": initial,
        }
        return FreshConditionCgroup(
            condition_id=condition_id,
            _directory=directory,
            _parent_identity=root_identity,
            _identity=identity,
            _expected_cpus=hydrated.logical_cpus,
            _begin_evidence=begin_evidence,
            _begin_digest=_sha256_text(_canonical_json(begin_evidence)),
        )
    except Exception:
        try:
            os.rmdir(directory)
        except OSError:
            pass
        raise


def _enter_condition_cgroup_and_exec(
    *,
    directory: Path,
    expected_device: int,
    expected_inode: int,
    expected_cpus: Iterable[int],
    worker_command: Sequence[str],
    proof_file: Path | None,
) -> None:
    root, _root_identity, current = _delegated_memory_context()
    target = directory
    expected_identity = {
        "directory": str(target),
        "device": expected_device,
        "inode": expected_inode,
    }
    if (
        not target.is_absolute()
        or target.parent != root
        or target == current.directory
        or not _same_cgroup_identity(target, expected_identity)
    ):
        raise ResourceIsolationError("condition cgroup target is not authenticated")
    _write_cgroup_value(target / "cgroup.procs", "0", label="condition cgroup.procs")
    moved = _resolve_current_cgroup(PROC_ROOT)
    if moved.directory != target or not _same_cgroup_identity(target, expected_identity):
        raise ResourceIsolationError("condition wrapper did not enter its cgroup")
    proof = verify_resource_contract(
        expected_cpus, expected_memory_bytes=MEMORY_MAX_BYTES
    )
    if proof_file is not None:
        _write_proof(proof_file, proof)
    compact = _canonical_json(proof)
    sys.stderr.write(f"HIGHAMBENCH_RESOURCE_PROOF={compact}\n")
    sys.stderr.flush()
    environment = dict(os.environ)
    environment["HIGHAMBENCH_RESOURCE_PROOF"] = compact
    worker = _validate_worker_command(worker_command)
    os.execvpe(worker[0], list(worker), environment)


def _validate_worker_command(worker_command: Sequence[str]) -> tuple[str, ...]:
    if not worker_command or not all(
        isinstance(item, str) and item and "\x00" not in item
        for item in worker_command
    ):
        raise ResourceIsolationError(
            "worker_command must be a nonempty sequence of nonempty strings"
        )
    return tuple(worker_command)


def _validate_slot(slot: ResourceSlot) -> None:
    if len(slot.cores) != PHYSICAL_CORES_PER_SLOT:
        raise ResourceIsolationError(
            f"a production slot must contain exactly {PHYSICAL_CORES_PER_SLOT} physical cores"
        )
    if len({core.identity for core in slot.cores}) != PHYSICAL_CORES_PER_SLOT:
        raise ResourceIsolationError("a production slot repeats a physical core")
    if {core.type_key for core in slot.cores} != {slot.type_key}:
        raise ResourceIsolationError("a production slot mixes CPU types")
    expected = {cpu for core in slot.cores for cpu in core.logical_cpus}
    if expected != set(slot.logical_cpus):
        raise ResourceIsolationError(
            "a production slot does not contain every logical sibling exactly once"
        )


def build_systemd_run_command(
    slot: ResourceSlot,
    worker_command: Sequence[str],
    *,
    unit_name: str,
    working_directory: Path | None = None,
    proof_file: Path | None = None,
) -> list[str]:
    """Build the sole production launch command.

    There is deliberately no switch for removing systemd, the memory boundary,
    locked scheduler affinity, or in-worker verification.
    """

    _validate_slot(slot)
    worker = _validate_worker_command(worker_command)
    if _UNIT_NAME_RE.fullmatch(unit_name) is None:
        raise ResourceIsolationError(f"invalid transient unit name: {unit_name!r}")
    cpu_list = format_cpu_list(slot.logical_cpus)
    # CPUAffinity= follows systemd's CPU-set syntax, whose list separator is
    # whitespace.  Keep the canonical comma form for our own proof CLI.
    systemd_cpu_list = cpu_list.replace(",", " ")
    command = [
        "systemd-run",
        "--user",
        "--collect",
        "--wait",
        "--pipe",
        "--service-type=exec",
        f"--unit={unit_name}",
        "--property=Delegate=memory",
        "--property=MemoryAccounting=yes",
        "--property=MemoryMax=infinity",
        "--property=MemoryHigh=infinity",
        f"--property=MemorySwapMax={MEMORY_SWAP_MAX_BYTES}",
        f"--property=CPUAffinity={systemd_cpu_list}",
        "--property=CPUAccounting=yes",
        "--property=KillMode=control-group",
        "--property=OOMPolicy=kill",
        "--property=NoNewPrivileges=yes",
        "--property=SystemCallArchitectures=native",
        "--property=SystemCallFilter=~sched_setaffinity",
        "--property=SystemCallErrorNumber=EPERM",
    ]
    if working_directory is not None:
        resolved_cwd = working_directory.resolve()
        if not resolved_cwd.is_dir():
            raise ResourceIsolationError(
                f"working directory does not exist: {resolved_cwd}"
            )
        command.append(f"--working-directory={resolved_cwd}")
    command.extend(
        [
            "--",
            sys.executable,
            str(Path(__file__).resolve()),
            "_verify-and-exec",
            "--expected-cpus",
            cpu_list,
        ]
    )
    if proof_file is not None:
        command.extend(["--proof-file", str(proof_file.resolve())])
    command.extend(["--", *worker])
    return command


def systemd_run_command(
    slot: ResourceSlot | Mapping[str, object],
    unit_name: str,
    child_argv: Sequence[str],
    *,
    working_directory: Path | None = None,
    proof_file: Path | None = None,
) -> list[str]:
    """Public orchestrator API for the mandatory production launch command."""

    return build_systemd_run_command(
        _slot_from_public(slot),
        child_argv,
        unit_name=unit_name,
        working_directory=working_directory,
        proof_file=proof_file,
    )


def launch_in_slot(
    slot: ResourceSlot,
    worker_command: Sequence[str],
    *,
    unit_name: str,
    working_directory: Path | None = None,
    proof_file: Path | None = None,
    dry_run: bool = False,
) -> dict[str, object]:
    """Plan or run the production command; dry-run never invokes a worker."""

    command = build_systemd_run_command(
        slot,
        worker_command,
        unit_name=unit_name,
        working_directory=working_directory,
        proof_file=proof_file,
    )
    plan: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-resource-launch",
        "dry_run": dry_run,
        "executed": False,
        "slot": slot.to_json(),
        "command": command,
        "command_display": shlex.join(command),
    }
    if dry_run:
        plan["disposition"] = "plan-only; worker was not executed"
        return plan
    missing = [name for name in ("systemd-run",) if shutil.which(name) is None]
    if missing:
        raise ResourceIsolationError(
            "required production executables are unavailable: " + ", ".join(missing)
        )
    completed = subprocess.run(command, check=False)
    plan["executed"] = True
    plan["exit_code"] = completed.returncode
    return plan


def _parse_meminfo(raw: str) -> dict[str, dict[str, object]]:
    parsed: dict[str, dict[str, object]] = {}
    for line in raw.splitlines():
        key, separator, value = line.partition(":")
        if not separator:
            continue
        fields = value.strip().split()
        record: dict[str, object] = {"raw": value.strip()}
        if fields and fields[0].isdigit():
            amount = int(fields[0])
            if len(fields) == 1:
                record["value"] = amount
            elif fields[1] == "kB":
                record["bytes"] = amount * 1024
        parsed[key] = record
    return parsed


def _cpu_runtime_facts(cpu_root: Path, cpus: Iterable[int]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for cpu in sorted(cpus):
        base = cpu_root / f"cpu{cpu}"
        cpufreq = base / "cpufreq"
        row: dict[str, object] = {"cpu": cpu}
        for name in (
            "scaling_driver",
            "scaling_governor",
            "scaling_available_governors",
            "scaling_min_freq",
            "scaling_max_freq",
            "scaling_cur_freq",
            "cpuinfo_min_freq",
            "cpuinfo_max_freq",
            "energy_performance_preference",
            "energy_performance_available_preferences",
        ):
            row[name] = _optional_text(cpufreq / name)
        row["online"] = _optional_text(base / "online") or "1"
        row["cpu_capacity"] = _optional_text(base / "cpu_capacity")
        rows.append(row)
    return rows


def _numa_facts(sys_root: Path) -> dict[str, object]:
    node_root = sys_root / "devices/system/node"
    online_raw = _optional_text(node_root / "online")
    nodes = parse_cpu_list(online_raw) if online_raw else ()
    records: list[dict[str, object]] = []
    for node in nodes:
        base = node_root / f"node{node}"
        hugepages: dict[str, dict[str, str | None]] = {}
        for path in sorted((base / "hugepages").glob("hugepages-*kB")):
            hugepages[path.name] = {
                "nr_hugepages": _optional_text(path / "nr_hugepages"),
                "free_hugepages": _optional_text(path / "free_hugepages"),
                "surplus_hugepages": _optional_text(path / "surplus_hugepages"),
            }
        records.append(
            {
                "node": node,
                "cpulist": _optional_text(base / "cpulist"),
                "distance": _optional_text(base / "distance"),
                "meminfo": _optional_text(base / "meminfo"),
                "hugepages": hugepages,
            }
        )
    return {"online": online_raw, "nodes": records}


def _command_version(command: Sequence[str]) -> dict[str, object]:
    try:
        completed = subprocess.run(
            list(command),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return {"command": list(command), "error": str(error)}
    return {
        "command": list(command),
        "exit_code": completed.returncode,
        "output": completed.stdout.strip(),
    }


def collect_host_facts(
    inventory: CpuInventory,
    *,
    sys_root: Path = SYS_ROOT,
    proc_root: Path = PROC_ROOT,
) -> dict[str, object]:
    """Collect the auditable host snapshot used to qualify a measurement."""

    cpu_root = sys_root / "devices/system/cpu"
    meminfo_raw = _read_text(proc_root / "meminfo", label="/proc/meminfo")
    cpuinfo_raw = _read_text(proc_root / "cpuinfo", label="/proc/cpuinfo")
    mountinfo_raw = _read_text(
        proc_root / "self/mountinfo", label="/proc/self/mountinfo"
    )
    cgroup_raw = _read_text(proc_root / "self/cgroup", label="/proc/self/cgroup")
    location = _resolve_current_cgroup(proc_root)
    uname = platform.uname()
    dmi_root = sys_root / "class/dmi/id"
    dmi_names = (
        "sys_vendor",
        "product_name",
        "product_version",
        "product_family",
        "board_vendor",
        "board_name",
        "board_version",
        "bios_vendor",
        "bios_version",
        "bios_date",
        "chassis_type",
    )
    global_cpu_files = (
        "online",
        "offline",
        "possible",
        "present",
        "isolated",
        "nohz_full",
        "smt/active",
        "smt/control",
        "intel_pstate/status",
        "intel_pstate/no_turbo",
        "cpufreq/boost",
    )
    meminfo = _parse_meminfo(meminfo_raw)
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-host-facts",
        "captured_at": _utc_now(),
        "kernel": {
            "system": uname.system,
            "node": uname.node,
            "release": uname.release,
            "version": uname.version,
            "machine": uname.machine,
            "processor": uname.processor,
            "proc_version": _optional_text(proc_root / "version"),
            "command_line": _optional_text(proc_root / "cmdline"),
            "boot_id": _optional_text(sys_root / "kernel/random/boot_id"),
            "clocksource_current": _optional_text(
                sys_root / "devices/system/clocksource/clocksource0/current_clocksource"
            ),
            "clocksource_available": _optional_text(
                sys_root / "devices/system/clocksource/clocksource0/available_clocksource"
            ),
            "transparent_hugepage_enabled": _optional_text(
                sys_root / "kernel/mm/transparent_hugepage/enabled"
            ),
            "transparent_hugepage_defrag": _optional_text(
                sys_root / "kernel/mm/transparent_hugepage/defrag"
            ),
            "numa_balancing": _optional_text(proc_root / "sys/kernel/numa_balancing"),
        },
        "hardware": {
            "dmi": {name: _optional_text(dmi_root / name) for name in dmi_names},
            "cpu": {
                "inventory": inventory.to_json(),
                "global_sysfs": {
                    name: _optional_text(cpu_root / name) for name in global_cpu_files
                },
                "runtime_per_allowed_cpu": _cpu_runtime_facts(
                    cpu_root, inventory.allowed_cpus
                ),
                "proc_cpuinfo_raw": cpuinfo_raw,
                "proc_cpuinfo_sha256": _sha256_text(cpuinfo_raw),
            },
            "numa": _numa_facts(sys_root),
        },
        "memory": {
            "proc_meminfo_raw": meminfo_raw,
            "proc_meminfo_sha256": _sha256_text(meminfo_raw),
            "proc_meminfo": meminfo,
            "mem_total_bytes": meminfo.get("MemTotal", {}).get("bytes"),
            "mem_available_bytes": meminfo.get("MemAvailable", {}).get("bytes"),
            "swap_total_bytes": meminfo.get("SwapTotal", {}).get("bytes"),
            "page_size_bytes": os.sysconf("SC_PAGE_SIZE"),
            "physical_pages": os.sysconf("SC_PHYS_PAGES"),
            "available_physical_pages": os.sysconf("SC_AVPHYS_PAGES"),
        },
        "cgroup": {
            "version": 2,
            "proc_self_cgroup_raw": cgroup_raw,
            "proc_self_mountinfo_cgroup_lines": [
                line for line in mountinfo_raw.splitlines() if " - cgroup" in line
            ],
            "location": location.to_json(),
            "current": _snapshot_cgroup(location.directory),
            "root": _snapshot_cgroup(location.mount_point),
            "ancestor_memory_limits": _ancestor_memory_limits(location),
        },
        "runtime": {
            "python": sys.version,
            "python_executable": sys.executable,
            "systemd_run_path": shutil.which("systemd-run"),
            "systemd_version": _command_version(["systemd-run", "--version"]),
        },
    }


def _write_proof(path: Path, proof: Mapping[str, object]) -> None:
    if not path.is_absolute():
        raise ResourceIsolationError("resource proof path must be absolute")
    if not path.parent.is_dir():
        raise ResourceIsolationError(
            f"resource proof parent directory does not exist: {path.parent}"
        )
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    payload = json.dumps(proof, indent=2, sort_keys=True) + "\n"
    try:
        with temporary.open("x", encoding="utf-8") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _verified_exec(
    expected_cpus: Iterable[int],
    worker_command: Sequence[str],
    *,
    proof_file: Path | None,
) -> None:
    # The privileged CPU guard passes its shared campaign flock as fd 0 so
    # systemd's queued/running launch keeps release blocked if the guard helper
    # dies.  Once this wrapper is executing, systemd has already placed it in
    # the measured service cgroup; replace fd 0 before any worker code can see
    # or unlock the root-owned descriptor.  Standalone/user launches do not set
    # the marker and retain their ordinary stdin.
    lifetime_lock_marker = os.environ.pop(
        "HIGHAMBENCH_LIFETIME_LOCK_STDIN", None
    )
    if lifetime_lock_marker is not None:
        if lifetime_lock_marker != "1":
            raise ResourceIsolationError(
                "invalid campaign lifetime-lock marker"
            )
        try:
            null_descriptor = os.open(os.devnull, os.O_RDONLY | os.O_CLOEXEC)
            try:
                os.dup2(null_descriptor, 0)
            finally:
                os.close(null_descriptor)
        except OSError as error:
            raise ResourceIsolationError(
                f"cannot detach campaign lifetime-lock stdin: {error}"
            ) from error
    worker = _validate_worker_command(worker_command)
    delegated_layout = _prepare_delegated_memory_layout()
    proof = verify_resource_contract(
        expected_cpus, expected_memory_bytes=MANAGER_MEMORY_MAX_BYTES
    )
    proof["delegated_memory_layout"] = delegated_layout
    if proof_file is not None:
        _write_proof(proof_file, proof)
    compact = _canonical_json(proof)
    sys.stderr.write(f"HIGHAMBENCH_RESOURCE_PROOF={compact}\n")
    sys.stderr.flush()
    environment = dict(os.environ)
    environment["HIGHAMBENCH_RESOURCE_PROOF"] = compact
    os.execvpe(worker[0], list(worker), environment)


def _strip_remainder(command: Sequence[str]) -> list[str]:
    result = list(command)
    if result and result[0] == "--":
        result.pop(0)
    return result


def _select_local_slot(index: int) -> tuple[CpuInventory, ResourceSlot]:
    inventory = inventory_cpu_topology()
    slots = allocate_resource_slots(inventory)
    if index < 0 or index >= len(slots):
        raise ResourceIsolationError(
            f"slot index {index} is unavailable; host exposes {len(slots)} slot(s)"
        )
    return inventory, slots[index]


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)

    inventory_parser = subparsers.add_parser("inventory")
    inventory_parser.add_argument("--slot-count", type=int)

    for action in ("plan", "run"):
        launch_parser = subparsers.add_parser(action)
        launch_parser.add_argument("--slot-index", type=int, default=0)
        launch_parser.add_argument("--unit", required=True)
        launch_parser.add_argument("--working-directory", type=Path)
        launch_parser.add_argument("--proof-file", type=Path)
        launch_parser.add_argument("worker", nargs=argparse.REMAINDER)

    verify_parser = subparsers.add_parser("_verify-and-exec", help=argparse.SUPPRESS)
    verify_parser.add_argument("--expected-cpus", required=True)
    verify_parser.add_argument("--proof-file", type=Path)
    verify_parser.add_argument("worker", nargs=argparse.REMAINDER)

    condition_parser = subparsers.add_parser(
        "_enter-condition-cgroup-and-exec", help=argparse.SUPPRESS
    )
    condition_parser.add_argument("--cgroup-directory", type=Path, required=True)
    condition_parser.add_argument("--expected-device", type=int, required=True)
    condition_parser.add_argument("--expected-inode", type=int, required=True)
    condition_parser.add_argument("--expected-cpus", required=True)
    condition_parser.add_argument("--proof-file", type=Path)
    condition_parser.add_argument("worker", nargs=argparse.REMAINDER)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.action == "inventory":
            inventory = inventory_cpu_topology()
            slots = allocate_resource_slots(inventory, slot_count=args.slot_count)
            payload = collect_host_facts(inventory)
            payload["resource_slots"] = [slot.to_json() for slot in slots]
            print(json.dumps(payload, indent=2, sort_keys=True))
            return 0
        if args.action == "_verify-and-exec":
            _verified_exec(
                parse_cpu_list(args.expected_cpus),
                _strip_remainder(args.worker),
                proof_file=args.proof_file,
            )
            raise AssertionError("os.execvpe returned unexpectedly")
        if args.action == "_enter-condition-cgroup-and-exec":
            if args.expected_device < 0 or args.expected_inode <= 0:
                raise ResourceIsolationError("invalid condition cgroup device/inode")
            _enter_condition_cgroup_and_exec(
                directory=args.cgroup_directory,
                expected_device=args.expected_device,
                expected_inode=args.expected_inode,
                expected_cpus=parse_cpu_list(args.expected_cpus),
                worker_command=_strip_remainder(args.worker),
                proof_file=args.proof_file,
            )
            raise AssertionError("os.execvpe returned unexpectedly")
        _inventory, slot = _select_local_slot(args.slot_index)
        result = launch_in_slot(
            slot,
            _strip_remainder(args.worker),
            unit_name=args.unit,
            working_directory=args.working_directory,
            proof_file=args.proof_file,
            dry_run=args.action == "plan",
        )
        print(json.dumps(result, indent=2, sort_keys=True))
        if args.action == "run":
            return int(result["exit_code"])
        return 0
    except ResourceIsolationError as error:
        print(f"resource isolation failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
