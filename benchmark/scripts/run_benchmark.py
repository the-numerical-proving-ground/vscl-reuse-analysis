#!/usr/bin/env python3
"""Create, inspect, and run the tracked VSCLReuse measurement campaign."""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import time
from typing import Any, Iterable, Mapping, Sequence
import uuid

try:
    from .common import (
        MeasurementError,
        append_jsonl,
        artifact,
        atomic_write_json,
        canonical_digest,
        command_version,
        manifest_for_tree,
        read_object,
        resolved_regular_file,
        run_captured,
        sha256_file,
        utc_now,
        verify_manifest,
    )
    from . import resources, host_limits
except ImportError:  # pragma: no cover - direct execution
    from common import (  # type: ignore
        MeasurementError,
        append_jsonl,
        artifact,
        atomic_write_json,
        canonical_digest,
        command_version,
        manifest_for_tree,
        read_object,
        resolved_regular_file,
        run_captured,
        sha256_file,
        utc_now,
        verify_manifest,
    )
    import resources  # type: ignore
    import host_limits  # type: ignore


CAMPAIGN_KIND = "highambench-campaign-lock"
PAIR_KIND = "highambench-pair-result"
CPU_GUARD_PATH = Path(
    "/usr/local/libexec/highambench/highambench-cpu-guard"
)
CPU_GUARD_HOST_PATH = Path(
    "/usr/local/libexec/highambench/highambench-cpu-guard-host"
)
CPU_GUARD_SOURCE_RELATIVE = Path("admin/highambench_cpu_guard.py")
CPU_GUARD_FRONTEND_SOURCE_RELATIVE = Path(
    "admin/highambench_cpu_guard_frontend.py"
)
CPU_GUARD_SUDO_PATH = Path("/usr/bin/sudo")
CPU_GUARD_ACQUIRE_KIND = "highambench-cpu-guard-acquire"
CPU_GUARD_RELEASE_KIND = "highambench-cpu-guard-release"
CPU_GUARD_STATUS_KIND = "highambench-cpu-guard-status"
CPU_GUARD_RECOVERY_KIND = "highambench-cpu-guard-pre-acquire"
CPU_GUARD_RECOVERY_REQUEST_KIND = (
    "highambench-cpu-guard-pre-acquire-request"
)
CPU_GUARD_ACQUIRE_INTENT_KIND = "highambench-cpu-guard-acquire-intent"
CPU_GUARD_IDLE_SAMPLE_SECONDS = 2.0
CPU_GUARD_MAXIMUM_BUSY_PERCENT = 0.0
_CPU_GUARD_LEASE_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}$")
_CPU_GUARD_UNIT_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.@-]{0,180}$")
MEMORY_BYTES = resources.MEMORY_MAX_BYTES
MANAGER_MEMORY_BYTES = resources.MANAGER_MEMORY_MAX_BYTES
HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT = MEMORY_BYTES + MANAGER_MEMORY_BYTES
NUMSTABILITY_REPOSITORY = (
    "https://github.com/AlexGeorgantzas/lean-numerical-stability.git"
)
NUMSTABILITY_REF = "38228c607d62e9485b4fa1fc668cc3cb2857857e"
MATHLIB_REPOSITORY = "https://github.com/leanprover-community/mathlib4"
MATHLIB_COMMIT = "e8ea1afc32790ce1d4e1a4e45cc412ba9388716b"
MATHLIB_CACHE_ARTIFACT_COUNT = 8_033
MATHLIB_CACHE_ARTIFACT_BYTES = 393_376_909
MAX_MATHLIB_CACHE_DOWNLOAD_BYTES = 8 * 1024 * 1024 * 1024
MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256 = (
    "7b56da3bb98c5dc8ed297cfb72048cc308c7245f7bef217f71050da9ab891973"
)
MATHLIB_COMMIT_MANIFEST_BYTES = 163_719
MATHLIB_COMMIT_MANIFEST_RELATIVE_PATH = (
    "scripts/mathlib_cache_commit_manifest.txt"
)
MATHLIB_COMMIT_MANIFEST_SHA256 = (
    "2ff9a9c943dc1c6f8df203135f7de550555235f7c535c9be3322b072c2f9e0ae"
)
MATHLIB_CACHE_FILENAME_SET_SHA256 = (
    "664cb1e03a33504b6f333678859396a1d9ae7de0405811f3884ff92f1f65b1f3"
)
MATHLIB_COMMIT_MANIFEST_RECORD = {
    "source": "tracked-authenticated-lock",
    "relative_path": MATHLIB_COMMIT_MANIFEST_RELATIVE_PATH,
    "size": MATHLIB_COMMIT_MANIFEST_BYTES,
    "sha256": MATHLIB_COMMIT_MANIFEST_SHA256,
    "expected_sha256": MATHLIB_COMMIT_MANIFEST_SHA256,
    "artifact_count": MATHLIB_CACHE_ARTIFACT_COUNT,
    "filename_set_sha256": MATHLIB_CACHE_FILENAME_SET_SHA256,
    "remote_commit_marker_required": False,
    "remote_download_observed": False,
    "authenticated_before_artifact_download": True,
}
LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc3"
LEAN_TOOLCHAIN_ARCHIVE_BYTES = 537_223_656
MAX_LEAN_TOOLCHAIN_TAR_BYTES = 4 * 1024 * 1024 * 1024
LEAN_TOOLCHAIN_ARCHIVE_SHA256 = (
    "6a8de92790c716de3083c4b5828f1dcc1c83f4cd9770b3dad7ad5c7c22db6012"
)
LEAN_TOOLCHAIN_TREE_SHA256 = (
    "a59ea7e8f02b0d8d2c441df5b8e97e679ed4e7f1d53f5742b855f4da8b22f979"
)
LEAN_TOOLCHAIN_LAKE_SHA256 = (
    "a608ff084d7e2af228b92a29d7c2fd083ba0580e46889175ec74a81678c98359"
)
LEAN_TOOLCHAIN_LEAN_SHA256 = (
    "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
)
LEAN_TOOLCHAIN_INTEGRITY = {
    "algorithm": "sha256-complete-tree-v2-with-link-count",
    "digest": LEAN_TOOLCHAIN_TREE_SHA256,
    "regular_files": 13_334,
    "directories": 533,
    "symlinks": 12,
    "regular_file_bytes": 2_791_170_725,
    "git_administrative_directories_included": True,
}
TASK_LOCK_RELATIVE = Path("metadata/task_corpus_lock.json")
TASK_SCOPE_RELATIVES = (
    Path("metadata/manifest.json"),
    Path("metadata/papers.csv"),
    Path("metadata/config.json"),
    Path("metadata/dependencies.json"),
    Path("tasks"),
    Path("shared"),
    Path("metadata/controlled"),
    Path("metadata/run_order.json"),
)
PREPARATION_ISOLATION_CONTRACT = {
    "contract_version": 5,
    "engine": "bubblewrap-inside-unshare",
    "host_root_mount": "not-mounted",
    "only_writable_host_tree": "derived-build",
    "environment_cleared": True,
    "nested_user_namespaces_disabled": True,
    "network_namespace": "private-unshare",
    "network_egress": "none-for-every-lake-process",
    "dependency_prefetch": "trusted-host-before-offline-lake",
    "lean_toolchain": "bounded-archive-authenticated-private-tree",
    "local_repository_mounts_visible_to_lake": False,
    "derived_git_administrative_metadata": (
        "read-only-overlays-for-every-lake-process"
    ),
}
PREFETCH_LOCK_CONTRACT = {
    "all_manifest_git_packages_at_exact_commits": True,
    "lean_toolchain": LEAN_TOOLCHAIN,
    "lean_toolchain_archive_bytes": LEAN_TOOLCHAIN_ARCHIVE_BYTES,
    "lean_toolchain_archive_sha256": LEAN_TOOLCHAIN_ARCHIVE_SHA256,
    "lean_toolchain_tree_sha256": LEAN_TOOLCHAIN_TREE_SHA256,
    "lean_toolchain_lake_sha256": LEAN_TOOLCHAIN_LAKE_SHA256,
    "lean_toolchain_lean_sha256": LEAN_TOOLCHAIN_LEAN_SHA256,
    "lean_toolchain_archive_download_observed": True,
    "lean_toolchain_archive_authenticated_before_extraction": True,
    "curl_kernel_file_size_limit_required": True,
    "mathlib_cache_remaining_batch_bound_required": True,
    "mathlib_cache_download_max_bytes": MAX_MATHLIB_CACHE_DOWNLOAD_BYTES,
    "lean_toolchain_tar_max_bytes": MAX_LEAN_TOOLCHAIN_TAR_BYTES,
    "mathlib_cache_artifact_count": MATHLIB_CACHE_ARTIFACT_COUNT,
    "mathlib_cache_artifact_bytes": MATHLIB_CACHE_ARTIFACT_BYTES,
    "mathlib_cache_artifact_manifest_sha256": (
        MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256
    ),
    "mathlib_cache_commit_manifest_source": "tracked-authenticated-lock",
    "mathlib_cache_commit_manifest_relative_path": (
        MATHLIB_COMMIT_MANIFEST_RELATIVE_PATH
    ),
    "mathlib_cache_commit_manifest_bytes": MATHLIB_COMMIT_MANIFEST_BYTES,
    "mathlib_cache_commit_manifest_sha256": MATHLIB_COMMIT_MANIFEST_SHA256,
    "mathlib_cache_filename_set_sha256": MATHLIB_CACHE_FILENAME_SET_SHA256,
    "mathlib_cache_commit_manifest_artifact_count": (
        MATHLIB_CACHE_ARTIFACT_COUNT
    ),
    "mathlib_cache_remote_commit_marker_required": False,
    "mathlib_cache_commit_manifest_remote_download_observed": False,
    "mathlib_cache_commit_manifest_authenticated_before_artifact_download": True,
    "leantar_version": "0.1.16",
    "leantar_binary_sha256": (
        "08546cc20f71916656df14ee0dee03e908530f7370ebfaaf276f3d8e8c548d9f"
    ),
    "proofwidgets_release_sha256": (
        "a6dc87b48d55b3507ccbe73248fc9762421c862bcf214e0cf16509dea376e0d5"
    ),
}


class _PairTerminalPublicationError(MeasurementError):
    """A completed pair could not be durably published to the campaign log."""


def _protocol(benchmark_root: Path) -> dict[str, Any]:
    value = read_object(
        benchmark_root / "metadata" / "measurement_protocol.json",
        kind="highambench-measurement-protocol",
    )
    attempt = value.get("attempt")
    pair = value.get("pair")
    resource = value.get("resources")
    comparability = value.get("comparability")
    agent = value.get("agent")
    dependencies = value.get("dependencies")
    storage = value.get("storage_isolation")
    telemetry = value.get("telemetry")
    if not all(
        isinstance(item, Mapping)
        for item in (
            attempt,
            pair,
            resource,
            comparability,
            agent,
            dependencies,
            storage,
            telemetry,
        )
    ):
        raise MeasurementError("measurement protocol is incomplete")
    numstability = dependencies.get("numstability")
    mathlib = dependencies.get("mathlib")
    preparation_isolation = dependencies.get("preparation_isolation")
    prefetch_lock = dependencies.get("prefetch_lock")
    if not all(
        isinstance(item, Mapping)
        for item in (numstability, mathlib, preparation_isolation, prefetch_lock)
    ):
        raise MeasurementError("measurement dependency policy is incomplete")
    if (
        value.get("schema_version") != 6
        or value.get("protocol_id") != "highambench-measured-v6"
        or value.get("status") != "measurement_ready"
        or not isinstance(value.get("lifecycle"), Mapping)
        or value["lifecycle"].get("task_corpus_locked") is not True
        or value["lifecycle"].get("measurement_ready") is not True
        or value["lifecycle"].get("campaign_creation_requires_clean_committed_inputs")
        is not True
        or attempt.get("wall_clock_seconds") != 7200
        or attempt.get("hidden_validation_command_max_seconds") != 1800
        or attempt.get("submission_boundary")
        != "authenticated root turn/completed with the final candidate.lean state"
        or attempt.get("scored_time")
        != "authenticated prompt release to the submission boundary"
        or attempt.get("hidden_validation_timing")
        != "starts after the submission boundary and is recorded separately from scored time"
        or attempt.get("intermediate_candidate_validation_allowed") is not False
        or attempt.get("token_limit") is not None
        or attempt.get("token_usage_recorded") is not True
        or attempt.get("conditions") != ["N", "L"]
        or pair.get("conditions_run_serially") is not True
        or pair.get("condition_order_is_execution_constraint") is not True
        or pair.get("resource_allocation_shared_by_both_conditions") is not False
        or pair.get("memory_coordinator_cgroup_shared_by_both_conditions") is not False
        or pair.get("binding_memory_limit_shared_by_both_conditions") is not False
        or pair.get("memory_condition_cgroup_shared_by_both_conditions") is not False
        or pair.get("parallelism_unit") != "condition attempt"
        or pair.get("parallel_attempts_allowed") is not False
        or pair.get("same_pair_attempts_may_overlap") is not False
        or pair.get("provider_active_attempt_limit_per_authentication") != 1
        or not isinstance(pair.get("provider_concurrency_reason"), str)
        or resource.get("physical_cores_per_attempt") != 4
        or resource.get("include_all_online_threads_of_selected_cores") is not True
        or resource.get("homogeneous_core_profile_required") is not True
        or resource.get("exact_core_ids_may_differ_between_attempts") is not True
        or resource.get("coordinator_memory_cgroup_required") is not True
        or resource.get("coordinator_memory_max") != "max"
        or resource.get("coordinator_memory_high") != "max"
        or resource.get("manager_memory_max_bytes") != MANAGER_MEMORY_BYTES
        or resource.get("condition_memory_max_bytes") != MEMORY_BYTES
        or resource.get("condition_memory_high") != "max"
        or resource.get("condition_memory_swap_max_bytes") != 0
        or resource.get("host_memory_admission_bytes_per_attempt")
        != HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
        or resource.get("host_memory_admission_is_physical_reservation")
        is not False
        or resource.get("all_condition_ancestors_memory_max_and_high_nonbinding")
        is not True
        or resource.get("fresh_unique_memory_cgroup_per_condition_required")
        is not True
        or resource.get("condition_memory_cgroup_reuse_allowed") is not False
        or resource.get("cpu_affinity_required") is not True
        or resource.get("cpu_affinity_assignment")
        != "root-cpuset-partition-and-systemd-system-unit-CPUAffinity"
        or resource.get("cpu_affinity_immutability")
        != "inherited-seccomp-denial-of-sched_setaffinity"
        or resource.get("cpu_syscall_architectures") != "native"
        or resource.get("cpuset_controller_required") is not True
        or resource.get("root_owned_cpu_guard_required") is not True
        or resource.get("cpuset_partition_required") is not True
        or resource.get("cpuset_partition_mode") != "root"
        or resource.get("cpu_partition_scope")
        != "campaign-wide-union-of-disjoint-attempt-slots"
        or resource.get("cpu_partition_idle_admission")
        != "sustained-all-slots-or-fail-before-provider-use"
        or resource.get("cpu_partition_idle_sample_seconds")
        != CPU_GUARD_IDLE_SAMPLE_SECONDS
        or resource.get("cpu_partition_maximum_busy_percent")
        != CPU_GUARD_MAXIMUM_BUSY_PERCENT
        or resource.get("cpu_partition_launch_manager")
        != "system-systemd-as-configured-unprivileged-uid"
        or resource.get("cpu_partition_release") != "empty-only"
        or resource.get("cpu_partition_userspace_exclusivity") is not True
        or resource.get("parallel_cpu_slots_disjoint") is not True
        or resource.get("foreign_process_signals_allowed") is not False
        or resource.get("foreign_process_cgroup_migration_allowed") is not False
        or resource.get("group_oom_policy")
        != "systemd-OOMPolicy-kill-and-memory.oom.group-1"
        or resource.get("memory_oom_group_required") is not True
        or resource.get("same_uid_processes_outside_benchmark_trusted") is not True
        or resource.get("dedicated_idle_host_required") is not False
        or resource.get("host_core_exclusive_locks_required") is not True
        or resource.get("single_coordinator_per_campaign") is not True
        or resource.get("memory_peak_metric")
        != "read-only lifetime high-water of the fresh condition memory cgroup"
        or resource.get("memory_peak_reset_allowed") is not False
        or resource.get("memory_peak_same_open_file_description_required")
        is not False
        or resource.get("memory_peak_read_after_cgroup_events_populated_zero")
        is not True
        or resource.get("memory_peak_read_before_condition_cgroup_teardown")
        is not True
        or resource.get("post_measurement_memory_reclaim")
        != "bounded numeric requests"
        or resource.get("memory_reclaim_eagain_means_partial_success") is not True
        or resource.get("memory_reclaim_exact_zero_required") is not False
        or resource.get("post_condition_parent_residue_diagnostics_required")
        is not True
        or resource.get("fail_closed_without_kernel_evidence") is not True
        or comparability.get("memory_peak_poolable_with_measured_v2") is not False
        or not isinstance(
            comparability.get("memory_peak_nonpoolability_reason"), str
        )
        or comparability.get("agent_parallelism_poolable_with_measured_v4")
        is not False
        or not isinstance(
            comparability.get("agent_parallelism_nonpoolability_reason"), str
        )
        or comparability.get("provider_concurrency_poolable_with_measured_v5")
        is not False
        or not isinstance(
            comparability.get("provider_concurrency_nonpoolability_reason"), str
        )
        or comparability.get(
            "host_developer_context_hash_match_required_for_cross_campaign_comparison"
        )
        is not True
        or resource.get("slurm_required") is not False
        or resource.get("slurm_supported") is not False
        or agent.get("model") != "gpt-6-sol"
        or agent.get("reasoning_effort") != "xhigh"
        or agent.get("subagents_enabled") is not False
        or agent.get("maximum_agent_threads_per_attempt") != 1
        or telemetry.get("record_and_verify_model_visible_host_developer_context")
        is not True
        or telemetry.get("host_developer_context_must_be_constant_within_campaign")
        is not True
        or preparation_isolation != PREPARATION_ISOLATION_CONTRACT
        or prefetch_lock != PREFETCH_LOCK_CONTRACT
        or numstability.get("editable") is not False
        or numstability.get("tracked_sources_may_be_modified") is not False
        or numstability.get("pristine_source_checkout_used_as_build_directory")
        is not False
        or numstability.get("derived_build_checkout_separate_from_source") is not True
        or numstability.get("pristine_checkout_created_after_all_lake_commands")
        is not True
        or numstability.get("fresh_derived_build_required_at_campaign_creation")
        is not False
        or numstability.get("reused_derived_build_requires_full_integrity_check")
        is not True
        or mathlib.get("editable") is not False
        or mathlib.get("tracked_sources_may_be_modified") is not False
        or mathlib.get("pristine_source_checkout_used_as_build_directory")
        is not False
        or mathlib.get("derived_build_checkout_separate_from_source") is not True
        or mathlib.get("pristine_checkout_created_after_all_lake_commands")
        is not True
        or storage.get("results_and_cache_outside_every_git_worktree") is not True
        or storage.get("symlink_components_allowed") is not False
        or storage.get("results_and_cache_may_overlap") is not False
        or storage.get("current_user_ownership_required") is not True
        or storage.get("group_or_other_permission_bits_allowed") is not False
        or storage.get("required_root_mode") != "0700"
        or storage.get("campaign_canonical_results_root_bound_in_lock") is not True
        or storage.get("generated_results_or_runtime_inside_repository_allowed")
        is not False
        or storage.get("codex_state_under_attempt_root") is not True
        or storage.get("agent_tmp_bind_under_attempt_root") is not True
        or storage.get("infrastructure_retry_within_campaign") is not True
        or storage.get("infrastructure_incident_archives_authenticated") is not True
    ):
        raise MeasurementError("measurement protocol differs from the implemented contract")
    return value


def _portable_task_corpus_manifest(benchmark_root: Path) -> dict[str, Any]:
    """Hash the fixed task corpus without embedding its checkout location."""

    raw = manifest_for_tree(
        benchmark_root,
        [benchmark_root / relative for relative in TASK_SCOPE_RELATIVES],
    )
    return {
        "schema_version": 1,
        "roots": [relative.as_posix() for relative in TASK_SCOPE_RELATIVES],
        "files": raw["files"],
    }


def _verify_task_corpus_lock(benchmark_root: Path) -> dict[str, Any]:
    lock_path = benchmark_root / TASK_LOCK_RELATIVE
    lock = read_object(lock_path, kind="highambench-task-corpus-lock")
    current = _portable_task_corpus_manifest(benchmark_root)
    digest = canonical_digest(current)
    if (
        lock.get("schema_version") != 1
        or lock.get("status") != "locked"
        or lock.get("manifest_sha256") != digest
        or lock.get("file_count") != len(current["files"])
        or lock.get("scope_roots") != current["roots"]
    ):
        raise MeasurementError(
            "fixed task corpus differs from metadata/task_corpus_lock.json"
        )
    return {
        "manifest_sha256": digest,
        "file_count": len(current["files"]),
        "lock_sha256": sha256_file(lock_path),
    }


def _repository_root(benchmark_root: Path) -> Path:
    root = Path(_git_read_only(benchmark_root, "rev-parse", "--show-toplevel"))
    root = root.resolve(strict=True)
    try:
        benchmark_root.resolve().relative_to(root)
    except ValueError as error:
        raise MeasurementError("benchmark root is outside its Git checkout") from error
    return root


def _require_controlled_checkout_clean(benchmark_root: Path) -> dict[str, Any]:
    """Require the task, prompt, and runner inputs to be committed before locking."""

    repository = _repository_root(benchmark_root)
    _assert_safe_local_git_policy(repository, label="benchmark repository")
    controlled = [
        *TASK_SCOPE_RELATIVES,
        TASK_LOCK_RELATIVE,
        Path("measurement_prompt.md"),
        Path("condition_prompts/L.md"),
        Path("metadata/measurement_protocol.json"),
        CPU_GUARD_SOURCE_RELATIVE,
        CPU_GUARD_FRONTEND_SOURCE_RELATIVE,
        Path("scripts"),
        Path("tools/validator.py"),
        Path("tools/lean_isolated.py"),
        Path("tools/sandbox_paths.py"),
        Path("__init__.py"),
        Path("tools/__init__.py"),
        Path("tools/dependency_audit.lean"),
        Path("tools/offline_shell.c"),
        Path("tools/common.py"),
        Path("tools/hashes.py"),
    ]
    pathspecs = [
        (benchmark_root / relative).resolve().relative_to(repository).as_posix()
        for relative in controlled
    ]
    status = _git_read_only(
        repository,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=all",
        "--",
        *pathspecs,
    )
    index_status = _git_read_only(
        repository,
        "diff-index",
        "--cached",
        "--name-status",
        "--no-renames",
        "--no-ext-diff",
        "--no-textconv",
        "HEAD",
        "--",
        *pathspecs,
    )
    if status or index_status:
        raise MeasurementError(
            "controlled task/prompt/runner files are not committed and clean; "
            "campaign creation is forbidden:\n" + (status or index_status)
        )
    return {
        "repository": str(repository),
        "head": _git_read_only(repository, "rev-parse", "HEAD"),
        "pathspecs": pathspecs,
        "clean": True,
    }


def _corpus_manifest(benchmark_root: Path) -> dict[str, Any]:
    roots = [
        benchmark_root / "tasks",
        benchmark_root / "shared",
        benchmark_root / "metadata" / "controlled",
        benchmark_root / "metadata" / "run_order.json",
        benchmark_root / "measurement_prompt.md",
        benchmark_root / "condition_prompts" / "L.md",
        benchmark_root / "metadata" / "measurement_protocol.json",
        benchmark_root / TASK_LOCK_RELATIVE,
    ]
    return manifest_for_tree(benchmark_root, roots)


def _execution_manifest(benchmark_root: Path) -> dict[str, Any]:
    roots = [
        benchmark_root / CPU_GUARD_SOURCE_RELATIVE,
        benchmark_root / CPU_GUARD_FRONTEND_SOURCE_RELATIVE,
        benchmark_root / "scripts",
        benchmark_root / "tools" / "validator.py",
        benchmark_root / "tools" / "lean_isolated.py",
        benchmark_root / "tools" / "sandbox_paths.py",
        benchmark_root / "__init__.py",
        benchmark_root / "tools" / "__init__.py",
        benchmark_root / "tools" / "dependency_audit.lean",
        benchmark_root / "tools" / "offline_shell.c",
        benchmark_root / "tools" / "common.py",
        benchmark_root / "tools" / "hashes.py",
    ]
    return manifest_for_tree(benchmark_root, roots)


def _trusted_git_environment() -> dict[str, str]:
    inherited_keys = (
        "PATH",
        "HTTP_PROXY",
        "HTTPS_PROXY",
        "NO_PROXY",
        "http_proxy",
        "https_proxy",
        "no_proxy",
        "SSL_CERT_DIR",
        "SSL_CERT_FILE",
    )
    environment = {
        key: os.environ[key] for key in inherited_keys if key in os.environ
    }
    environment.update(
        {
            "HOME": "/nonexistent",
            "XDG_CONFIG_HOME": "/nonexistent",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_ATTR_NOSYSTEM": "1",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_TERMINAL_PROMPT": "0",
            "LANG": "C",
            "LC_ALL": "C",
        }
    )
    return environment


def _git_read_only(checkout: Path, *arguments: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        env=_trusted_git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    if completed.returncode != 0:
        raise MeasurementError(
            f"read-only git {' '.join(arguments)} failed in {checkout}: "
            f"{completed.stderr.strip()}"
        )
    return completed.stdout.strip()


def _assert_safe_local_git_policy(repository: Path, *, label: str) -> None:
    try:
        from .prepare_runtime import (
            PreparationError,
            assert_nonexecuting_git_config,
        )
    except ImportError:  # pragma: no cover - direct execution
        from prepare_runtime import (  # type: ignore
            PreparationError,
            assert_nonexecuting_git_config,
        )
    try:
        assert_nonexecuting_git_config(repository, label=label)
    except PreparationError as error:
        raise MeasurementError(str(error)) from error


def _benchmark_git_identity(repository: Path) -> dict[str, Any]:
    """Inventory the benchmark checkout without entering nested repositories."""

    root = repository.resolve(strict=True)
    _assert_safe_local_git_policy(root, label="benchmark repository")
    status = _git_read_only(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=all",
    )
    index_status = _git_read_only(
        root,
        "diff-index",
        "--cached",
        "--name-status",
        "--no-renames",
        "--no-ext-diff",
        "--no-textconv",
        "HEAD",
        "--",
    )
    status_lines = status.splitlines()
    status_lines.extend(
        f"INDEX {line}"
        for line in index_status.splitlines()
        if line and line not in status_lines
    )
    return {
        "root": str(root),
        "commit": _git_read_only(root, "rev-parse", "HEAD"),
        "branch": _git_read_only(root, "branch", "--show-current") or None,
        "dirty": bool(status or index_status),
        "status_lines": status_lines,
    }


def git_identity(repository: Path) -> dict[str, Any]:
    """Compatibility entry point backed by the hardened benchmark inventory."""

    return _benchmark_git_identity(repository)


def _snapshot_path(
    raw: Any, label: str, *, expect_directory: bool = True
) -> Path:
    if not isinstance(raw, str):
        raise MeasurementError(f"runtime snapshot lacks {label}")
    path = Path(raw)
    if not path.is_absolute():
        raise MeasurementError(f"runtime {label} is not an absolute path")
    cursor = Path(path.anchor)
    for component in path.parts[1:]:
        cursor /= component
        if cursor.is_symlink():
            raise MeasurementError(
                f"runtime {label} contains a symlink component: {cursor}"
            )
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise MeasurementError(f"runtime {label} is missing: {path}") from error
    valid = resolved.is_dir() if expect_directory else resolved.is_file()
    if not valid:
        expected = "directory" if expect_directory else "file"
        raise MeasurementError(f"runtime {label} is not a regular {expected}")
    return resolved


def _paths_overlap(first: Path, second: Path) -> bool:
    return (
        first == second
        or first in second.parents
        or second in first.parents
    )


def _verify_runtime_checkout(
    checkout: Path,
    expected_commit: str,
    *,
    label: str,
    include_ignored: bool,
) -> str:
    """Authenticate a detached checkout using read-only Git operations."""

    try:
        from .prepare_runtime import (
            PreparationError,
            assert_index_exactly_matches_head,
            assert_nonexecuting_git_config,
            command_environment,
            locate_executable,
        )
    except ImportError:  # pragma: no cover - direct execution
        from prepare_runtime import (  # type: ignore
            PreparationError,
            assert_index_exactly_matches_head,
            assert_nonexecuting_git_config,
            command_environment,
            locate_executable,
        )
    try:
        assert_nonexecuting_git_config(checkout, label=label)
    except PreparationError as error:
        raise MeasurementError(str(error)) from error
    if _git_read_only(checkout, "rev-parse", "HEAD").lower() != expected_commit:
        raise MeasurementError(f"{label} moved from its locked commit")
    symbolic = subprocess.run(
        ["git", "-C", str(checkout), "symbolic-ref", "-q", "HEAD"],
        env=command_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    if symbolic.returncode != 1:
        raise MeasurementError(f"{label} is not detached")
    try:
        assert_index_exactly_matches_head(
            checkout, locate_executable("git"), label=label
        )
    except PreparationError as error:
        raise MeasurementError(str(error)) from error
    status_arguments = [
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=all",
    ]
    if include_ignored:
        status_arguments.append("--ignored=matching")
    if _git_read_only(checkout, *status_arguments):
        raise MeasurementError(f"{label} is not pristine")
    return _git_read_only(checkout, "rev-parse", "HEAD^{tree}").lower()


def _load_runtime_snapshot(path: Path, *, deep: bool = False) -> dict[str, Any]:
    snapshot_path = path.resolve()
    snapshot = read_object(snapshot_path)
    if snapshot.get("schema_version") != 3:
        raise MeasurementError("unsupported runtime snapshot schema")
    source = snapshot.get("source")
    condition_l = snapshot.get("condition_l")
    runtime = snapshot.get("runtime")
    if not all(isinstance(item, Mapping) for item in (source, condition_l, runtime)):
        raise MeasurementError("runtime snapshot is incomplete")
    if snapshot.get("preparation_isolation") != PREPARATION_ISOLATION_CONTRACT:
        raise MeasurementError(
            "runtime was not built under the required filesystem capability boundary"
        )
    prefetch = snapshot.get("prefetch")
    binary_prefetch = (
        prefetch.get("binary_cache") if isinstance(prefetch, Mapping) else None
    )
    toolchain_prefetch = (
        prefetch.get("lean_toolchain") if isinstance(prefetch, Mapping) else None
    )
    artifacts = (
        binary_prefetch.get("mathlib_ltar_artifacts")
        if isinstance(binary_prefetch, Mapping)
        else None
    )
    commit_manifest = (
        binary_prefetch.get("mathlib_commit_manifest")
        if isinstance(binary_prefetch, Mapping)
        else None
    )
    leantar_prefetch = (
        binary_prefetch.get("leantar")
        if isinstance(binary_prefetch, Mapping)
        else None
    )
    proofwidgets_prefetch = (
        binary_prefetch.get("proofwidgets_release")
        if isinstance(binary_prefetch, Mapping)
        else None
    )
    ltar_download_safety = (
        binary_prefetch.get("mathlib_ltar_download_safety")
        if isinstance(binary_prefetch, Mapping)
        else None
    )
    if (
        not isinstance(prefetch, Mapping)
        or prefetch.get("completed_before_first_lake_process") is not True
        or prefetch.get("remote_downloads_after_first_lake_process") is not False
        or prefetch.get("lake_network") != "offline-private-unshare"
        or prefetch.get("local_source_stores_visible_to_lake") is not False
        or not isinstance(prefetch.get("dependency_sources"), list)
        or not isinstance(toolchain_prefetch, Mapping)
        or toolchain_prefetch.get("phase")
        != "completed-before-first-lake-process"
        or toolchain_prefetch.get("toolchain") != LEAN_TOOLCHAIN
        or toolchain_prefetch.get("archive_size")
        != LEAN_TOOLCHAIN_ARCHIVE_BYTES
        or toolchain_prefetch.get("archive_sha256")
        != LEAN_TOOLCHAIN_ARCHIVE_SHA256
        or not isinstance(toolchain_prefetch.get("integrity"), Mapping)
        or toolchain_prefetch["integrity"].get("digest")
        != LEAN_TOOLCHAIN_TREE_SHA256
        or toolchain_prefetch.get("lake_sha256")
        != LEAN_TOOLCHAIN_LAKE_SHA256
        or toolchain_prefetch.get("lean_sha256")
        != LEAN_TOOLCHAIN_LEAN_SHA256
        or toolchain_prefetch.get("private_copy") is not True
        or toolchain_prefetch.get("source_tree_not_mounted") is not True
        or toolchain_prefetch.get("archive_download_observed") is not True
        or toolchain_prefetch.get("archive_authenticated_before_extraction")
        is not True
        or toolchain_prefetch.get("archive_kernel_file_size_limit_bytes")
        != LEAN_TOOLCHAIN_ARCHIVE_BYTES
        or toolchain_prefetch.get(
            "decompressed_tar_kernel_file_size_limit_bytes"
        )
        != MAX_LEAN_TOOLCHAIN_TAR_BYTES
        or commit_manifest != MATHLIB_COMMIT_MANIFEST_RECORD
        or not isinstance(artifacts, Mapping)
        or artifacts.get("count") != MATHLIB_CACHE_ARTIFACT_COUNT
        or artifacts.get("total_bytes") != MATHLIB_CACHE_ARTIFACT_BYTES
        or artifacts.get("content_manifest_sha256")
        != MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256
        or binary_prefetch.get("post_lake_artifact_verification") != artifacts
        or not isinstance(leantar_prefetch, Mapping)
        or leantar_prefetch.get("version") != PREFETCH_LOCK_CONTRACT["leantar_version"]
        or leantar_prefetch.get("binary_sha256")
        != PREFETCH_LOCK_CONTRACT["leantar_binary_sha256"]
        or not isinstance(proofwidgets_prefetch, Mapping)
        or proofwidgets_prefetch.get("sha256")
        != PREFETCH_LOCK_CONTRACT["proofwidgets_release_sha256"]
        or ltar_download_safety
        != {
            "kernel_file_size_limit_each_curl_process": True,
            "remaining_aggregate_bound_applied_before_each_batch": True,
            "maximum_aggregate_bytes": MAX_MATHLIB_CACHE_DOWNLOAD_BYTES,
        }
    ):
        raise MeasurementError("runtime has no authenticated offline prefetch record")
    numstability = source.get("numstability")
    derived_build = source.get("derived_build")
    mathlib = source.get("mathlib")
    derived_mathlib = source.get("derived_mathlib_package")
    lean = source.get("lean")
    if not all(
        isinstance(item, Mapping)
        for item in (numstability, derived_build, mathlib, derived_mathlib, lean)
    ):
        raise MeasurementError("runtime dependency identity is incomplete")
    commit = numstability.get("commit")
    checkout_raw = numstability.get("checkout")
    if (
        not isinstance(commit, str)
        or re.fullmatch(r"[0-9a-f]{40}", commit) is None
    ):
        raise MeasurementError("runtime has no exact NumStability commit/checkout")
    if (
        numstability.get("repository") != NUMSTABILITY_REPOSITORY
        or numstability.get("ref") != NUMSTABILITY_REF
        or commit != NUMSTABILITY_REF
    ):
        raise MeasurementError(
            "runtime snapshot is not the exact Higham commit used in the paper"
        )
    checkout = _snapshot_path(checkout_raw, "pristine NumStability checkout")
    build_checkout = _snapshot_path(
        derived_build.get("checkout"), "derived NumStability build checkout"
    )
    mathlib_checkout = _snapshot_path(
        mathlib.get("checkout"), "pristine Mathlib checkout"
    )
    derived_mathlib_checkout = _snapshot_path(
        derived_mathlib.get("checkout"), "derived Mathlib package"
    )
    packages_root = _snapshot_path(
        derived_build.get("packages_root"), "derived packages root"
    )
    pristine_and_build = (checkout, mathlib_checkout, build_checkout)
    if any(
        _paths_overlap(first, second)
        for index, first in enumerate(pristine_and_build)
        for second in pristine_and_build[index + 1 :]
    ):
        raise MeasurementError("pristine dependency and derived build trees overlap")
    if (
        derived_mathlib_checkout != packages_root / "mathlib"
        or not _paths_overlap(derived_mathlib_checkout, build_checkout)
        or packages_root.parent != build_checkout / ".lake"
    ):
        raise MeasurementError("derived Mathlib/package paths escape the build tree")
    if (
        numstability.get("read_only") is not True
        or numstability.get("git_role") != "pristine-source"
        or numstability.get("lake_directory_absent") is not True
        or mathlib.get("read_only") is not True
        or mathlib.get("git_role") != "pristine-source"
        or mathlib.get("lake_directory_absent") is not True
        or derived_build.get("read_only") is not True
        or derived_build.get("git_role") != "derived-build"
        or derived_build.get("lake_preparation_filesystem_isolated") is not True
        or derived_mathlib.get("read_only") is not True
        or derived_mathlib.get("git_role") != "derived-package"
    ):
        raise MeasurementError("runtime source/build roles are not immutable and separate")
    for pristine, label in (
        (checkout, "NumStability"),
        (mathlib_checkout, "Mathlib"),
    ):
        if (pristine / ".lake").exists():
            raise MeasurementError(
                f"pristine {label} checkout contains build artifacts"
            )
    if any(
        candidate.lstat().st_mode & 0o222
        for candidate in (
            checkout,
            checkout / "NumStability",
            checkout / "docs",
            mathlib_checkout,
            build_checkout,
            derived_mathlib_checkout,
        )
    ):
        raise MeasurementError("runtime cache has writable dependency directories")
    for required in (
        checkout / "NumStability.lean",
        checkout / "docs" / "LIBRARY_LOOKUP.md",
    ):
        if not required.is_file() or required.is_symlink() or required.lstat().st_mode & 0o222:
            raise MeasurementError(f"runtime dependency file is not immutable: {required}")
    build_lib = _snapshot_path(
        condition_l.get("lean_build_lib"), "NumStability olean tree"
    )
    try:
        build_lib.relative_to(build_checkout)
        derived_mathlib_checkout.relative_to(build_checkout)
        packages_root.relative_to(build_checkout)
    except ValueError as error:
        raise MeasurementError(
            "derived build or mathlib path escapes the derived checkout"
        ) from error
    if (
        Path(str(condition_l.get("numstability_source"))).resolve() != checkout
        or Path(str(condition_l.get("numstability_derived_build"))).resolve()
        != build_checkout
        or Path(str(condition_l.get("library_lookup"))).resolve()
        != checkout / "docs" / "LIBRARY_LOOKUP.md"
        or build_lib != build_checkout / ".lake" / "build" / "lib" / "lean"
        or Path(str(condition_l.get("mathlib_source"))).resolve()
        != mathlib_checkout
        or Path(str(condition_l.get("mathlib_derived_package"))).resolve()
        != derived_mathlib_checkout
        or Path(str(condition_l.get("derived_packages_root"))).resolve()
        != packages_root
        or condition_l.get("mount_mode") != "read-only"
    ):
        raise MeasurementError("condition L paths disagree with runtime provenance")
    if mathlib.get("commit") != MATHLIB_COMMIT:
        raise MeasurementError("runtime snapshot uses the wrong mathlib commit")
    if mathlib.get("repository") != MATHLIB_REPOSITORY:
        raise MeasurementError("runtime snapshot uses the wrong mathlib repository")
    if lean.get("toolchain") != LEAN_TOOLCHAIN:
        raise MeasurementError("runtime snapshot uses the wrong Lean toolchain")
    for key in ("source_manifest", "runtime_manifest"):
        manifest_raw = runtime.get(key)
        digest = runtime.get(f"{key}_sha256")
        if not isinstance(manifest_raw, str) or not isinstance(digest, str):
            raise MeasurementError(f"runtime snapshot lacks {key}")
        manifest_path = Path(manifest_raw).resolve()
        if not manifest_path.is_file() or sha256_file(manifest_path) != digest:
            raise MeasurementError(f"runtime snapshot {key} is stale")
    numstability_tree = _verify_runtime_checkout(
        checkout, commit, label="pristine NumStability checkout", include_ignored=True
    )
    build_tree = _verify_runtime_checkout(
        build_checkout,
        commit,
        label="derived NumStability build",
        include_ignored=False,
    )
    mathlib_tree = _verify_runtime_checkout(
        mathlib_checkout,
        str(mathlib.get("commit")),
        label="pristine Mathlib checkout",
        include_ignored=True,
    )
    derived_mathlib_tree = _verify_runtime_checkout(
        derived_mathlib_checkout,
        str(mathlib.get("commit")),
        label="derived Mathlib package",
        include_ignored=False,
    )
    if (
        numstability_tree != numstability.get("git_tree")
        or build_tree != numstability_tree
        or mathlib_tree != mathlib.get("git_tree")
        or derived_mathlib_tree != mathlib_tree
        or derived_mathlib.get("git_tree") != mathlib_tree
    ):
        raise MeasurementError("runtime pristine and derived Git trees disagree")
    if deep:
        try:
            from .prepare_runtime import (
                PreparationError,
                assert_no_hardlinked_regular_files,
                assert_read_only,
                cache_integrity,
            )
        except ImportError:  # pragma: no cover - direct execution
            from prepare_runtime import (  # type: ignore
                PreparationError,
                assert_no_hardlinked_regular_files,
                assert_read_only,
                cache_integrity,
            )
        source_manifest_path = Path(str(runtime["source_manifest"])).resolve()
        source_manifest = read_object(source_manifest_path)
        source_policy = source_manifest.get("policy")
        source_numstability = source_manifest.get("numstability")
        source_mathlib = source_manifest.get("mathlib")
        source_derived_mathlib = source_manifest.get("derived_mathlib_package")
        source_build = source_manifest.get("build")
        source_tools = source_manifest.get("tools_observed_at_cache_creation")
        source_prefetch = source_manifest.get("prefetch")
        if not all(
            isinstance(item, Mapping)
            for item in (
                source_policy,
                source_numstability,
                source_mathlib,
                source_derived_mathlib,
                source_build,
                source_tools,
                source_prefetch,
            )
        ):
            raise MeasurementError("source manifest has incomplete cache records")
        if (
            source_manifest.get("schema_version") != 3
            or source_policy.get("numstability_sources_may_be_modified") is not False
            or source_policy.get("mathlib_sources_may_be_modified") is not False
            or source_policy.get(
                "pristine_numstability_checkout_used_as_build_directory"
            )
            is not False
            or source_policy.get("pristine_mathlib_checkout_used_as_build_directory")
            is not False
            or source_policy.get("lake_completed_before_pristine_checkouts_created")
            is not True
            or source_policy.get("lake_may_run_after_pristine_checkouts_created")
            is not False
            or source_policy.get("lake_preparation_host_root_was_not_mounted")
            is not True
            or source_policy.get(
                "lake_preparation_only_writable_host_tree_was_derived_build"
            )
            is not True
            or source_policy.get(
                "lake_preparation_nested_user_namespaces_disabled"
            )
            is not True
            or source_policy.get("lake_preparation_network_egress_was_none")
            is not True
            or source_policy.get("all_dependencies_prefetched_before_first_lake")
            is not True
            or source_policy.get(
                "local_repository_mirrors_were_not_mounted_into_lake"
            )
            is not True
            or source_manifest.get("preparation_isolation")
            != PREPARATION_ISOLATION_CONTRACT
            or source_prefetch != prefetch
            or source_tools.get("lake_network") != "offline-private-unshare"
            or source_tools.get("explicit_local_repository_mounts") != []
            or source_tools.get("preparation_script_sha256")
            != sha256_file(Path(__file__).with_name("prepare_runtime.py"))
        ):
            raise MeasurementError("source manifest violates immutable-upstream policy")
        if (
            Path(str(source_numstability.get("checkout"))).resolve() != checkout
            or Path(str(source_mathlib.get("checkout"))).resolve()
            != mathlib_checkout
            or Path(str(source_derived_mathlib.get("checkout"))).resolve()
            != derived_mathlib_checkout
            or Path(str(source_build.get("derived_checkout"))).resolve()
            != build_checkout
            or Path(str(source_build.get("packages_root"))).resolve()
            != packages_root
        ):
            raise MeasurementError("source manifest dependency paths disagree")
        expected_source_integrity = source_numstability.get("integrity")
        expected_mathlib_integrity = source_mathlib.get("integrity")
        expected_build_integrity = source_build.get("integrity")
        assert_read_only(checkout)
        assert_read_only(mathlib_checkout)
        assert_read_only(build_checkout)
        try:
            assert_no_hardlinked_regular_files(
                checkout, label="pristine NumStability source"
            )
            assert_no_hardlinked_regular_files(
                mathlib_checkout, label="pristine Mathlib source"
            )
        except PreparationError as error:
            raise MeasurementError(str(error)) from error
        if cache_integrity(checkout) != expected_source_integrity:
            raise MeasurementError("pristine NumStability source was tampered")
        if cache_integrity(mathlib_checkout) != expected_mathlib_integrity:
            raise MeasurementError("pristine Mathlib source was tampered")
        if cache_integrity(build_checkout) != expected_build_integrity:
            raise MeasurementError("derived NumStability build cache was tampered")
    return snapshot


def _package_lean_paths(packages_root: Path) -> list[Path]:
    paths: list[Path] = []
    mathlib = packages_root / "mathlib" / ".lake" / "build" / "lib" / "lean"
    if not mathlib.is_dir():
        raise MeasurementError(f"mathlib build output is missing: {mathlib}")
    paths.append(mathlib)
    for package in sorted(packages_root.iterdir(), key=lambda path: path.name):
        built = package / ".lake" / "build" / "lib" / "lean"
        if package.name != "mathlib" and built.is_dir():
            paths.append(built)
    return paths


def _compile_offline_shell(
    benchmark_root: Path, environment_root: Path, commands_log: Path
) -> Path:
    compiler = shutil.which("cc")
    if compiler is None:
        raise MeasurementError("a C compiler is required to build the offline shell")
    source = benchmark_root / "tools" / "offline_shell.c"
    output = environment_root / "offline-shell"
    command = [
        compiler,
        "-std=c11",
        "-O2",
        "-Wall",
        "-Wextra",
        "-Werror",
        str(source.resolve()),
        "-o",
        str(output.resolve()),
    ]
    result = run_captured(command, cwd=benchmark_root, timeout=120)
    append_jsonl(commands_log, {"kind": "environment-command", **result.as_record()})
    if result.returncode != 0:
        raise MeasurementError(f"offline-shell build failed: {result.stderr}")
    output.chmod(0o555)
    return output


def _lexical_external_path(raw: Path, label: str) -> Path:
    """Return an absolute path without erasing lexical symlink evidence."""

    raw = raw.expanduser()
    path = raw if raw.is_absolute() else Path.cwd() / raw
    if ".." in path.parts:
        raise MeasurementError(f"{label} must not contain '..' path components")
    if not path.anchor:
        raise MeasurementError(f"{label} is not an absolute path")
    return path


def _nearest_real_directory(path: Path, label: str) -> Path:
    """Find the nearest existing ancestor while rejecting every symlink."""

    cursor = Path(path.anchor)
    nearest = cursor
    for component in path.parts[1:]:
        cursor /= component
        try:
            status = cursor.lstat()
        except FileNotFoundError:
            return nearest
        except OSError as error:
            raise MeasurementError(f"cannot inspect {label} component: {cursor}") from error
        if stat.S_ISLNK(status.st_mode):
            raise MeasurementError(
                f"{label} contains a symlink component: {cursor}"
            )
        if not stat.S_ISDIR(status.st_mode):
            raise MeasurementError(
                f"{label} contains a non-directory component: {cursor}"
            )
        nearest = cursor
    return nearest


def _reject_git_worktree(directory: Path, label: str) -> None:
    """Reject a target whose nearest existing directory is in any worktree."""

    environment = _trusted_git_environment()
    environment["GIT_DISCOVERY_ACROSS_FILESYSTEM"] = "1"
    try:
        completed = subprocess.run(
            ["git", "-C", str(directory), "rev-parse", "--show-toplevel"],
            env=environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
            check=False,
        )
    except OSError as error:
        raise MeasurementError(
            f"cannot establish whether {label} is outside a Git worktree"
        ) from error
    if completed.returncode == 0:
        worktree = completed.stdout.strip()
        if not worktree:
            raise MeasurementError(
                f"cannot establish the Git worktree containing {label}"
            )
        raise MeasurementError(
            f"{label} must be outside every Git worktree; found {worktree}"
        )
    if "not a git repository" not in completed.stderr.lower():
        raise MeasurementError(
            f"cannot establish whether {label} is outside a Git worktree: "
            f"{completed.stderr.strip()}"
        )


def _external_private_directory(
    raw: Path, label: str, *, create: bool
) -> Path:
    """Validate an external, real, private, user-owned directory.

    The pre-creation worktree check deliberately runs from the nearest existing
    ancestor.  This catches a nonexistent ``results`` path below an unrelated
    checkout before any campaign files are created there.
    """

    try:
        from .prepare_runtime import PreparationError, _secure_walk_directory
    except ImportError:  # pragma: no cover - direct execution
        from prepare_runtime import (  # type: ignore
            PreparationError,
            _secure_walk_directory,
        )

    path = _lexical_external_path(raw, label)
    # Preserve an early, read-only worktree diagnostic.  The subsequent pinned
    # walk is authoritative against races before any creation takes place.
    lexical_nearest = _nearest_real_directory(path, label)
    _reject_git_worktree(lexical_nearest, label)
    try:
        nearest = _secure_walk_directory(path, label=label, create=False)
    except PreparationError as error:
        raise MeasurementError(str(error)) from error
    _reject_git_worktree(nearest, label)
    if create:
        try:
            completed = _secure_walk_directory(path, label=label, create=True)
        except PreparationError as error:
            raise MeasurementError(str(error)) from error
        if completed != path:
            raise MeasurementError(f"unable to create {label}: {path}")
    elif nearest != path:
        raise MeasurementError(f"{label} does not exist: {path}")

    try:
        nearest_after = _secure_walk_directory(path, label=label, create=False)
    except PreparationError as error:
        raise MeasurementError(str(error)) from error
    if nearest_after != path:
        raise MeasurementError(f"{label} is not an existing directory: {path}")
    _reject_git_worktree(path, label)
    status = path.lstat()
    if (
        not stat.S_ISDIR(status.st_mode)
        or status.st_uid != os.getuid()
        or stat.S_IMODE(status.st_mode) != 0o700
    ):
        raise MeasurementError(
            f"{label} must be a real, private, user-owned directory with exact mode 0700"
        )
    return path


def _prepare_campaign_runtime(
    benchmark_root: Path,
    environment_root: Path,
    cache_base: Path,
    toolchain_root: Path,
    commands_log: Path,
) -> Path:
    """Build a fresh official runtime during campaign creation.

    A unique empty cache namespace prevents campaign creation from trusting a
    caller-supplied or previously populated ignored ``.lake`` tree.  The
    preparation script prefetches and authenticates every dependency before
    running Lake offline in an independently cloned derived checkout. Only
    after every Lake command has finished does it clone and seal separate
    pristine NumStability and Mathlib source checkouts from the private stores.
    """

    cache_base = _external_private_directory(
        cache_base, "runtime cache base", create=False
    )
    fresh_cache = cache_base / f"campaign-runtime-{uuid.uuid4().hex}"
    if fresh_cache.exists() or fresh_cache.is_symlink():
        raise MeasurementError("fresh campaign runtime cache path already exists")
    output = environment_root / "runtime-preparation"
    if output.exists() or output.is_symlink():
        raise MeasurementError("campaign runtime output already exists")
    script = _script_path(benchmark_root, "prepare_runtime.py")
    git = shutil.which("git")
    bwrap = shutil.which("bwrap")
    unshare = shutil.which("unshare")
    curl = shutil.which("curl")
    zstd = shutil.which("zstd")
    if any(tool is None for tool in (git, bwrap, unshare, curl, zstd)):
        raise MeasurementError(
            "Git, curl, zstd, Bubblewrap, and unshare are required for "
            "campaign runtime preparation"
        )
    command = [
        sys.executable,
        str(script),
        "--benchmark-root",
        str(benchmark_root),
        "--cache-root",
        str(fresh_cache),
        "--output-dir",
        str(output),
        "--source-repository",
        NUMSTABILITY_REPOSITORY,
        "--git-bin",
        str(Path(git).resolve()),
        "--unshare-bin",
        str(Path(str(unshare)).resolve()),
        "--bwrap-bin",
        str(Path(str(bwrap)).resolve()),
        "--curl-bin",
        str(Path(str(curl)).resolve()),
        "--zstd-bin",
        str(Path(str(zstd)).resolve()),
    ]
    result = run_captured(command, timeout=4 * 60 * 60)
    append_jsonl(
        commands_log,
        {"kind": "fresh-campaign-runtime-build", **result.as_record()},
    )
    if result.returncode != 0:
        raise MeasurementError(
            "fresh campaign runtime preparation failed:\n"
            + result.stdout[-4000:]
            + result.stderr[-4000:]
        )
    snapshot = output / "snapshot.json"
    printed = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if printed != [str(snapshot)] or not snapshot.is_file() or snapshot.is_symlink():
        raise MeasurementError("runtime preparation did not emit its exact snapshot")
    return snapshot


def _verify_reused_runtime_location(
    runtime: Mapping[str, Any], cache_base: Path
) -> None:
    source = runtime["source"]
    for label, raw in (
        ("NumStability source", source["numstability"]["checkout"]),
        ("NumStability build", source["derived_build"]["checkout"]),
        ("Mathlib source", source["mathlib"]["checkout"]),
    ):
        candidate = _snapshot_path(raw, label)
        if not candidate.is_relative_to(cache_base):
            raise MeasurementError(
                f"reused {label} is outside the selected runtime cache base"
            )


def _compile_shared(
    benchmark_root: Path,
    environment_root: Path,
    toolchain_root: Path,
    packages_root: Path,
    commands_log: Path,
) -> tuple[Path, dict[str, Any]]:
    lean = toolchain_root / "bin" / "lean"
    if not lean.is_file():
        raise MeasurementError(f"Lean binary is missing: {lean}")
    output_root = environment_root / "shared-olean"
    corpus_files = _portable_task_corpus_manifest(benchmark_root)["files"]
    sources = sorted(
        benchmark_root / str(entry["path"])
        for entry in corpus_files
        if re.fullmatch(
            r"shared/VSCLReuse/P[0-9]{2}/Definitions\.lean",
            str(entry["path"]),
        )
    )
    if not sources or sources != sorted(
        (benchmark_root / "shared" / "VSCLReuse").glob("P[0-9][0-9]/Definitions.lean")
    ):
        raise MeasurementError("paper definition files differ from the locked corpus")
    environment = dict(os.environ)
    for source in sources:
        paper_id = source.parent.name
        paper_root = output_root / paper_id
        module_root = paper_root / "VSCLReuse" / paper_id
        module_root.mkdir(parents=True)
        lean_paths = [
            paper_root,
            *_package_lean_paths(packages_root),
            toolchain_root / "lib" / "lean",
        ]
        environment["LEAN_PATH"] = ":".join(
            str(path.resolve()) for path in lean_paths
        )
        stem = source.stem
        olean = module_root / f"{stem}.olean"
        command = [
            str(lean.resolve()),
            "-o",
            str(olean.resolve()),
            str(source.resolve()),
        ]
        with host_limits.command_scope(
            command, cwd=benchmark_root, environment=environment, timeout=600
        ) as bounded:
            result = run_captured(bounded, cwd=benchmark_root, env=environment, timeout=600)
        append_jsonl(commands_log, {"kind": "environment-command", **result.as_record()})
        if result.returncode != 0:
            raise MeasurementError(
                f"shared definition build failed for {source.name}:\n"
                f"{result.stdout}{result.stderr}"
            )
    manifest = manifest_for_tree(environment_root, [output_root])
    for path in output_root.rglob("*"):
        if path.is_file():
            path.chmod(0o444)
        elif path.is_dir():
            path.chmod(0o555)
    output_root.chmod(0o555)
    return output_root, manifest


def _complete_toolchain_integrity(root: Path) -> dict[str, Any]:
    """Authenticate every entry that campaign sandboxes can see."""

    root = root.resolve(strict=True)
    digest = hashlib.sha256()
    files = 0
    directories = 0
    symlinks = 0
    total_bytes = 0
    pending = [root]
    while pending:
        directory = pending.pop()
        for path in sorted(directory.iterdir(), key=lambda item: item.name):
            metadata = path.lstat()
            relative = path.relative_to(root).as_posix()
            executable = bool(stat.S_IMODE(metadata.st_mode) & 0o111)
            if stat.S_ISDIR(metadata.st_mode):
                kind = "directory"
                content_sha256 = ""
                directories += 1
                pending.append(path)
            elif stat.S_ISREG(metadata.st_mode):
                if metadata.st_nlink != 1:
                    raise MeasurementError(
                        f"Lean toolchain contains a hard-linked file: {relative}"
                    )
                kind = "file"
                content_sha256 = sha256_file(path)
                files += 1
                total_bytes += metadata.st_size
            elif stat.S_ISLNK(metadata.st_mode):
                target = os.readlink(path)
                if not target or "\x00" in target or Path(target).is_absolute():
                    raise MeasurementError(
                        f"Lean toolchain contains an unsafe symlink: {relative}"
                    )
                try:
                    resolved = path.resolve(strict=True)
                    resolved.relative_to(root)
                except (OSError, RuntimeError, ValueError) as error:
                    raise MeasurementError(
                        f"Lean toolchain symlink escapes its root: {relative}"
                    ) from error
                kind = "symlink"
                content_sha256 = hashlib.sha256(target.encode("utf-8")).hexdigest()
                symlinks += 1
            else:
                raise MeasurementError(
                    f"Lean toolchain contains a special filesystem entry: {relative}"
                )
            row = {
                "path": relative,
                "kind": kind,
                "executable": executable,
                "size": metadata.st_size if kind == "file" else None,
                "link_count": metadata.st_nlink if kind == "file" else None,
                "content_sha256": content_sha256,
            }
            digest.update(
                (json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n").encode(
                    "utf-8"
                )
            )
    return {
        "algorithm": "sha256-complete-tree-v2-with-link-count",
        "digest": digest.hexdigest(),
        "regular_files": files,
        "directories": directories,
        "symlinks": symlinks,
        "regular_file_bytes": total_bytes,
        "git_administrative_directories_included": True,
    }


def _lock_toolchain(
    toolchain_root: Path, expected_toolchain: str
) -> tuple[dict[str, Any], dict[str, Any]]:
    if toolchain_root.is_symlink():
        raise MeasurementError("Lean toolchain root must not be a symlink")
    root = toolchain_root.resolve(strict=True)
    if not root.is_dir():
        raise MeasurementError("Lean toolchain root must be a non-symlink directory")
    lean = root / "bin" / "lean"
    lake = root / "bin" / "lake"
    library = root / "lib" / "lean"
    if not lean.is_file() or not lake.is_file() or not library.is_dir():
        raise MeasurementError("Lean toolchain root is incomplete")
    integrity = _complete_toolchain_integrity(root)
    if integrity != LEAN_TOOLCHAIN_INTEGRITY:
        raise MeasurementError("supplied Lean toolchain differs from the tracked lock")
    if (
        sha256_file(lean) != LEAN_TOOLCHAIN_LEAN_SHA256
        or sha256_file(lake) != LEAN_TOOLCHAIN_LAKE_SHA256
    ):
        raise MeasurementError("supplied Lean/Lake executable differs from the lock")
    lean_version = command_version(lean, "--version")
    lake_version = command_version(lake, "--version")
    expected_version = expected_toolchain.rsplit(":", 1)[-1].removeprefix("v")
    if expected_version not in str(lean_version.get("version_output")):
        raise MeasurementError(
            "supplied Lean toolchain does not match the runtime snapshot"
        )
    manifest = manifest_for_tree(root, [lean, lake, library])
    return (
        {
            "root": str(root),
            "expected_toolchain": expected_toolchain,
            "lean": lean_version,
            "lake": lake_version,
            "complete_tree_integrity": integrity,
            "manifest_sha256": manifest["manifest_sha256"],
        },
        manifest,
    )


def _runtime_tools_identity() -> dict[str, Any]:
    commands = {
        "python": (Path(sys.executable), ("--version",)),
        "bubblewrap": (Path("/bin/bwrap"), ("--version",)),
        "git": (Path(shutil.which("git") or ""), ("--version",)),
        "systemd_run": (Path(shutil.which("systemd-run") or ""), ("--version",)),
    }
    identities: dict[str, Any] = {}
    for name, (path, arguments) in commands.items():
        if not str(path) or not path.is_file():
            raise MeasurementError(f"required runtime tool is missing: {name}")
        identities[name] = command_version(path, *arguments)
    return identities


def _code_mode_host_identity(codex: Path) -> dict[str, Any]:
    """Authenticate the companion executable used by Codex code-mode tools."""

    codex = codex.resolve(strict=True)
    candidate = codex.parent / "codex-code-mode-host"
    mode = stat.S_IMODE(candidate.stat().st_mode) if candidate.is_file() else 0
    if (
        candidate.is_symlink()
        or not candidate.is_file()
        or mode & 0o7000
        or not os.access(candidate, os.X_OK)
    ):
        raise MeasurementError(
            "Codex code-mode host must be executable by the benchmark user, "
            "have no special mode bits, and be a regular non-symlink sibling of "
            f"the Codex executable: {candidate}"
        )
    return artifact(candidate)


def _verify_code_mode_host_identity(
    codex: Path, identity: Mapping[str, Any]
) -> Path:
    """Recheck the exact companion executable frozen into a campaign lock."""

    current = _code_mode_host_identity(codex)
    if current != identity:
        raise MeasurementError("Codex code-mode host changed after campaign creation")
    return Path(str(current["path"]))


def _stable_hardware_identity(
    host: Mapping[str, Any], slots: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    if not slots:
        raise MeasurementError("campaign requires at least one resource slot")
    first = slots[0]
    if any(
        slot.get("type_key") != first.get("type_key")
        or slot.get("type_signature") != first.get("type_signature")
        or slot.get("physical_core_count") != 4
        or slot.get("memory_max_bytes") != MEMORY_BYTES
        for slot in slots
    ):
        raise MeasurementError("campaign slots do not share one hardware profile")
    hardware = host.get("hardware")
    memory = host.get("memory")
    kernel = host.get("kernel")
    if not all(isinstance(item, Mapping) for item in (hardware, memory, kernel)):
        raise MeasurementError("host inventory is incomplete")
    cpu = hardware.get("cpu")
    if not isinstance(cpu, Mapping):
        raise MeasurementError("host inventory has no CPU record")
    cpuinfo_identity: dict[str, str] = {}
    cpuinfo_raw = cpu.get("proc_cpuinfo_raw")
    if isinstance(cpuinfo_raw, str):
        first_block = cpuinfo_raw.split("\n\n", 1)[0]
        parsed = {}
        for line in first_block.splitlines():
            if ":" in line:
                key, value = line.split(":", 1)
                parsed[key.strip()] = value.strip()
        for key in (
            "vendor_id",
            "cpu family",
            "model",
            "model name",
            "stepping",
            "microcode",
            "flags",
        ):
            if key in parsed:
                cpuinfo_identity[key] = parsed[key]
    global_sysfs = cpu.get("global_sysfs")
    stable_global = (
        {
            key: global_sysfs.get(key)
            for key in (
                "online",
                "offline",
                "smt/active",
                "smt/control",
                "intel_pstate/status",
                "intel_pstate/no_turbo",
                "cpufreq/boost",
            )
        }
        if isinstance(global_sysfs, Mapping)
        else None
    )
    frequency_signatures: list[dict[str, Any]] = []
    runtime_cpu = cpu.get("runtime_per_allowed_cpu")
    selected_logical_cpus = {
        int(logical_cpu)
        for slot in slots
        for logical_cpu in slot.get("logical_cpus", [])
    }
    if isinstance(runtime_cpu, list):
        stable_frequency_keys = (
            "cpu_capacity",
            "cpuinfo_max_freq",
            "cpuinfo_min_freq",
            "energy_performance_available_preferences",
            "energy_performance_preference",
            "scaling_available_governors",
            "scaling_driver",
            "scaling_governor",
            "scaling_max_freq",
            "scaling_min_freq",
        )
        unique: dict[str, dict[str, Any]] = {}
        for raw in runtime_cpu:
            if (
                isinstance(raw, Mapping)
                and raw.get("cpu") in selected_logical_cpus
            ):
                signature = {key: raw.get(key) for key in stable_frequency_keys}
                unique[canonical_digest(signature)] = signature
        frequency_signatures = [unique[key] for key in sorted(unique)]
    numa = hardware.get("numa")
    numa_topology: Any = None
    if isinstance(numa, Mapping) and isinstance(numa.get("nodes"), list):
        numa_topology = {
            "online": numa.get("online"),
            "nodes": [
                {
                    "node": node.get("node"),
                    "cpulist": node.get("cpulist"),
                    "distance": node.get("distance"),
                }
                for node in numa["nodes"]
                if isinstance(node, Mapping)
            ],
        }
    return {
        "kernel_system": kernel.get("system"),
        "kernel_release": kernel.get("release"),
        "kernel_version": kernel.get("version"),
        "kernel_machine": kernel.get("machine"),
        "clocksource_current": kernel.get("clocksource_current"),
        "transparent_hugepage_enabled": kernel.get(
            "transparent_hugepage_enabled"
        ),
        "numa_balancing": kernel.get("numa_balancing"),
        "dmi": hardware.get("dmi"),
        "mem_total_bytes": memory.get("mem_total_bytes"),
        "cpu_identity": cpuinfo_identity,
        "cpu_global_policy": stable_global,
        "frequency_policy_signatures": frequency_signatures,
        "numa_topology": numa_topology,
        "cpu_profile_id": first.get("type_key"),
        "cpu_type_signature": first.get("type_signature"),
        "physical_cores_per_attempt": 4,
        "condition_memory_max_bytes": MEMORY_BYTES,
        "manager_memory_max_bytes": MANAGER_MEMORY_BYTES,
        "coordinator_memory_max": "max",
        "host_memory_admission_bytes_per_attempt": (
            HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
        ),
        "host_memory_admission_is_physical_reservation": False,
        "memory_swap_max_bytes": 0,
    }


def _locked_hardware_snapshot(
    lock: Mapping[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, Any]]:
    """Re-read the locked CPUs and stable host facts without trusting affinity.

    Attempt workers run with an immutable four-core scheduler-affinity mask.
    Supplying the campaign-locked CPU union explicitly lets them re-authenticate
    kernel, microcode, topology, frequency policy, and memory identity for the
    whole campaign allocation.  It also keeps crash recovery reachable while a
    stale CPU partition temporarily removes those CPUs from this coordinator's
    own scheduler-affinity mask.
    """

    raw_slots = lock.get("resource_slots")
    if not isinstance(raw_slots, list) or not raw_slots:
        raise MeasurementError("campaign lock has no resource slots")
    slots: list[Mapping[str, Any]] = []
    logical_cpus: set[int] = set()
    for raw in raw_slots:
        if not isinstance(raw, Mapping) or not isinstance(
            raw.get("logical_cpus"), list
        ):
            raise MeasurementError("campaign lock has an invalid resource slot")
        slots.append(raw)
        logical_cpus.update(int(cpu) for cpu in raw["logical_cpus"])
    host = resources.inventory_host(allowed_cpus=logical_cpus)
    hardware_identity = lock.get("hardware_identity")
    profile = (
        hardware_identity.get("cpu_profile_id")
        if isinstance(hardware_identity, Mapping)
        else None
    )
    if not isinstance(profile, str):
        raise MeasurementError("campaign lock has no CPU profile identity")
    current_slots = resources.allocate_slots(
        host,
        jobs=len(slots),
        profile_id=profile,
        reserve_physical_cores=0,
    )
    if current_slots != raw_slots:
        raise MeasurementError(
            "current exact CPU-slot topology differs from the campaign lock"
        )
    identity = _stable_hardware_identity(host, current_slots)
    if identity != lock.get("hardware_identity"):
        raise MeasurementError("current host hardware differs from the campaign lock")
    return host, current_slots, identity


def _verify_locked_hardware_identity(
    lock: Mapping[str, Any],
) -> dict[str, Any]:
    _host, _slots, identity = _locked_hardware_snapshot(lock)
    return identity


def _script_path(benchmark_root: Path, name: str) -> Path:
    path = benchmark_root / "scripts" / name
    if not path.is_file() or path.is_symlink():
        raise MeasurementError(f"tracked script is missing: {path}")
    return path.resolve()


def create_campaign(args: argparse.Namespace) -> int:
    if not args.acknowledge_environment_lock:
        raise MeasurementError(
            "campaign creation freezes the environment; pass "
            "--acknowledge-environment-lock only when actual benchmarking is ready"
        )
    benchmark_root = args.benchmark_root.resolve()
    protocol = _protocol(benchmark_root)
    if args.jobs != 1:
        raise MeasurementError(
            "measured-v6 requires --jobs 1 so measured attempts sharing one "
            "provider authentication cannot contend or affect each other's cache state"
        )
    task_corpus_lock = _verify_task_corpus_lock(benchmark_root)
    controlled_checkout = _require_controlled_checkout_clean(benchmark_root)
    lexical_results = _lexical_external_path(
        args.results_root, "campaign results root"
    )
    lexical_cache = _lexical_external_path(
        args.runtime_cache_root, "runtime cache base"
    )
    benchmark_repository = Path(str(controlled_checkout["repository"]))
    if any(
        _paths_overlap(candidate, benchmark_repository)
        for candidate in (lexical_results, lexical_cache)
    ):
        raise MeasurementError(
            "campaign results/runtime cache roots must not overlap the benchmark "
            "Git worktree"
        )
    if _paths_overlap(lexical_results, lexical_cache):
        raise MeasurementError(
            "campaign results root and runtime cache base must be disjoint"
        )
    results_root = _external_private_directory(
        args.results_root, "campaign results root", create=True
    )
    if results_root.exists() and any(results_root.iterdir()):
        raise MeasurementError(f"results root is not empty: {results_root}")
    runtime_cache_root = _external_private_directory(
        args.runtime_cache_root, "runtime cache base", create=False
    )
    if _paths_overlap(results_root, runtime_cache_root):
        raise MeasurementError(
            "campaign results root and runtime cache base must be disjoint"
        )
    environment_root = results_root / "environment"
    environment_root.mkdir(mode=0o700)
    commands_log = environment_root / "preparation_commands.jsonl"
    # Reject an impossible CPU/memory request and an incompatible installed
    # guard before downloading or building the frozen runtime environment.
    host = resources.inventory_host()
    slots = resources.allocate_slots(
        host, jobs=args.jobs, profile_id=args.core_profile,
        slot_offset=args.slot_offset,
    )
    memory = host.get("memory")
    available = (
        memory.get("mem_available_bytes")
        if isinstance(memory, Mapping)
        else None
    )
    required_memory = len(slots) * HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
    if not isinstance(available, int) or available < required_memory:
        raise MeasurementError(
            f"host has {available!r} available bytes; the point-in-time "
            f"admission threshold is {required_memory} bytes for concurrent "
            "attempt slots (this check does not reserve physical memory)"
        )
    guard_precreate_root = environment_root / "cpu_guard_precreate"
    guard_precreate_root.mkdir(mode=0o700)
    guard_precreate_control, guard_precreate_status = _run_cpu_guard_status(
        results_root, guard_precreate_root
    )
    if guard_precreate_status.get("phase") != "inactive":
        raise MeasurementError(
            "CPU guard has an active transaction before campaign creation"
        )
    _require_cpu_guard_capacity(guard_precreate_status, slots)
    toolchain_root = args.toolchain_root.resolve()
    dependencies = protocol.get("dependencies")
    expected_toolchain = (
        dependencies.get("lean_toolchain")
        if isinstance(dependencies, Mapping)
        else None
    )
    if not isinstance(expected_toolchain, str):
        raise MeasurementError("measurement protocol has no Lean toolchain identity")
    toolchain_identity, toolchain_manifest = _lock_toolchain(
        toolchain_root, expected_toolchain
    )
    reuse_snapshot_argument = getattr(args, "reuse_runtime_snapshot", None)
    if reuse_snapshot_argument is None:
        runtime_snapshot_source = _prepare_campaign_runtime(
            benchmark_root,
            environment_root,
            runtime_cache_root,
            toolchain_root,
            commands_log,
        )
        runtime_mode = "fresh-build"
    else:
        runtime_snapshot_source = _snapshot_path(
            str(reuse_snapshot_argument),
            "reused runtime snapshot",
            expect_directory=False,
        )
        if (
            _paths_overlap(runtime_snapshot_source, benchmark_repository)
            or _paths_overlap(runtime_snapshot_source, results_root)
        ):
            raise MeasurementError(
                "reused runtime snapshot must be external to the benchmark "
                "checkout and new results root"
            )
        runtime_mode = "authenticated-reuse"
    runtime = _load_runtime_snapshot(runtime_snapshot_source, deep=True)
    source = runtime["source"]
    if runtime_mode == "authenticated-reuse":
        _verify_reused_runtime_location(runtime, runtime_cache_root)
        append_jsonl(
            commands_log,
            {
                "kind": "authenticated-campaign-runtime-reuse",
                "source_snapshot": artifact(runtime_snapshot_source),
                "snapshot_id": runtime.get("snapshot_id"),
                "full_integrity_checked": True,
                "verified_at_utc": utc_now(),
            },
        )
    runtime_origin = {
        "mode": runtime_mode,
        "source_snapshot": artifact(runtime_snapshot_source),
        "snapshot_id": runtime.get("snapshot_id"),
    }
    ref_resolution = {
        "repository": NUMSTABILITY_REPOSITORY,
        "ref": NUMSTABILITY_REF,
        "commit": source["numstability"]["commit"],
        "resolved_at_utc": runtime.get("generated_at", utc_now()),
        "resolved_by": (
            "trusted-runtime-prefetch-before-first-lake"
            if runtime_mode == "fresh-build"
            else "authenticated-pinned-runtime-reuse"
        ),
    }
    condition_l = runtime["condition_l"]
    packages_root = Path(condition_l["derived_packages_root"]).resolve()
    if source["lean"].get("toolchain") != expected_toolchain:
        raise MeasurementError("prepared runtime used a different Lean toolchain")
    prepared_toolchain = runtime["prefetch"].get("lean_toolchain")
    if (
        not isinstance(prepared_toolchain, Mapping)
        or prepared_toolchain.get("integrity")
        != toolchain_identity.get("complete_tree_integrity")
        or prepared_toolchain.get("lake_sha256")
        != toolchain_identity["lake"].get("sha256")
        or prepared_toolchain.get("lean_sha256")
        != toolchain_identity["lean"].get("sha256")
    ):
        raise MeasurementError(
            "prepared runtime used a different authenticated Lean toolchain"
        )
    runtime_tools = _runtime_tools_identity()
    codex = dict(command_version(args.codex.resolve(), "--version"))
    codex["code_mode_host"] = _code_mode_host_identity(args.codex)
    current_host = resources.inventory_host()
    current_slots = resources.allocate_slots(
        current_host, jobs=args.jobs, profile_id=args.core_profile,
        slot_offset=args.slot_offset,
    )
    if current_slots != slots:
        raise MeasurementError(
            "CPU-slot allocation changed during campaign preparation"
        )
    host = current_host
    slots = current_slots
    memory = host.get("memory")
    available = memory.get("mem_available_bytes") if isinstance(memory, Mapping) else None
    required_memory = len(slots) * HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
    if not isinstance(available, int) or available < required_memory:
        raise MeasurementError(
            f"host has {available!r} available bytes; the point-in-time "
            f"admission threshold is {required_memory} bytes for concurrent "
            "attempt slots (this check does not reserve physical memory)"
        )
    hardware_identity = _stable_hardware_identity(host, slots)
    offline_shell = _compile_offline_shell(
        benchmark_root, environment_root, commands_log
    )
    shared_olean, shared_manifest = _compile_shared(
        benchmark_root,
        environment_root,
        toolchain_root,
        packages_root,
        commands_log,
    )
    corpus = _corpus_manifest(benchmark_root)
    execution = _execution_manifest(benchmark_root)
    source_manifest_copy = environment_root / "numstability_source_manifest.json"
    runtime_manifest_copy = environment_root / "runtime_preparation_manifest.json"
    shutil.copyfile(Path(runtime["runtime"]["source_manifest"]), source_manifest_copy)
    shutil.copyfile(Path(runtime["runtime"]["runtime_manifest"]), runtime_manifest_copy)
    source_manifest_copy.chmod(0o444)
    runtime_manifest_copy.chmod(0o444)
    runtime_copy = json.loads(json.dumps(runtime))
    runtime_copy["runtime"]["source_manifest"] = str(source_manifest_copy.resolve())
    runtime_copy["runtime"]["runtime_manifest"] = str(runtime_manifest_copy.resolve())
    snapshot_copy = environment_root / "runtime_snapshot.json"
    atomic_write_json(snapshot_copy, runtime_copy, mode=0o444)
    host_path = environment_root / "host_at_creation.json"
    atomic_write_json(host_path, host, mode=0o444)
    slots_path = environment_root / "resource_slots.json"
    atomic_write_json(slots_path, {"slots": slots}, mode=0o444)
    shared_manifest_path = environment_root / "shared_manifest.json"
    atomic_write_json(shared_manifest_path, shared_manifest, mode=0o444)
    corpus_path = environment_root / "corpus_manifest.json"
    atomic_write_json(corpus_path, corpus, mode=0o444)
    execution_path = environment_root / "execution_manifest.json"
    atomic_write_json(execution_path, execution, mode=0o444)
    toolchain_manifest_path = environment_root / "toolchain_manifest.json"
    atomic_write_json(toolchain_manifest_path, toolchain_manifest, mode=0o444)
    protocol_descriptor = artifact(
        benchmark_root / "metadata" / "measurement_protocol.json",
        relative_to=benchmark_root,
    )
    benchmark_git = git_identity(_repository_root(benchmark_root))
    if not commands_log.exists():
        commands_log.touch(mode=0o600)
    commands_log.chmod(0o444)
    lock_payload: dict[str, Any] = {
        "schema_version": 3,
        "kind": CAMPAIGN_KIND,
        "created_at_utc": utc_now(),
        "campaign_id": None,
        "status": "locked_not_started",
        "results_root": str(results_root),
        "protocol": protocol,
        "protocol_artifact": protocol_descriptor,
        "task_corpus_lock": artifact(
            benchmark_root / TASK_LOCK_RELATIVE, relative_to=benchmark_root
        ),
        "task_corpus_identity": task_corpus_lock,
        "controlled_checkout": controlled_checkout,
        "corpus": artifact(corpus_path, relative_to=results_root),
        "execution": artifact(execution_path, relative_to=results_root),
        "runtime_snapshot": artifact(snapshot_copy, relative_to=results_root),
        "runtime_snapshot_id": runtime.get("snapshot_id"),
        "runtime_origin": runtime_origin,
        "numstability": source.get("numstability"),
        "numstability_ref_resolution_at_campaign_creation": ref_resolution,
        "mathlib": source.get("mathlib"),
        "lean": source.get("lean"),
        "benchmark_git": benchmark_git,
        "agent": {
            **codex,
            "id": "codex",
            "model": "gpt-6-sol",
            "reasoning_effort": "xhigh",
            "subagents_enabled": False,
            "maximum_threads": 1,
        },
        "auth": {
            "path": str(args.auth_file.resolve()),
            "content_recorded": False,
        },
        "offline_shell": artifact(offline_shell, relative_to=results_root),
        "preparation_commands": artifact(commands_log, relative_to=results_root),
        "shared_olean_root": str(shared_olean.resolve()),
        "shared_manifest": artifact(shared_manifest_path, relative_to=results_root),
        "toolchain_root": str(toolchain_root),
        "toolchain": toolchain_identity,
        "toolchain_manifest": artifact(
            toolchain_manifest_path, relative_to=results_root
        ),
        "runtime_tools": runtime_tools,
        "packages_root": str(packages_root),
        "hardware_identity": hardware_identity,
        "host_at_creation": artifact(host_path, relative_to=results_root),
        "resource_slots_artifact": artifact(slots_path, relative_to=results_root),
        "resource_slots": slots,
        "cpu_guard_precreate_status": guard_precreate_control,
        "parallel_attempt_workers": 1,
        "provider_active_attempt_limit_per_authentication": 1,
        "resource_policy": {
            "physical_cores_per_attempt": 4,
            "coordinator_memory_max": "max",
            "coordinator_memory_high": "max",
            "manager_memory_max_bytes": MANAGER_MEMORY_BYTES,
            "host_memory_admission_bytes_per_attempt": (
                HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
            ),
            "host_memory_admission_is_physical_reservation": False,
            "condition_memory_max_bytes": MEMORY_BYTES,
            "condition_memory_swap_max_bytes": 0,
            "condition_memory_cgroup_mode": "fresh-unique-leaf",
            "memory_peak_mode": "read-only-condition-cgroup-lifetime-high-water",
            "cpu_affinity_assignment": (
                "root-cpuset-partition-and-systemd-system-unit-CPUAffinity"
            ),
            "cpu_affinity_immutability": (
                "inherited-seccomp-denial-of-sched_setaffinity"
            ),
            "cpu_syscall_architectures": "native",
            "cpuset_controller_required": True,
            "root_owned_cpu_guard_required": True,
            "cpuset_partition_required": True,
            "cpuset_partition_mode": "root",
            "cpu_partition_scope": (
                "campaign-wide-union-of-disjoint-attempt-slots"
            ),
            "cpu_partition_idle_admission": (
                "sustained-all-slots-or-fail-before-provider-use"
            ),
            "cpu_partition_idle_sample_seconds": (
                CPU_GUARD_IDLE_SAMPLE_SECONDS
            ),
            "cpu_partition_maximum_busy_percent": (
                CPU_GUARD_MAXIMUM_BUSY_PERCENT
            ),
            "cpu_guard_allowed_cpus": guard_precreate_status["allowed_cpus"],
            "cpu_guard_maximum_slots": guard_precreate_status["maximum_slots"],
            "cpu_partition_launch_manager": (
                "system-systemd-as-configured-unprivileged-uid"
            ),
            "cpu_partition_release": "empty-only",
            "cpu_partition_userspace_exclusivity": True,
            "parallel_cpu_slots_disjoint": True,
            "foreign_process_signals_allowed": False,
            "foreign_process_cgroup_migration_allowed": False,
            "dedicated_idle_host_required": False,
            "group_oom_policy": protocol["resources"]["group_oom_policy"],
            "conditions_serial_inside_pair": True,
            "parallelism_unit": "condition_attempt",
            "slurm": False,
        },
    }
    identity_payload = dict(lock_payload)
    identity_payload["campaign_id"] = None
    lock_payload["campaign_id"] = "highambench-" + canonical_digest(identity_payload)[:20]
    lock_payload["record_sha256"] = canonical_digest(lock_payload)
    pairs_root = results_root / "pairs"
    pairs_root.mkdir(mode=0o700)
    _campaign_pairs_root(results_root)
    lock_path = results_root / "campaign_lock.json"
    atomic_write_json(lock_path, lock_payload, mode=0o444)
    print(lock_payload["campaign_id"])
    return 0


def _campaign_pairs_root(results_root: Path) -> Path:
    """Authenticate the fixed campaign pair container before any child access."""

    pairs_root = results_root / "pairs"
    try:
        metadata = pairs_root.lstat()
    except OSError as error:
        raise MeasurementError("campaign pairs directory is missing") from error
    if (
        stat.S_ISLNK(metadata.st_mode)
        or not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != os.getuid()
        or stat.S_IMODE(metadata.st_mode) != 0o700
    ):
        raise MeasurementError(
            "campaign pairs directory must be a real, user-owned directory "
            "with exact mode 0700"
        )
    resolved = pairs_root.resolve(strict=True)
    if resolved != pairs_root:
        raise MeasurementError("campaign pairs directory is not canonical")
    return resolved


def _campaign_pair_root(results_root: Path, pair_id: str) -> Path:
    """Authenticate one already-reserved pair directory."""

    if not pair_id or Path(pair_id).name != pair_id or pair_id in (".", ".."):
        raise MeasurementError("campaign pair id is not a single path component")
    pair_root = _campaign_pairs_root(results_root) / pair_id
    try:
        metadata = pair_root.lstat()
    except OSError as error:
        raise MeasurementError(f"campaign pair directory is missing: {pair_id}") from error
    if (
        stat.S_ISLNK(metadata.st_mode)
        or not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != os.getuid()
        or stat.S_IMODE(metadata.st_mode) != 0o700
    ):
        raise MeasurementError(
            f"campaign pair directory is not private and real: {pair_id}"
        )
    resolved = pair_root.resolve(strict=True)
    if resolved != pair_root:
        raise MeasurementError(f"campaign pair directory is not canonical: {pair_id}")
    return resolved


def _load_campaign(results_root: Path) -> dict[str, Any]:
    authenticated_root = _external_private_directory(
        results_root, "campaign results root", create=False
    )
    _campaign_pairs_root(authenticated_root)
    lock_path = resolved_regular_file(
        authenticated_root / "campaign_lock.json", label="campaign lock"
    )
    lock = read_object(lock_path, kind=CAMPAIGN_KIND)
    if (
        lock.get("schema_version") != 3
        or not isinstance(lock.get("protocol"), Mapping)
        or lock["protocol"].get("protocol_id") != "highambench-measured-v6"
    ):
        raise MeasurementError("campaign lock is not a measured-v6 campaign")
    stored = lock.get("record_sha256")
    payload = dict(lock)
    payload.pop("record_sha256", None)
    if stored != canonical_digest(payload):
        raise MeasurementError("campaign lock self-hash is invalid")
    if lock.get("results_root") != str(authenticated_root):
        raise MeasurementError(
            "campaign lock is bound to a different canonical results root"
        )
    identity_payload = dict(payload)
    identity_payload["campaign_id"] = None
    expected_campaign_id = (
        "highambench-" + canonical_digest(identity_payload)[:20]
    )
    if lock.get("campaign_id") != expected_campaign_id:
        raise MeasurementError("campaign id is inconsistent with its locked inputs")
    return lock


def _artifact_path(results_root: Path, descriptor: Mapping[str, Any]) -> Path:
    relative = descriptor.get("path")
    digest = descriptor.get("sha256")
    expected_bytes = descriptor.get("bytes")
    if (
        not isinstance(relative, str)
        or not isinstance(digest, str)
        or not isinstance(expected_bytes, int)
    ):
        raise MeasurementError("campaign artifact descriptor is invalid")
    unresolved = results_root / relative
    path = resolved_regular_file(unresolved, label="campaign artifact")
    try:
        path.relative_to(results_root.resolve())
    except ValueError as error:
        raise MeasurementError("campaign artifact escapes result root") from error
    if path.stat().st_size != expected_bytes or sha256_file(path) != digest:
        raise MeasurementError(f"campaign artifact is stale: {relative}")
    return path


def _benchmark_artifact_path(
    benchmark_root: Path, descriptor: Mapping[str, Any], label: str
) -> Path:
    relative = descriptor.get("path")
    digest = descriptor.get("sha256")
    expected_bytes = descriptor.get("bytes")
    if (
        not isinstance(relative, str)
        or not isinstance(digest, str)
        or not isinstance(expected_bytes, int)
    ):
        raise MeasurementError(f"{label} descriptor is invalid")
    path = resolved_regular_file(benchmark_root / relative, label=label)
    try:
        path.relative_to(benchmark_root.resolve())
    except ValueError as error:
        raise MeasurementError(f"{label} escapes the benchmark root") from error
    if path.stat().st_size != expected_bytes or sha256_file(path) != digest:
        raise MeasurementError(f"{label} changed")
    return path


def verify_campaign_inputs(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
    *,
    deep_runtime: bool = False,
) -> dict[str, Any]:
    current_protocol = _protocol(benchmark_root)
    resource_policy = lock.get("resource_policy")
    if (
        not isinstance(resource_policy, Mapping)
        or resource_policy.get("cpu_partition_idle_sample_seconds")
        != CPU_GUARD_IDLE_SAMPLE_SECONDS
        or resource_policy.get("cpu_partition_maximum_busy_percent")
        != CPU_GUARD_MAXIMUM_BUSY_PERCENT
    ):
        raise MeasurementError(
            "campaign CPU idle-admission policy differs from measured-v6"
        )
    protocol_path = _benchmark_artifact_path(
        benchmark_root, lock["protocol_artifact"], "measurement protocol"
    )
    if current_protocol != lock.get("protocol"):
        raise MeasurementError("measurement protocol changed after campaign creation")
    task_lock_path = _benchmark_artifact_path(
        benchmark_root, lock["task_corpus_lock"], "task corpus lock"
    )
    task_identity = _verify_task_corpus_lock(benchmark_root)
    if (
        task_identity != lock.get("task_corpus_identity")
        or task_identity.get("lock_sha256") != sha256_file(task_lock_path)
    ):
        raise MeasurementError("task corpus lock identity changed")
    controlled_checkout = _require_controlled_checkout_clean(benchmark_root)
    if controlled_checkout != lock.get("controlled_checkout"):
        raise MeasurementError("controlled Git checkout identity changed")
    corpus_path = _artifact_path(results_root, lock["corpus"])
    execution_path = _artifact_path(results_root, lock["execution"])
    snapshot_path = _artifact_path(results_root, lock["runtime_snapshot"])
    corpus = read_object(corpus_path, kind="highambench-file-manifest")
    execution = read_object(execution_path, kind="highambench-file-manifest")
    corpus_check = verify_manifest(benchmark_root, corpus)
    execution_check = verify_manifest(benchmark_root, execution)
    current_corpus = _corpus_manifest(benchmark_root)
    current_execution = _execution_manifest(benchmark_root)
    corpus_check["exact_scope_match"] = current_corpus == corpus
    execution_check["exact_scope_match"] = current_execution == execution
    if corpus_check.get("ok") is not True:
        raise MeasurementError("task corpus changed after campaign creation")
    if corpus_check["exact_scope_match"] is not True:
        raise MeasurementError("task corpus gained, lost, or changed a controlled file")
    if execution_check.get("ok") is not True:
        raise MeasurementError("measurement scripts changed after campaign creation")
    if execution_check["exact_scope_match"] is not True:
        raise MeasurementError("measurement script scope gained, lost, or changed a file")
    _artifact_path(results_root, lock["offline_shell"])
    _artifact_path(results_root, lock["host_at_creation"])
    _artifact_path(results_root, lock["preparation_commands"])
    slots_path = _artifact_path(results_root, lock["resource_slots_artifact"])
    slots_value = read_object(slots_path)
    if slots_value != {"slots": lock.get("resource_slots")}:
        raise MeasurementError("campaign resource slot artifact changed")
    locked_slots = lock.get("resource_slots")
    guard_status_control = lock.get("cpu_guard_precreate_status")
    if (
        not isinstance(locked_slots, list)
        or not isinstance(guard_status_control, Mapping)
        or set(guard_status_control) != {"command", "evidence", "log"}
        or guard_status_control.get("command") != _cpu_guard_status_command()
        or not isinstance(guard_status_control.get("evidence"), Mapping)
        or not isinstance(guard_status_control.get("log"), Mapping)
    ):
        raise MeasurementError("campaign lacks its CPU-guard pre-create status")
    guard_status_path = _artifact_path(
        results_root, guard_status_control["evidence"]
    )
    guard_log_path = _artifact_path(results_root, guard_status_control["log"])
    expected_guard_root = results_root / "environment" / "cpu_guard_precreate"
    if (
        guard_status_path != expected_guard_root / "status.json"
        or guard_log_path != expected_guard_root / "status.log"
    ):
        raise MeasurementError("campaign CPU-guard pre-create artifacts moved")
    guard_status = read_object(guard_status_path, kind=CPU_GUARD_STATUS_KIND)
    if (
        guard_status.get("schema_version") != 1
        or guard_status.get("verified") is not True
        or guard_status.get("phase") != "inactive"
        or guard_status.get("recovery_required") is not False
        or guard_status.get("active_lease") is not None
        or guard_status.get("applied") is not None
        or guard_status.get("idle_sample_seconds")
        != CPU_GUARD_IDLE_SAMPLE_SECONDS
        or guard_status.get("maximum_busy_percent")
        != CPU_GUARD_MAXIMUM_BUSY_PERCENT
        or guard_status.get("allowed_cpus")
        != resource_policy.get("cpu_guard_allowed_cpus")
        or guard_status.get("maximum_slots")
        != resource_policy.get("cpu_guard_maximum_slots")
    ):
        raise MeasurementError("campaign CPU-guard pre-create status is invalid")
    _require_cpu_guard_capacity(guard_status, locked_slots)
    runtime = _load_runtime_snapshot(snapshot_path, deep=deep_runtime)
    if runtime.get("snapshot_id") != lock.get("runtime_snapshot_id"):
        raise MeasurementError("runtime snapshot identity changed")
    if (
        lock.get("numstability") != runtime["source"].get("numstability")
        or lock.get("mathlib") != runtime["source"].get("mathlib")
        or lock.get("lean") != runtime["source"].get("lean")
        or Path(str(lock.get("packages_root"))).resolve()
        != Path(str(runtime["condition_l"].get("derived_packages_root"))).resolve()
    ):
        raise MeasurementError("campaign dependency identity differs from runtime")
    codex = lock.get("agent")
    if not isinstance(codex, Mapping):
        raise MeasurementError("campaign lock has no agent identity")
    codex_path = Path(str(codex.get("path"))).resolve()
    if not codex_path.is_file() or sha256_file(codex_path) != codex.get("sha256"):
        raise MeasurementError("Codex binary changed after campaign creation")
    code_mode_host = codex.get("code_mode_host")
    if not isinstance(code_mode_host, Mapping):
        raise MeasurementError("campaign lock has no Codex code-mode host identity")
    _verify_code_mode_host_identity(codex_path, code_mode_host)
    toolchain = lock.get("toolchain")
    runtime_tools = lock.get("runtime_tools")
    if not isinstance(toolchain, Mapping) or not isinstance(runtime_tools, Mapping):
        raise MeasurementError("campaign lock lacks toolchain/runtime tool identity")
    toolchain_root = Path(str(lock.get("toolchain_root"))).resolve()
    for key in ("lean", "lake"):
        identity = toolchain.get(key)
        if not isinstance(identity, Mapping):
            raise MeasurementError(f"campaign toolchain lacks {key} identity")
        executable = Path(str(identity.get("path"))).resolve()
        if (
            not executable.is_file()
            or sha256_file(executable) != identity.get("sha256")
        ):
            raise MeasurementError(f"campaign {key} executable changed")
    if _runtime_tools_identity() != runtime_tools:
        raise MeasurementError("campaign runtime tools changed")
    shared_manifest_path = _artifact_path(results_root, lock["shared_manifest"])
    shared_manifest = read_object(
        shared_manifest_path, kind="highambench-file-manifest"
    )
    shared_root = Path(str(lock.get("shared_olean_root")))
    if shared_root.is_symlink():
        raise MeasurementError("campaign shared olean root became a symlink")
    shared_root = shared_root.resolve(strict=True)
    shared_check = verify_manifest(shared_root.parent, shared_manifest)
    current_shared_manifest = manifest_for_tree(shared_root.parent, [shared_root])
    if shared_check.get("ok") is not True or current_shared_manifest != shared_manifest:
        raise MeasurementError("campaign shared olean tree changed")
    for shared_path in [shared_root, *shared_root.rglob("*")]:
        if not shared_path.is_symlink() and shared_path.lstat().st_mode & 0o222:
            raise MeasurementError("campaign shared olean tree became writable")
    if deep_runtime:
        if (
            toolchain.get("complete_tree_integrity") != LEAN_TOOLCHAIN_INTEGRITY
            or _complete_toolchain_integrity(toolchain_root)
            != LEAN_TOOLCHAIN_INTEGRITY
        ):
            raise MeasurementError("campaign Lean toolchain complete tree changed")
        toolchain_manifest_path = _artifact_path(
            results_root, lock["toolchain_manifest"]
        )
        toolchain_manifest = read_object(
            toolchain_manifest_path, kind="highambench-file-manifest"
        )
        toolchain_check = verify_manifest(toolchain_root, toolchain_manifest)
        if toolchain_check.get("ok") is not True:
            raise MeasurementError("campaign Lean toolchain libraries changed")
        current_toolchain_manifest = manifest_for_tree(
            toolchain_root,
            [
                toolchain_root / "bin" / "lean",
                toolchain_root / "bin" / "lake",
                toolchain_root / "lib" / "lean",
            ],
        )
        if current_toolchain_manifest != toolchain_manifest:
            raise MeasurementError("campaign Lean toolchain file scope changed")
    return {
        "verified_at_utc": utc_now(),
        "protocol_sha256": sha256_file(protocol_path),
        "task_corpus": task_identity,
        "controlled_checkout": controlled_checkout,
        "corpus": corpus_check,
        "execution": execution_check,
        "runtime_snapshot_id": runtime.get("snapshot_id"),
        "deep_runtime_integrity_checked": deep_runtime,
        "codex_sha256": codex.get("sha256"),
        "toolchain_manifest_sha256": toolchain.get("manifest_sha256"),
        "runtime_tools": runtime_tools,
        "shared_manifest_sha256": shared_manifest.get("manifest_sha256"),
    }


def _order_pairs(benchmark_root: Path) -> list[dict[str, Any]]:
    order = read_object(benchmark_root / "metadata" / "run_order.json")
    raw_pairs = order.get("pairs")
    manifest = read_object(benchmark_root / "metadata" / "manifest.json")
    config = read_object(benchmark_root / "metadata" / "config.json")
    task_ids = [
        str(target["task_id"])
        for paper in manifest.get("papers", [])
        if isinstance(paper, Mapping)
        for target in paper.get("targets", [])
        if isinstance(target, Mapping) and target.get("availability") == "available"
    ]
    repetition_ids = [
        str(repetition["id"])
        for repetition in config.get("repetitions", [])
        if isinstance(repetition, Mapping) and isinstance(repetition.get("id"), str)
    ]
    canonical_keys = [
        (task_id, repetition_id)
        for task_id in task_ids
        for repetition_id in repetition_ids
    ]
    if (
        not task_ids
        or not repetition_ids
        or not isinstance(raw_pairs, list)
        or len(raw_pairs) != len(canonical_keys)
    ):
        raise MeasurementError(
            "run order must contain one pair for every manifest task and repetition"
        )
    pairs: list[dict[str, Any]] = []
    seen: set[str] = set()
    if order.get("method", {}).get("name") != "frozen_sha256_first_byte_parity":
        raise MeasurementError("run order must use the locked counterbalancing digests")
    expected_pairs = {f"{task}-{repetition}": (task, repetition)
                      for task, repetition in canonical_keys}
    for raw in raw_pairs:
        if not isinstance(raw, Mapping):
            raise MeasurementError("run order contains a non-object pair")
        pair = dict(raw)
        pair_id = pair.get("pair_id")
        if not isinstance(pair_id, str) or pair_id not in expected_pairs:
            raise MeasurementError("run order contains an unknown task/repetition pair")
        expected_task, expected_repetition = expected_pairs[pair_id]
        task_id = pair.get("task_id")
        condition_order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if (
            not isinstance(pair_id, str)
            or pair_id in seen
            or not isinstance(task_id, str)
            or condition_order not in (["N", "L"], ["L", "N"])
            or not isinstance(run_ids, list)
            or len(run_ids) != 2
        ):
            raise MeasurementError(f"invalid run-order pair: {pair!r}")
        seen.add(pair_id)
        digest = pair.get("sha256")
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise MeasurementError("run-order pair lacks its frozen counterbalancing digest")
        expected_order = (
            ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
        )
        expected_pair_id = f"{expected_task}-{expected_repetition}"
        expected_run_ids = [
            f"{expected_pair_id}-{condition}" for condition in expected_order
        ]
        if (
            task_id != expected_task
            or pair.get("repetition_id") != expected_repetition
            or pair_id != expected_pair_id
            or pair.get("sha256") != digest
            or condition_order != expected_order
            or run_ids != expected_run_ids
        ):
            raise MeasurementError(
                f"run-order pair is not canonical: {pair!r}"
            )
        pairs.append(pair)
    return pairs


def _attempt_terminal_valid(
    attempt_path: Path,
    pair_root: Path,
    expected: Mapping[str, Any],
    condition: str,
    lock: Mapping[str, Any],
    returncode: int,
    *,
    resource_record_path: Path | None = None,
) -> bool:
    """Authenticate the terminal attempt before a pair can be committed."""

    try:
        expected_path = pair_root / f"condition-{condition}" / "attempt.json"
        path = resolved_regular_file(attempt_path, label="attempt terminal")
        if path != expected_path:
            return False
        record = read_object(path, kind="highambench-measured-attempt")
        payload = dict(record)
        stored = payload.pop("record_sha256", None)
        order = expected.get("condition_order")
        run_ids = expected.get("run_ids")
        if (
            stored != canonical_digest(payload)
            or record.get("schema_version") != 3
            or condition not in ("N", "L")
            or not isinstance(order, list)
            or not isinstance(run_ids, list)
            or condition not in order
            or record.get("pair_id") != expected.get("pair_id")
            or record.get("task_id") != expected.get("task_id")
            or record.get("condition") != condition
            or record.get("run_id") != run_ids[order.index(condition)]
            or record.get("campaign_id") != lock.get("campaign_id")
            or record.get("campaign_lock_sha256") != lock.get("record_sha256")
            or record.get("infrastructure_failure") is not False
            or returncode not in (0, 1)
            or (
                record.get("pass") is not True
                and record.get("pass") is not False
            )
            or returncode != (0 if record.get("pass") is True else 1)
        ):
            return False
        expected_bindings = {
            "resource_record": resource_record_path or pair_root / "resource_record.json",
            "condition_resource_record": (
                pair_root / f"condition_cgroup_begin_{condition}.json"
            ),
            "condition_cgroup_entry_proof": (
                pair_root / f"condition_cgroup_entry_{condition}.json"
            ),
        }
        for field, expected_artifact in expected_bindings.items():
            descriptor = record.get(field)
            if (
                not isinstance(descriptor, Mapping)
                or _artifact_path(pair_root, descriptor) != expected_artifact
            ):
                return False
        live_proof = record.get("resource_kernel_proof_at_attempt_start")
        entry_proof = read_object(
            expected_bindings["condition_cgroup_entry_proof"],
            kind="highambench-resource-proof",
        )
        if (
            not isinstance(live_proof, Mapping)
            or live_proof.get("schema_version") != resources.SCHEMA_VERSION
            or live_proof.get("kind") != "highambench-resource-proof"
            or live_proof.get("verified") is not True
            or entry_proof.get("schema_version") != resources.SCHEMA_VERSION
            or entry_proof.get("verified") is not True
            or _resource_contract_identity(live_proof)
            != _resource_contract_identity(entry_proof)
        ):
            return False
        return True
    except (KeyError, MeasurementError, OSError, TypeError, ValueError):
        return False


def _pair_payload_valid_v3(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
) -> bool:
    path = pair_root / "pair.json"
    if not path.is_file() or path.is_symlink():
        return False
    try:
        value = read_object(path, kind=PAIR_KIND)
    except MeasurementError:
        return False
    stored = value.get("record_sha256")
    payload = dict(value)
    payload.pop("record_sha256", None)
    if not (
        stored == canonical_digest(payload)
        and value.get("schema_version") == 3
        and value.get("complete") is True
        and value.get("infrastructure_failure") is False
        and value.get("pair_id") == expected.get("pair_id")
        and value.get("task_id") == expected.get("task_id")
        and value.get("repetition_id") == expected.get("repetition_id")
        and value.get("condition_order") == expected.get("condition_order")
        and value.get("run_ids") == expected.get("run_ids")
        and value.get("campaign_id") == lock.get("campaign_id")
        and value.get("campaign_lock_sha256") == lock.get("record_sha256")
        and value.get("hardware_verification_before")
        == lock.get("hardware_identity")
        and value.get("hardware_verification_after")
        == lock.get("hardware_identity")
        and isinstance(value.get("corpus_verification_before"), Mapping)
        and isinstance(value.get("corpus_verification_after"), Mapping)
    ):
        return False
    attempts = value.get("attempts")
    order = expected.get("condition_order")
    samples = value.get("resource_samples")
    if (
        not isinstance(attempts, list)
        or len(attempts) != 2
        or not isinstance(order, list)
        or [item.get("condition") for item in attempts if isinstance(item, Mapping)]
        != order
        or not isinstance(samples, list)
        or len(samples) != 2
        or [item.get("after_condition") for item in samples if isinstance(item, Mapping)]
        != order
    ):
        return False
    try:
        pair_resource_bindings = {
            "resource": pair_root / "resource_record.json",
            "resource_proof": pair_root / "resource_kernel_proof.json",
            "resource_worker_proof": pair_root / "resource_worker_proof.json",
        }
        for field, expected_artifact in pair_resource_bindings.items():
            descriptor = value.get(field)
            if (
                not isinstance(descriptor, Mapping)
                or _artifact_path(pair_root, descriptor) != expected_artifact
            ):
                return False
        resource_record = read_object(
            pair_resource_bindings["resource"], kind="highambench-pair-resource"
        )
        resource_payload = dict(resource_record)
        resource_digest = resource_payload.pop("record_sha256", None)
        if (
            resource_digest != canonical_digest(resource_payload)
            or resource_record.get("schema_version") != 2
            or resource_record.get("pair_id") != expected.get("pair_id")
        ):
            return False
        for condition, attempt, sample in zip(order, attempts, samples, strict=True):
            if not isinstance(attempt, Mapping) or not isinstance(sample, Mapping):
                return False
            required_attempt_fields = {
                "condition",
                "returncode",
                "record",
                "process_log",
                "command",
                "condition_resource",
                "condition_entry_proof",
            }
            if not required_attempt_fields <= set(attempt):
                return False
            for field in (
                "record",
                "process_log",
                "command",
                "condition_resource",
                "condition_entry_proof",
            ):
                if not isinstance(attempt.get(field), Mapping):
                    return False
                _artifact_path(pair_root, attempt[field])
            returncode = attempt.get("returncode")
            attempt_path = _artifact_path(pair_root, attempt["record"])
            if (
                not isinstance(returncode, int)
                or isinstance(returncode, bool)
                or not _attempt_terminal_valid(
                    attempt_path,
                    pair_root,
                    expected,
                    str(condition),
                    lock,
                    returncode,
                )
            ):
                return False
            required_sample_fields = {
                "after_condition",
                "condition_cgroup_begin",
                "condition_cgroup_entry_proof",
                "condition_cgroup_finish",
                "manager_after_condition",
            }
            if set(sample) != required_sample_fields:
                return False
            expected_sample_paths = {
                "condition_cgroup_begin": (
                    pair_root / f"condition_cgroup_begin_{condition}.json"
                ),
                "condition_cgroup_entry_proof": (
                    pair_root / f"condition_cgroup_entry_{condition}.json"
                ),
                "condition_cgroup_finish": (
                    pair_root / f"condition_cgroup_finish_{condition}.json"
                ),
                "manager_after_condition": (
                    pair_root / f"resource_after_{condition}.json"
                ),
            }
            for field, expected_artifact in expected_sample_paths.items():
                descriptor = sample.get(field)
                if (
                    not isinstance(descriptor, Mapping)
                    or _artifact_path(pair_root, descriptor) != expected_artifact
                ):
                    return False
            if (
                _artifact_path(pair_root, attempt["condition_resource"])
                != expected_sample_paths["condition_cgroup_begin"]
                or _artifact_path(pair_root, attempt["condition_entry_proof"])
                != expected_sample_paths["condition_cgroup_entry_proof"]
            ):
                return False
        return True
    except (KeyError, MeasurementError, OSError, TypeError, ValueError):
        return False


def _pair_payload_valid(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
) -> bool:
    path = pair_root / "pair.json"
    try:
        value = read_object(path, kind=PAIR_KIND)
        if value.get("schema_version") == 3:
            return _pair_payload_valid_v3(pair_root, expected, lock)
        payload = dict(value)
        stored = payload.pop("record_sha256", None)
        if not (
            stored == canonical_digest(payload)
            and value.get("schema_version") == 4
            and value.get("complete") is True
            and value.get("infrastructure_failure") is False
            and value.get("pair_id") == expected.get("pair_id")
            and value.get("task_id") == expected.get("task_id")
            and value.get("repetition_id") == expected.get("repetition_id")
            and value.get("condition_order") == expected.get("condition_order")
            and value.get("condition_order_is_execution_constraint") is True
            and value.get("run_ids") == expected.get("run_ids")
            and value.get("campaign_id") == lock.get("campaign_id")
            and value.get("campaign_lock_sha256") == lock.get("record_sha256")
            and value.get("hardware_verification_before")
            == lock.get("hardware_identity")
            and value.get("hardware_verification_after")
            == lock.get("hardware_identity")
            and isinstance(value.get("corpus_verification_before"), Mapping)
            and isinstance(value.get("corpus_verification_after"), Mapping)
        ):
            return False
        attempts = value.get("attempts")
        resource_entries = value.get("condition_resources")
        if (
            not isinstance(attempts, list)
            or not isinstance(resource_entries, list)
            or len(attempts) != 2
            or len(resource_entries) != 2
            or [item.get("condition") for item in attempts] != ["N", "L"]
            or [item.get("condition") for item in resource_entries]
            != ["N", "L"]
        ):
            return False
        for condition, attempt, resource_entry in zip(
            ("N", "L"), attempts, resource_entries, strict=True
        ):
            if not isinstance(attempt, Mapping) or not isinstance(
                resource_entry, Mapping
            ):
                return False
            resource_path = pair_root / f"resource_record_{condition}.json"
            bindings = {
                "resource": resource_path,
                "resource_proof": (
                    pair_root / f"resource_kernel_proof_{condition}.json"
                ),
                "resource_worker_proof": (
                    pair_root / f"resource_worker_proof_{condition}.json"
                ),
                "worker": pair_root / f"condition-{condition}.worker.json",
            }
            for field, expected_path in bindings.items():
                descriptor = resource_entry.get(field)
                if (
                    not isinstance(descriptor, Mapping)
                    or _artifact_path(pair_root, descriptor) != expected_path
                ):
                    return False
            resource_record = read_object(
                resource_path, kind="highambench-attempt-resource"
            )
            resource_payload = dict(resource_record)
            resource_digest = resource_payload.pop("record_sha256", None)
            if (
                resource_digest != canonical_digest(resource_payload)
                or resource_record.get("schema_version") != 2
                or resource_record.get("pair_id") != expected.get("pair_id")
                or resource_record.get("condition") != condition
            ):
                return False
            returncode = attempt.get("returncode")
            descriptor = attempt.get("record")
            if (
                not isinstance(returncode, int)
                or isinstance(returncode, bool)
                or not isinstance(descriptor, Mapping)
                or not _attempt_terminal_valid(
                    _artifact_path(pair_root, descriptor),
                    pair_root,
                    expected,
                    condition,
                    lock,
                    returncode,
                    resource_record_path=resource_path,
                )
                or not _condition_worker_payload_valid(
                    pair_root, expected, condition, lock
                )
            ):
                return False
        return True
    except (KeyError, MeasurementError, OSError, TypeError, ValueError):
        return False


def _strict_pair_resource_evidence_valid(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
) -> bool:
    """Apply the final verifier's resource checks before durable completion.

    The import is intentionally lazy: ``verify_results`` imports coordinator
    helpers, while this path is reached only after both condition workers have
    exited.
    Keeping one strict implementation prevents the completion gate and the
    offline verifier from drifting apart.
    """

    try:
        if __package__:
            from .verify_results import _verify_resource
        else:  # pragma: no cover - direct execution
            from verify_results import _verify_resource  # type: ignore

        pair = read_object(pair_root / "pair.json", kind=PAIR_KIND)
        _verify_resource(pair_root, pair, expected, lock)
        return True
    except Exception:
        # Completion is a fail-closed decision.  The normal verifier provides
        # the detailed diagnostic when an operator inspects the failed pair.
        return False


def _pair_record_valid_v3(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
    *,
    resource_evidence_prevalidated: bool = False,
) -> bool:
    """Accept completion only after the coordinator's outer terminal is sealed."""

    if not _pair_payload_valid(pair_root, expected, lock):
        return False
    if (
        not resource_evidence_prevalidated
        and not _strict_pair_resource_evidence_valid(pair_root, expected, lock)
    ):
        return False
    try:
        pair_path = resolved_regular_file(
            pair_root / "pair.json", label="pair result"
        )
        terminal_path = resolved_regular_file(
            pair_root / "outer_terminal.json", label="pair outer terminal"
        )
        terminal = read_object(
            terminal_path, kind="highambench-pair-outer-terminal"
        )
        terminal_payload = dict(terminal)
        terminal_digest = terminal_payload.pop("record_sha256", None)
        if (
            terminal_digest != canonical_digest(terminal_payload)
            or terminal.get("pair_id") != expected.get("pair_id")
            or terminal.get("campaign_id") != lock.get("campaign_id")
            or terminal.get("campaign_lock_sha256")
            != lock.get("record_sha256")
            or terminal.get("returncode") != 0
            or terminal.get("complete") is not True
        ):
            return False
        pair_descriptor = terminal.get("pair")
        launch_descriptor = terminal.get("launch")
        if not isinstance(pair_descriptor, Mapping) or not isinstance(
            launch_descriptor, Mapping
        ):
            return False
        if _artifact_path(pair_root, pair_descriptor) != pair_path:
            return False
        launch_path = _artifact_path(pair_root, launch_descriptor)
        if launch_path != pair_root / "launch.json":
            return False
        launch = read_object(launch_path, kind="highambench-pair-launch")
        launch_payload = dict(launch)
        launch_digest = launch_payload.pop("record_sha256", None)
        if (
            launch_digest != canonical_digest(launch_payload)
            or launch.get("pair_id") != expected.get("pair_id")
            or launch.get("campaign_id") != lock.get("campaign_id")
            or launch.get("campaign_lock_sha256") != lock.get("record_sha256")
            or launch.get("returncode") != 0
            or launch.get("slot") not in lock.get("resource_slots", [])
            or launch.get("launcher") != "privileged-cpu-guard"
            or not isinstance(launch.get("cpu_guard_lease_id"), str)
            or _CPU_GUARD_LEASE_RE.fullmatch(
                str(launch.get("cpu_guard_lease_id"))
            )
            is None
        ):
            return False
        log_descriptor = launch.get("log")
        return isinstance(log_descriptor, Mapping) and bool(
            _artifact_path(pair_root, log_descriptor)
        )
    except (MeasurementError, OSError, TypeError, ValueError):
        return False


def _pair_record_valid(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
    *,
    resource_evidence_prevalidated: bool = False,
) -> bool:
    pair_value: Mapping[str, Any] | None = None
    try:
        pair_value = read_object(pair_root / "pair.json", kind=PAIR_KIND)
        if pair_value.get("schema_version") == 3:
            return _pair_record_valid_v3(
                pair_root,
                expected,
                lock,
                resource_evidence_prevalidated=resource_evidence_prevalidated,
            )
    except (MeasurementError, OSError):
        pass
    if not _pair_payload_valid(pair_root, expected, lock):
        return False
    if (
        not resource_evidence_prevalidated
        and not _strict_pair_resource_evidence_valid(pair_root, expected, lock)
    ):
        return False
    try:
        pair_path = resolved_regular_file(pair_root / "pair.json", label="pair result")
        terminal_path = resolved_regular_file(
            pair_root / "outer_terminal.json", label="pair outer terminal"
        )
        terminal = read_object(
            terminal_path, kind="highambench-pair-outer-terminal"
        )
        terminal_payload = dict(terminal)
        terminal_digest = terminal_payload.pop("record_sha256", None)
        pair_descriptor = terminal.get("pair")
        condition_terminals = terminal.get("condition_terminals")
        if (
            terminal_digest != canonical_digest(terminal_payload)
            or terminal.get("schema_version") != 2
            or terminal.get("pair_id") != expected.get("pair_id")
            or terminal.get("campaign_id") != lock.get("campaign_id")
            or terminal.get("campaign_lock_sha256") != lock.get("record_sha256")
            or terminal.get("returncode") != 0
            or terminal.get("complete") is not True
            or not isinstance(pair_descriptor, Mapping)
            or _artifact_path(pair_root, pair_descriptor) != pair_path
            or not isinstance(condition_terminals, list)
            or len(condition_terminals) != 2
        ):
            return False
        seen: set[str] = set()
        for descriptor in condition_terminals:
            if not isinstance(descriptor, Mapping):
                return False
            condition_path = _artifact_path(pair_root, descriptor)
            condition_terminal = read_object(
                condition_path, kind="highambench-condition-outer-terminal"
            )
            condition_payload = dict(condition_terminal)
            condition_digest = condition_payload.pop("record_sha256", None)
            condition = condition_terminal.get("condition")
            if (
                condition not in ("N", "L")
                or condition in seen
                or condition_path
                != pair_root / f"condition-{condition}.outer_terminal.json"
                or condition_digest != canonical_digest(condition_payload)
                or condition_terminal.get("pair_id") != expected.get("pair_id")
                or condition_terminal.get("campaign_id") != lock.get("campaign_id")
                or condition_terminal.get("campaign_lock_sha256")
                != lock.get("record_sha256")
                or condition_terminal.get("returncode") != 0
                or condition_terminal.get("complete") is not True
            ):
                return False
            seen.add(str(condition))
            launch_descriptor = condition_terminal.get("launch")
            worker_descriptor = condition_terminal.get("worker")
            if not isinstance(launch_descriptor, Mapping) or not isinstance(
                worker_descriptor, Mapping
            ):
                return False
            launch_path = _artifact_path(pair_root, launch_descriptor)
            worker_path = _artifact_path(pair_root, worker_descriptor)
            if (
                launch_path != pair_root / f"launch_{condition}.json"
                or worker_path != pair_root / f"condition-{condition}.worker.json"
            ):
                return False
            launch = read_object(launch_path, kind="highambench-condition-launch")
            launch_payload = dict(launch)
            launch_digest = launch_payload.pop("record_sha256", None)
            slot = launch.get("slot")
            if (
                launch_digest != canonical_digest(launch_payload)
                or launch.get("pair_id") != expected.get("pair_id")
                or launch.get("condition") != condition
                or launch.get("campaign_id") != lock.get("campaign_id")
                or launch.get("campaign_lock_sha256") != lock.get("record_sha256")
                or launch.get("returncode") != 0
                or launch.get("launcher") != "privileged-cpu-guard"
                or slot not in lock.get("resource_slots", [])
            ):
                return False
        return seen == {"N", "L"}
    except (KeyError, MeasurementError, OSError, TypeError, ValueError):
        return False


def _failed_pair_terminal_result(
    pair_root: Path,
    expected: Mapping[str, Any],
    lock: Mapping[str, Any],
    *,
    relative_to: Path,
) -> dict[str, Any]:
    """Authenticate a durable, ordinary failed outer pair terminal."""

    terminal_path = resolved_regular_file(
        pair_root / "outer_terminal.json", label="failed pair outer terminal"
    )
    terminal = read_object(
        terminal_path, kind="highambench-pair-outer-terminal"
    )
    terminal_payload = dict(terminal)
    terminal_digest = terminal_payload.pop("record_sha256", None)
    returncode = terminal.get("returncode")
    if terminal.get("schema_version") == 2:
        pair_descriptor = terminal.get("pair")
        condition_terminals = terminal.get("condition_terminals")
        if (
            terminal_digest != canonical_digest(terminal_payload)
            or terminal.get("pair_id") != expected.get("pair_id")
            or terminal.get("campaign_id") != lock.get("campaign_id")
            or terminal.get("campaign_lock_sha256") != lock.get("record_sha256")
            or returncode != 2
            or terminal.get("complete") is not False
            or not isinstance(pair_descriptor, Mapping)
            or _artifact_path(pair_root, pair_descriptor)
            != pair_root / "pair.json"
            or not isinstance(condition_terminals, list)
        ):
            raise MeasurementError("failed pair outer terminal is invalid")
        lease_ids: set[str] = set()
        for condition in ("N", "L"):
            launch_path = pair_root / f"launch_{condition}.json"
            if not launch_path.is_file() or launch_path.is_symlink():
                continue
            launch = read_object(
                launch_path, kind="highambench-condition-launch"
            )
            launch_payload = dict(launch)
            launch_digest = launch_payload.pop("record_sha256", None)
            lease_id = launch.get("cpu_guard_lease_id")
            if (
                launch_digest != canonical_digest(launch_payload)
                or launch.get("pair_id") != expected.get("pair_id")
                or launch.get("condition") != condition
                or launch.get("campaign_id") != lock.get("campaign_id")
                or launch.get("campaign_lock_sha256") != lock.get("record_sha256")
                or not isinstance(lease_id, str)
                or _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None
            ):
                raise MeasurementError("failed condition launch evidence is invalid")
            lease_ids.add(lease_id)
        return {
            "pair_id": str(expected["pair_id"]),
            "returncode": returncode,
            "complete": False,
            "cpu_guard_lease_id": (
                next(iter(lease_ids)) if len(lease_ids) == 1 else None
            ),
            "terminal": artifact(terminal_path, relative_to=relative_to),
        }
    if (
        terminal_digest != canonical_digest(terminal_payload)
        or terminal.get("schema_version") != 1
        or terminal.get("pair_id") != expected.get("pair_id")
        or terminal.get("campaign_id") != lock.get("campaign_id")
        or terminal.get("campaign_lock_sha256") != lock.get("record_sha256")
        or isinstance(returncode, bool)
        or not isinstance(returncode, int)
        or terminal.get("complete") is not False
        or not isinstance(terminal.get("recorded_at_utc"), str)
    ):
        raise MeasurementError("failed pair outer terminal is invalid")
    launch_descriptor = terminal.get("launch")
    if not isinstance(launch_descriptor, Mapping):
        raise MeasurementError("failed pair outer terminal lacks launch evidence")
    launch_path = _artifact_path(pair_root, launch_descriptor)
    if launch_path != pair_root / "launch.json":
        raise MeasurementError("failed pair outer terminal uses another launch")
    launch = read_object(launch_path, kind="highambench-pair-launch")
    launch_payload = dict(launch)
    launch_digest = launch_payload.pop("record_sha256", None)
    lease_id = launch.get("cpu_guard_lease_id")
    slots = lock.get("resource_slots")
    if (
        launch_digest != canonical_digest(launch_payload)
        or launch.get("schema_version") != 1
        or launch.get("pair_id") != expected.get("pair_id")
        or launch.get("campaign_id") != lock.get("campaign_id")
        or launch.get("campaign_lock_sha256") != lock.get("record_sha256")
        or launch.get("returncode") != returncode
        or launch.get("launcher") != "privileged-cpu-guard"
        or not isinstance(slots, list)
        or launch.get("slot") not in slots
        or not isinstance(lease_id, str)
        or _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None
        or not isinstance(launch.get("finished_at_utc"), str)
        or not isinstance(launch.get("started_at_utc"), str)
    ):
        raise MeasurementError("failed pair launch evidence is invalid")
    log_descriptor = launch.get("log")
    if (
        not isinstance(log_descriptor, Mapping)
        or _artifact_path(pair_root, log_descriptor)
        != pair_root / "cpu-guard-launch.log"
    ):
        raise MeasurementError("failed pair launch log binding is invalid")
    pair_descriptor = terminal.get("pair")
    pair_path = pair_root / "pair.json"
    if pair_descriptor is None:
        if pair_path.exists() or pair_path.is_symlink():
            raise MeasurementError("failed pair terminal omitted an existing pair record")
    elif (
        not isinstance(pair_descriptor, Mapping)
        or _artifact_path(pair_root, pair_descriptor) != pair_path
    ):
        raise MeasurementError("failed pair terminal pair binding is invalid")
    return {
        "pair_id": str(expected["pair_id"]),
        "returncode": returncode,
        "complete": False,
        "cpu_guard_lease_id": lease_id,
        "terminal": artifact(terminal_path, relative_to=relative_to),
    }


def _select_pairs(
    benchmark_root: Path,
    results_root: Path,
    requested: Sequence[str],
    *,
    lock: Mapping[str, Any],
) -> list[dict[str, Any]]:
    pairs_root = _campaign_pairs_root(results_root)
    pairs = _order_pairs(benchmark_root)
    by_id = {pair["pair_id"]: pair for pair in pairs}
    if requested:
        if len(requested) != len(set(requested)):
            raise MeasurementError("duplicate --pair-id values are forbidden")
        missing = sorted(set(requested) - set(by_id))
        if missing:
            raise MeasurementError(f"unknown pair ids: {', '.join(missing)}")
        pairs = [by_id[pair_id] for pair_id in requested]
    selected: list[dict[str, Any]] = []
    for pair in pairs:
        root = pairs_root / pair["pair_id"]
        if _pair_record_valid(root, pair, lock):
            continue
        if root.exists():
            raise MeasurementError(
                f"incomplete or reserved pair root is never overwritten: {root}"
            )
        selected.append(pair)
    return selected


def _incident_records_for_pair(
    results_root: Path, pair_id: str
) -> list[Path]:
    parent = results_root / "infrastructure_incidents" / pair_id
    if parent.is_symlink():
        raise MeasurementError(f"infrastructure incident directory is invalid: {parent}")
    if not parent.exists():
        return []
    if not parent.is_dir():
        raise MeasurementError(f"infrastructure incident directory is invalid: {parent}")
    records = sorted(parent.glob("attempt-*.json"))
    archives = sorted(parent.glob("attempt-*[0-9]"))
    if len(records) != len(archives):
        raise MeasurementError(f"infrastructure incident archive is incomplete: {parent}")
    for record, archive in zip(records, archives, strict=True):
        if record.stem != archive.name:
            raise MeasurementError(f"infrastructure incident binding is invalid: {record}")
    return records


def _write_infrastructure_incident_record(
    results_root: Path,
    lock: Mapping[str, Any],
    pair_id: str,
    archive: Path,
    *,
    reason: str,
) -> Path:
    record_path = archive.with_suffix(".json")
    if record_path.exists() or record_path.is_symlink():
        raise MeasurementError(f"infrastructure incident record exists: {record_path}")
    manifest = manifest_for_tree(results_root, [archive])
    record: dict[str, Any] = {
        "schema_version": 1,
        "kind": "highambench-infrastructure-incident",
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "pair_id": pair_id,
        "reason": reason,
        "archive": archive.relative_to(results_root).as_posix(),
        "archive_manifest": manifest,
        "recorded_at_utc": utc_now(),
    }
    record["record_sha256"] = canonical_digest(record)
    atomic_write_json(record_path, record, mode=0o444)
    return record_path


def _seal_interrupted_incident_archives(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
) -> None:
    """Finish an archive record if a coordinator died after atomic rename."""

    for pair in _order_pairs(benchmark_root):
        pair_id = str(pair["pair_id"])
        parent = results_root / "infrastructure_incidents" / pair_id
        if not parent.exists():
            continue
        if parent.is_symlink() or not parent.is_dir():
            raise MeasurementError(f"infrastructure incident directory is invalid: {parent}")
        for archive in sorted(parent.glob("attempt-*[0-9]")):
            if re.fullmatch(r"attempt-[0-9]{3}", archive.name) is None:
                raise MeasurementError(f"infrastructure incident name is invalid: {archive}")
            if archive.is_symlink() or not archive.is_dir():
                raise MeasurementError(f"infrastructure incident archive is invalid: {archive}")
            if not archive.with_suffix(".json").exists():
                _write_infrastructure_incident_record(
                    results_root,
                    lock,
                    pair_id,
                    archive,
                    reason="coordinator-interrupted-after-archive-rename",
                )
        _incident_records_for_pair(results_root, pair_id)


def _archive_infrastructure_pair(
    results_root: Path,
    lock: Mapping[str, Any],
    pair: Mapping[str, Any],
    *,
    reason: str,
) -> Path:
    """Preserve an unscored failed pair before a fresh same-campaign retry."""

    pair_id = str(pair["pair_id"])
    pair_root = _campaign_pairs_root(results_root) / pair_id
    if pair_root.is_symlink() or not pair_root.is_dir():
        raise MeasurementError(f"cannot archive missing or linked pair root: {pair_root}")
    if _pair_record_valid(pair_root, pair, lock):
        raise MeasurementError(f"cannot archive a complete measured pair: {pair_id}")
    parent = results_root / "infrastructure_incidents" / pair_id
    parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    if parent.is_symlink() or stat.S_IMODE(parent.stat().st_mode) != 0o700:
        raise MeasurementError(f"infrastructure incident directory is not private: {parent}")
    number = len(_incident_records_for_pair(results_root, pair_id)) + 1
    archive = parent / f"attempt-{number:03d}"
    if archive.exists() or archive.with_suffix(".json").exists():
        raise MeasurementError(f"infrastructure incident destination exists: {archive}")
    pair_root.rename(archive)
    return _write_infrastructure_incident_record(
        results_root, lock, pair_id, archive, reason=reason
    )


def _condition_worker_command(
    benchmark_root: Path,
    results_root: Path,
    pair: Mapping[str, Any],
    condition: str,
    slot_file: Path,
) -> list[str]:
    return [
        sys.executable,
        str(_script_path(benchmark_root, "run_benchmark.py")),
        "--benchmark-root",
        str(benchmark_root),
        "_run-condition",
        "--results-root",
        str(results_root),
        "--pair-id",
        str(pair["pair_id"]),
        "--condition",
        condition,
        "--slot-file",
        str(slot_file),
    ]


def _cpu_guard_lease_id(campaign: Mapping[str, Any]) -> str:
    campaign_id = campaign.get("campaign_id")
    if not isinstance(campaign_id, str):
        raise MeasurementError("campaign has no CPU-guard lease identity")
    lease_id = f"{campaign_id}-{uuid.uuid4().hex[:16]}"
    if _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None:
        raise MeasurementError("campaign CPU-guard lease identity is invalid")
    return lease_id


def _cpu_guard_slot_lists(
    slots: Sequence[Mapping[str, Any]],
) -> list[str]:
    if not slots:
        raise MeasurementError("CPU guard requires at least one resource slot")
    result: list[str] = []
    used: set[int] = set()
    for slot in slots:
        raw = slot.get("logical_cpus")
        if (
            not isinstance(raw, list)
            or not raw
            or any(isinstance(cpu, bool) or not isinstance(cpu, int) for cpu in raw)
        ):
            raise MeasurementError("CPU guard resource slot has invalid CPUs")
        cpus = tuple(sorted(raw))
        if len(cpus) != len(set(cpus)) or used.intersection(cpus):
            raise MeasurementError("CPU guard resource slots overlap")
        used.update(cpus)
        result.append(resources.format_cpu_list(cpus))
    return result


def _require_cpu_guard_capacity(
    status: Mapping[str, Any], slots: Sequence[Mapping[str, Any]]
) -> None:
    slot_lists = _cpu_guard_slot_lists(slots)
    try:
        allowed = frozenset(
            resources.parse_cpu_list(str(status.get("allowed_cpus")))
        )
    except resources.ResourceIsolationError as error:
        raise MeasurementError(
            f"installed CPU-guard allowed CPU list is invalid: {error}"
        ) from error
    requested = frozenset(
        cpu
        for raw in slot_lists
        for cpu in resources.parse_cpu_list(raw)
    )
    maximum_slots = status.get("maximum_slots")
    if (
        isinstance(maximum_slots, bool)
        or not isinstance(maximum_slots, int)
        or len(slot_lists) > maximum_slots
        or not requested <= allowed
    ):
        raise MeasurementError(
            "campaign CPU slots exceed the installed CPU-guard capability"
        )


def _cpu_guard_executable_identity() -> dict[str, Any]:
    benchmark_root = Path(__file__).resolve().parent.parent
    components = (
        (
            "frontend",
            CPU_GUARD_PATH,
            CPU_GUARD_FRONTEND_SOURCE_RELATIVE,
            "VSCLReuse CPU-guard frontend",
        ),
        (
            "host_helper",
            CPU_GUARD_HOST_PATH,
            CPU_GUARD_SOURCE_RELATIVE,
            "VSCLReuse CPU-guard host helper",
        ),
    )
    identity: dict[str, Any] = {}
    for key, installed_path, source_relative, label in components:
        path = resolved_regular_file(installed_path, label=label)
        for directory in (
            path.parent,
            path.parent.parent,
            path.parent.parent.parent,
        ):
            directory_status = directory.lstat()
            if (
                not stat.S_ISDIR(directory_status.st_mode)
                or directory_status.st_uid != 0
                or directory_status.st_gid != 0
                or stat.S_IMODE(directory_status.st_mode) & 0o022
            ):
                raise MeasurementError(
                    "VSCLReuse CPU-guard installation directories must be "
                    "root-owned and not writable by group/other"
                )
        status = path.stat()
        mode = stat.S_IMODE(status.st_mode)
        if (
            status.st_uid != 0
            or status.st_gid != 0
            or status.st_nlink != 1
            or mode != 0o755
        ):
            raise MeasurementError(
                f"{label} must be a root-owned, singly linked mode-0755 executable"
            )
        source = resolved_regular_file(
            benchmark_root / source_relative,
            label=f"tracked {label} source",
        )
        installed_sha256 = sha256_file(path)
        status_after_hash = path.stat()
        stable_fields = (
            "st_dev",
            "st_ino",
            "st_mode",
            "st_uid",
            "st_gid",
            "st_nlink",
            "st_size",
            "st_mtime_ns",
            "st_ctime_ns",
        )
        if any(
            getattr(status, field) != getattr(status_after_hash, field)
            for field in stable_fields
        ):
            raise MeasurementError(
                f"installed {label} changed while it was being authenticated"
            )
        source_sha256 = sha256_file(source)
        if installed_sha256 != source_sha256:
            raise MeasurementError(
                f"installed {label} differs from the tracked campaign source"
            )
        identity[key] = {
            "path": str(path),
            "device": status.st_dev,
            "inode": status.st_ino,
            "owner_uid": status.st_uid,
            "owner_gid": status.st_gid,
            "hard_links": status.st_nlink,
            "mode": oct(mode),
            "sha256": installed_sha256,
            "tracked_source": {
                "path": source_relative.as_posix(),
                "bytes": source.stat().st_size,
                "sha256": source_sha256,
            },
        }
    return identity


def _cpu_guard_acquire_command(
    lease_id: str,
    evidence_path: Path,
    slots: Sequence[Mapping[str, Any]],
) -> list[str]:
    if _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None:
        raise MeasurementError("invalid CPU-guard lease id")
    command = [
        str(CPU_GUARD_SUDO_PATH),
        "-n",
        "--",
        str(CPU_GUARD_PATH),
        "acquire",
        "--lease-id",
        lease_id,
        "--evidence",
        str(evidence_path.resolve()),
    ]
    for cpu_list in _cpu_guard_slot_lists(slots):
        command.extend(["--slot", cpu_list])
    return command


def _cpu_guard_status_command() -> list[str]:
    return [
        str(CPU_GUARD_SUDO_PATH),
        "-n",
        "--",
        str(CPU_GUARD_PATH),
        "status",
    ]


def _cpu_guard_launch_command(
    lease_id: str,
    unit_name: str,
    slot: Mapping[str, Any],
    payload: Sequence[str],
    *,
    working_directory: Path,
    proof_file: Path,
) -> list[str]:
    if _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None:
        raise MeasurementError("invalid CPU-guard lease id")
    if _CPU_GUARD_UNIT_RE.fullmatch(unit_name) is None:
        raise MeasurementError("invalid CPU-guard unit name")
    slot_lists = _cpu_guard_slot_lists([slot])
    if not payload or any(not isinstance(item, str) or "\x00" in item for item in payload):
        raise MeasurementError("invalid CPU-guard payload")
    cwd = working_directory.resolve()
    if not cwd.is_dir():
        raise MeasurementError(f"CPU-guard working directory is missing: {cwd}")
    return [
        str(CPU_GUARD_SUDO_PATH),
        "-n",
        "--",
        str(CPU_GUARD_PATH),
        "launch",
        "--lease-id",
        lease_id,
        "--unit",
        unit_name,
        "--slot",
        slot_lists[0],
        "--working-directory",
        str(cwd),
        "--proof-file",
        str(proof_file.resolve()),
        "--",
        *payload,
    ]


def _cpu_guard_release_command(lease_id: str, evidence_path: Path) -> list[str]:
    if _CPU_GUARD_LEASE_RE.fullmatch(lease_id) is None:
        raise MeasurementError("invalid CPU-guard lease id")
    return [
        str(CPU_GUARD_SUDO_PATH),
        "-n",
        "--",
        str(CPU_GUARD_PATH),
        "release",
        "--lease-id",
        lease_id,
        "--evidence",
        str(evidence_path.resolve()),
    ]


def _private_cpu_guard_lease_directory(
    results_root: Path, lease_id: str
) -> Path:
    root = results_root / "cpu_guard_leases"
    try:
        root.mkdir(mode=0o700)
    except FileExistsError:
        pass
    root_status = root.lstat()
    if (
        root.is_symlink()
        or not stat.S_ISDIR(root_status.st_mode)
        or root_status.st_uid != os.getuid()
        or stat.S_IMODE(root_status.st_mode) & 0o077
    ):
        raise MeasurementError("CPU-guard lease root is not private and user-owned")
    lease_root = root / lease_id
    try:
        lease_root.mkdir(mode=0o700)
    except FileExistsError as error:
        raise MeasurementError("CPU-guard lease directory already exists") from error
    return lease_root


def _validate_cpu_guard_acquire_evidence(
    evidence: Mapping[str, Any],
    *,
    lease_id: str,
    expected_slots: Sequence[str],
) -> None:
    expected_keys = {
        "schema_version",
        "kind",
        "verified",
        "lease_id",
        "slots",
        "slot_details",
        "reserved_cpus",
        "host_cpus",
        "idle_sample_seconds",
        "maximum_busy_percent",
        "observed_busy_percent",
        "pre_partition_observed_busy_percent",
        "exclusive_post_partition_observed_busy_percent",
        "pinned_foreign_threads",
    }
    if (
        set(evidence) != expected_keys
        or evidence.get("schema_version") != 1
        or evidence.get("kind") != CPU_GUARD_ACQUIRE_KIND
        or evidence.get("verified") is not True
        or evidence.get("lease_id") != lease_id
        or evidence.get("slots") != list(expected_slots)
        or evidence.get("pinned_foreign_threads") != []
    ):
        raise MeasurementError("CPU-guard acquire evidence identity is invalid")

    try:
        slot_sets = [frozenset(resources.parse_cpu_list(raw)) for raw in expected_slots]
        if any(
            not cpus or resources.format_cpu_list(cpus) != raw
            for raw, cpus in zip(expected_slots, slot_sets, strict=True)
        ):
            raise MeasurementError("CPU-guard acquire slot list is not canonical")
        reserved = frozenset(cpu for cpus in slot_sets for cpu in cpus)
        if sum(len(cpus) for cpus in slot_sets) != len(reserved):
            raise MeasurementError("CPU-guard acquire slots overlap")
        reserved_raw = evidence.get("reserved_cpus")
        host_raw = evidence.get("host_cpus")
        if not isinstance(reserved_raw, str) or not isinstance(host_raw, str):
            raise MeasurementError("CPU-guard acquire CPU split is missing")
        observed_reserved = frozenset(resources.parse_cpu_list(reserved_raw))
        host = frozenset(resources.parse_cpu_list(host_raw))
        if (
            not host
            or observed_reserved != reserved
            or resources.format_cpu_list(observed_reserved) != reserved_raw
            or resources.format_cpu_list(host) != host_raw
            or host & reserved
        ):
            raise MeasurementError("CPU-guard acquire host/reserved split is invalid")
    except resources.ResourceIsolationError as error:
        raise MeasurementError(
            f"CPU-guard acquire CPU list is invalid: {error}"
        ) from error

    details = evidence.get("slot_details")
    if not isinstance(details, list) or len(details) != len(slot_sets):
        raise MeasurementError("CPU-guard acquire slot details are invalid")
    for index, (detail, slot_cpus) in enumerate(
        zip(details, slot_sets, strict=True)
    ):
        if (
            not isinstance(detail, Mapping)
            or set(detail)
            != {"slot_id", "physical_slot", "cpus", "physical_cores"}
            or isinstance(detail.get("slot_id"), bool)
            or detail.get("slot_id") != index
            or isinstance(detail.get("physical_slot"), bool)
            or detail.get("physical_slot") != index
            or detail.get("cpus") != expected_slots[index]
            or not isinstance(detail.get("physical_cores"), list)
            or len(detail["physical_cores"]) != 4
            or not all(isinstance(raw, str) for raw in detail["physical_cores"])
        ):
            raise MeasurementError("CPU-guard acquire slot details are invalid")
        try:
            core_sets = [
                frozenset(resources.parse_cpu_list(raw))
                for raw in detail["physical_cores"]
            ]
            if any(
                not cpus or resources.format_cpu_list(cpus) != raw
                for raw, cpus in zip(
                    detail["physical_cores"], core_sets, strict=True
                )
            ):
                raise MeasurementError(
                    "CPU-guard acquire physical-core lists are not canonical"
                )
        except resources.ResourceIsolationError as error:
            raise MeasurementError(
                f"CPU-guard acquire physical-core list is invalid: {error}"
            ) from error
        core_union = frozenset(cpu for cpus in core_sets for cpu in cpus)
        if (
            sum(len(cpus) for cpus in core_sets) != len(core_union)
            or core_union != slot_cpus
            or core_sets != sorted(core_sets, key=lambda cpus: min(cpus))
        ):
            raise MeasurementError(
                "CPU-guard acquire physical cores do not exactly form their slot"
            )

    idle_seconds = evidence.get("idle_sample_seconds")
    maximum_busy = evidence.get("maximum_busy_percent")
    if (
        isinstance(idle_seconds, bool)
        or not isinstance(idle_seconds, (int, float))
        or not math.isfinite(float(idle_seconds))
        or float(idle_seconds) != CPU_GUARD_IDLE_SAMPLE_SECONDS
        or isinstance(maximum_busy, bool)
        or not isinstance(maximum_busy, (int, float))
        or not math.isfinite(float(maximum_busy))
        or float(maximum_busy) != CPU_GUARD_MAXIMUM_BUSY_PERCENT
    ):
        raise MeasurementError("CPU-guard acquire idle-admission policy is invalid")
    expected_cpu_keys = {str(cpu) for cpu in reserved}

    def validate_sample(value: object, label: str) -> Mapping[str, Any]:
        if not isinstance(value, Mapping) or set(value) != expected_cpu_keys:
            raise MeasurementError(
                f"CPU-guard acquire {label} does not cover the reserved union"
            )
        for cpu, percent in value.items():
            if (
                isinstance(percent, bool)
                or not isinstance(percent, (int, float))
                or not math.isfinite(float(percent))
                or float(percent) < 0.0
                or float(percent) > float(maximum_busy)
            ):
                raise MeasurementError(
                    f"CPU-guard acquire {label} has invalid value for CPU {cpu}"
                )
        return value

    pre_sample = validate_sample(
        evidence.get("pre_partition_observed_busy_percent"),
        "pre-partition idle sample",
    )
    validate_sample(
        evidence.get("exclusive_post_partition_observed_busy_percent"),
        "exclusive post-partition idle sample",
    )
    if evidence.get("observed_busy_percent") != pre_sample:
        raise MeasurementError(
            "CPU-guard acquire observed_busy_percent is not the pre-sample alias"
        )


def _validate_cpu_guard_release_evidence(
    evidence: Mapping[str, Any],
    *,
    lease_id: str,
    expected_slots: Sequence[str],
    allowed_recovery_phases: set[str],
    allow_already_inactive: bool,
) -> None:
    common_keys = {
        "schema_version",
        "kind",
        "verified",
        "lease_id",
        "slots",
        "released",
    }
    if (
        evidence.get("schema_version") != 1
        or evidence.get("kind") != CPU_GUARD_RELEASE_KIND
        or evidence.get("verified") is not True
        or evidence.get("lease_id") != lease_id
        or evidence.get("released") is not True
    ):
        raise MeasurementError("CPU-guard release evidence identity is invalid")
    if evidence.get("already_inactive") is True:
        if (
            not allow_already_inactive
            or set(evidence) != common_keys | {"already_inactive"}
            or evidence.get("slots") != []
        ):
            raise MeasurementError(
                "CPU-guard release unexpectedly reported an inactive lease"
            )
        return
    stale_records = evidence.get("stale_launch_records")
    phase = evidence.get("recovered_from_phase")
    if (
        set(evidence)
        != common_keys | {"recovered_from_phase", "stale_launch_records"}
        or evidence.get("slots") != list(expected_slots)
        or phase not in allowed_recovery_phases
        or not isinstance(stale_records, Mapping)
        or not all(
            isinstance(slot, str) and isinstance(unit, str)
            for slot, unit in stale_records.items()
        )
    ):
        raise MeasurementError("CPU-guard release transaction evidence is invalid")


def _private_cpu_guard_recovery_directory(
    results_root: Path, campaign_id: str
) -> Path:
    if _CPU_GUARD_LEASE_RE.fullmatch(campaign_id) is None:
        raise MeasurementError("CPU-guard recovery campaign id is invalid")
    root = results_root / "cpu_guard_recoveries"
    try:
        root.mkdir(mode=0o700)
    except FileExistsError:
        pass
    root_status = root.lstat()
    if (
        root.is_symlink()
        or not stat.S_ISDIR(root_status.st_mode)
        or root_status.st_uid != os.getuid()
        or stat.S_IMODE(root_status.st_mode) != 0o700
        or root.resolve(strict=True) != root
    ):
        raise MeasurementError(
            "CPU-guard recovery root is not private, real, and user-owned"
        )
    attempt_id = f"{campaign_id}-{uuid.uuid4().hex[:16]}"
    attempt_root = root / attempt_id
    try:
        attempt_root.mkdir(mode=0o700)
    except FileExistsError as error:  # pragma: no cover - UUID collision
        raise MeasurementError(
            "CPU-guard recovery attempt directory already exists"
        ) from error
    return attempt_root


def _private_cpu_guard_artifact(path: Path, *, label: str) -> Path:
    """Authenticate a coordinator/root-guard artifact in a private result tree."""

    resolved = resolved_regular_file(path, label=label)
    absolute = Path(os.path.abspath(os.fspath(path)))
    status = resolved.stat()
    if (
        resolved != absolute
        or status.st_uid != os.getuid()
        or status.st_nlink != 1
        or stat.S_IMODE(status.st_mode) != 0o600
    ):
        raise MeasurementError(
            f"{label} must be a private, singly linked, user-owned regular file"
        )
    return resolved


def _fsync_private_cpu_guard_directory(path: Path, *, label: str) -> None:
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise MeasurementError(f"cannot open {label} for fsync: {error}") from error
    try:
        status = os.fstat(descriptor)
        if (
            not stat.S_ISDIR(status.st_mode)
            or status.st_uid != os.getuid()
            or stat.S_IMODE(status.st_mode) != 0o700
        ):
            raise MeasurementError(f"{label} is not private and user-owned")
        os.fsync(descriptor)
    except OSError as error:
        raise MeasurementError(f"cannot fsync {label}: {error}") from error
    finally:
        os.close(descriptor)


def _write_cpu_guard_acquire_intent(
    results_root: Path,
    lease_root: Path,
    campaign: Mapping[str, Any],
    lease_id: str,
    slot_lists: Sequence[str],
    executable: Mapping[str, Any],
) -> dict[str, Any]:
    campaign_id = campaign.get("campaign_id")
    campaign_lock_sha256 = campaign.get("record_sha256")
    if (
        not isinstance(campaign_id, str)
        or not isinstance(campaign_lock_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", campaign_lock_sha256) is None
        or re.fullmatch(
            rf"{re.escape(campaign_id)}-[0-9a-f]{{16}}", lease_id
        )
        is None
    ):
        raise MeasurementError("CPU-guard acquire intent identity is invalid")
    intent: dict[str, Any] = {
        "schema_version": 1,
        "kind": CPU_GUARD_ACQUIRE_INTENT_KIND,
        "campaign_id": campaign_id,
        "campaign_lock_sha256": campaign_lock_sha256,
        "lease_id": lease_id,
        "created_at_utc": utc_now(),
        "slots": list(slot_lists),
        "reserved_cpus": _cpu_guard_reserved_list(slot_lists),
        "cpu_guard_executable": dict(executable),
    }
    intent["record_sha256"] = canonical_digest(intent)
    intent_path = lease_root / "intent.json"
    if intent_path.exists() or intent_path.is_symlink():
        raise MeasurementError("CPU-guard acquire intent already exists")
    atomic_write_json(intent_path, intent, mode=0o600)
    # The intent must survive a coordinator crash before sudo can mutate the
    # guard state.  The file fsync occurs in atomic_write_json; this directory
    # fsync makes the final rename durable too.
    _fsync_private_cpu_guard_directory(
        lease_root, label="CPU-guard lease directory"
    )
    intent_file = _private_cpu_guard_artifact(
        intent_path, label="CPU-guard acquire intent"
    )
    return artifact(intent_file, relative_to=results_root)


def _run_cpu_guard_status(
    results_root: Path, attempt_root: Path
) -> tuple[dict[str, Any], dict[str, Any]]:
    status_path = attempt_root / "status.json"
    log_path = attempt_root / "status.log"
    command = _cpu_guard_status_command()
    if (
        status_path.exists()
        or status_path.is_symlink()
        or log_path.exists()
        or log_path.is_symlink()
    ):
        raise MeasurementError("CPU-guard status artifact path already exists")
    try:
        with status_path.open("xb") as output, log_path.open("xb") as log:
            os.chmod(status_path, 0o600)
            os.chmod(log_path, 0o600)
            completed = subprocess.run(
                command,
                stdout=output,
                stderr=log,
                check=False,
            )
            output.flush()
            log.flush()
            os.fsync(output.fileno())
            os.fsync(log.fileno())
    except (OSError, subprocess.SubprocessError) as error:
        raise MeasurementError(f"CPU-guard status invocation failed: {error}") from error
    if completed.returncode != 0:
        raise MeasurementError(
            f"CPU-guard status failed with exit code {completed.returncode}; "
            f"see {log_path}"
        )
    status_file = _private_cpu_guard_artifact(
        status_path, label="CPU-guard status evidence"
    )
    log_file = _private_cpu_guard_artifact(
        log_path, label="CPU-guard status log"
    )
    evidence = read_object(status_file)
    generation = evidence.get("generation")
    phase = evidence.get("phase")
    recovery_required = evidence.get("recovery_required")
    active = evidence.get("active_lease")
    applied = evidence.get("applied")
    idle_seconds = evidence.get("idle_sample_seconds")
    maximum_busy = evidence.get("maximum_busy_percent")
    allowed_raw = evidence.get("allowed_cpus")
    maximum_slots = evidence.get("maximum_slots")
    try:
        allowed_cpus = (
            frozenset(resources.parse_cpu_list(allowed_raw))
            if isinstance(allowed_raw, str)
            else frozenset()
        )
    except resources.ResourceIsolationError as error:
        raise MeasurementError(
            f"CPU-guard status allowed CPU list is invalid: {error}"
        ) from error
    if (
        set(evidence)
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
        or isinstance(idle_seconds, bool)
        or not isinstance(idle_seconds, (int, float))
        or not math.isfinite(float(idle_seconds))
        or float(idle_seconds) != CPU_GUARD_IDLE_SAMPLE_SECONDS
        or isinstance(maximum_busy, bool)
        or not isinstance(maximum_busy, (int, float))
        or not math.isfinite(float(maximum_busy))
        or float(maximum_busy) != CPU_GUARD_MAXIMUM_BUSY_PERCENT
        or not allowed_cpus
        or resources.format_cpu_list(allowed_cpus) != allowed_raw
        or isinstance(maximum_slots, bool)
        or not isinstance(maximum_slots, int)
        or maximum_slots < 1
        or evidence.get("schema_version") != 1
        or evidence.get("kind") != CPU_GUARD_STATUS_KIND
        or evidence.get("verified") is not True
        or isinstance(generation, bool)
        or not isinstance(generation, int)
        or generation < 0
        or phase not in {"inactive", "preparing", "active", "releasing"}
        or not isinstance(recovery_required, bool)
        or recovery_required != (phase in {"preparing", "releasing"})
        or (
            phase == "inactive"
            and (active is not None or applied is not None)
        )
        or (
            phase != "inactive"
            and (
                not isinstance(active, dict)
                or not isinstance(applied, dict)
                or not isinstance(active.get("lease_id"), str)
                or _CPU_GUARD_LEASE_RE.fullmatch(str(active.get("lease_id")))
                is None
                or not isinstance(active.get("slots"), list)
                or not all(isinstance(item, str) for item in active["slots"])
                or not isinstance(active.get("reserved_cpus"), str)
                or not isinstance(applied.get("reserved_cpus"), str)
            )
        )
    ):
        raise MeasurementError("CPU-guard status evidence is invalid")
    return (
        {
            "command": command,
            "evidence": artifact(status_file, relative_to=results_root),
            "log": artifact(log_file, relative_to=results_root),
        },
        evidence,
    )


def _cpu_guard_reserved_list(slot_lists: Sequence[str]) -> str:
    cpus: set[int] = set()
    for slot in slot_lists:
        parsed = resources.parse_cpu_list(slot)
        if not parsed or cpus.intersection(parsed):
            raise MeasurementError("CPU-guard recovery slot lists overlap or are empty")
        cpus.update(parsed)
    return resources.format_cpu_list(cpus)


def _owned_stale_cpu_guard_lease(
    results_root: Path,
    campaign_id: str,
    campaign_lock_sha256: str,
    active: Mapping[str, Any],
    applied: Mapping[str, Any],
    expected_slots: Sequence[str],
    expected_reserved: str,
    executable: Mapping[str, Any],
) -> dict[str, Any]:
    lease_id = active.get("lease_id")
    expected_id = re.compile(
        rf"^{re.escape(campaign_id)}-[0-9a-f]{{16}}$"
    )
    if not isinstance(lease_id, str) or expected_id.fullmatch(lease_id) is None:
        raise MeasurementError(
            "active CPU-guard lease is not owned by this exact campaign"
        )
    if (
        active.get("slots") != list(expected_slots)
        or active.get("reserved_cpus") != expected_reserved
        or applied.get("reserved_cpus") != expected_reserved
    ):
        raise MeasurementError(
            "active CPU-guard lease does not match this campaign's exact slots"
        )
    lease_container = results_root / "cpu_guard_leases"
    lease_root = lease_container / lease_id
    for path, label in (
        (lease_container, "CPU-guard lease root"),
        (lease_root, "stale CPU-guard lease directory"),
    ):
        try:
            status = path.lstat()
        except OSError as error:
            raise MeasurementError(f"{label} is missing") from error
        if (
            stat.S_ISLNK(status.st_mode)
            or not stat.S_ISDIR(status.st_mode)
            or status.st_uid != os.getuid()
            or stat.S_IMODE(status.st_mode) != 0o700
            or path.resolve(strict=True) != path
        ):
            raise MeasurementError(f"{label} is not private, real, and user-owned")
    acquire_log = _private_cpu_guard_artifact(
        lease_root / "acquire.log", label="stale CPU-guard acquire log"
    )
    result = {
        "lease_id": lease_id,
        "acquire_log": artifact(acquire_log, relative_to=results_root),
    }
    ownership_proven = False
    intent_path = lease_root / "intent.json"
    if intent_path.exists() or intent_path.is_symlink():
        intent_file = _private_cpu_guard_artifact(
            intent_path, label="stale CPU-guard acquire intent"
        )
        intent = read_object(intent_file, kind=CPU_GUARD_ACQUIRE_INTENT_KIND)
        intent_payload = dict(intent)
        intent_sha256 = intent_payload.pop("record_sha256", None)
        if (
            intent_sha256 != canonical_digest(intent_payload)
            or intent.get("schema_version") != 1
            or intent.get("campaign_id") != campaign_id
            or intent.get("campaign_lock_sha256") != campaign_lock_sha256
            or intent.get("lease_id") != lease_id
            or intent.get("slots") != list(expected_slots)
            or intent.get("reserved_cpus") != expected_reserved
            or intent.get("cpu_guard_executable") != dict(executable)
            or not isinstance(intent.get("created_at_utc"), str)
        ):
            raise MeasurementError(
                "stale CPU-guard acquire intent does not prove campaign ownership"
            )
        result["intent"] = artifact(intent_file, relative_to=results_root)
        ownership_proven = True
    acquire_path = lease_root / "acquire.json"
    if acquire_path.exists() or acquire_path.is_symlink():
        acquire_file = _private_cpu_guard_artifact(
            acquire_path, label="stale CPU-guard acquire evidence"
        )
        acquire = read_object(acquire_file)
        _validate_cpu_guard_acquire_evidence(
            acquire,
            lease_id=lease_id,
            expected_slots=expected_slots,
        )
        result["acquire_evidence"] = artifact(
            acquire_file, relative_to=results_root
        )
        ownership_proven = True
    if not ownership_proven:
        raise MeasurementError(
            "stale CPU-guard lease lacks a durable campaign ownership artifact"
        )
    old_release_path = lease_root / "release.json"
    if old_release_path.exists() or old_release_path.is_symlink():
        raise MeasurementError(
            "active CPU-guard state conflicts with an existing release evidence file"
        )
    return result


def _cpu_guard_recovery_request(
    attempt_root: Path,
    *,
    campaign_id: str,
    campaign_lock_sha256: str,
    expected_slots: Sequence[str],
    expected_reserved: str,
) -> dict[str, Any]:
    request: dict[str, Any] = {
        "schema_version": 1,
        "kind": CPU_GUARD_RECOVERY_REQUEST_KIND,
        "campaign_id": campaign_id,
        "campaign_lock_sha256": campaign_lock_sha256,
        "created_at_utc": utc_now(),
        "expected_slots": list(expected_slots),
        "expected_reserved_cpus": expected_reserved,
    }
    request["record_sha256"] = canonical_digest(request)
    atomic_write_json(attempt_root / "request.json", request, mode=0o600)
    return request


def _seal_cpu_guard_recovery_record(
    results_root: Path,
    attempt_root: Path,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    record = dict(payload)
    record["record_sha256"] = canonical_digest(record)
    record_path = attempt_root / "result.json"
    if record_path.exists() or record_path.is_symlink():
        raise MeasurementError("CPU-guard recovery result already exists")
    atomic_write_json(record_path, record, mode=0o600)
    record_file = _private_cpu_guard_artifact(
        record_path, label="CPU-guard recovery result"
    )
    return {
        "schema_version": 1,
        "kind": CPU_GUARD_RECOVERY_KIND,
        "outcome": record.get("outcome"),
        "record": artifact(record_file, relative_to=results_root),
    }


def _pre_acquire_cpu_guard_recovery(
    results_root: Path,
    campaign: Mapping[str, Any],
    slots: Sequence[Mapping[str, Any]],
    executable: Mapping[str, Any],
) -> dict[str, Any]:
    """Release only an authenticated, quiescent lease from this campaign.

    The privileged release operation owns the authoritative exclusive flock
    and populated-cgroup checks.  This coordinator-side proof only narrows the
    lease that may be named; it never signals, stops, or migrates a process.
    """

    campaign_id = campaign.get("campaign_id")
    campaign_lock_sha256 = campaign.get("record_sha256")
    if (
        not isinstance(campaign_id, str)
        or _CPU_GUARD_LEASE_RE.fullmatch(campaign_id) is None
        or not isinstance(campaign_lock_sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", campaign_lock_sha256) is None
    ):
        raise MeasurementError("campaign cannot authorize CPU-guard recovery")
    expected_slots = _cpu_guard_slot_lists(slots)
    expected_reserved = _cpu_guard_reserved_list(expected_slots)
    attempt_root = _private_cpu_guard_recovery_directory(
        results_root, campaign_id
    )
    request = _cpu_guard_recovery_request(
        attempt_root,
        campaign_id=campaign_id,
        campaign_lock_sha256=campaign_lock_sha256,
        expected_slots=expected_slots,
        expected_reserved=expected_reserved,
    )
    base: dict[str, Any] = {
        "schema_version": 1,
        "kind": CPU_GUARD_RECOVERY_KIND,
        "campaign_id": campaign_id,
        "campaign_lock_sha256": campaign_lock_sha256,
        "recorded_at_utc": utc_now(),
        "expected_slots": expected_slots,
        "expected_reserved_cpus": expected_reserved,
        "request": artifact(
            attempt_root / "request.json", relative_to=results_root
        ),
        "request_record_sha256": request["record_sha256"],
    }
    status_control: dict[str, Any] | None = None
    try:
        status_control, status = _run_cpu_guard_status(
            results_root, attempt_root
        )
        base["status"] = status_control
        allowed_cpus = frozenset(
            resources.parse_cpu_list(str(status["allowed_cpus"]))
        )
        requested_cpus = frozenset(
            cpu
            for raw in expected_slots
            for cpu in resources.parse_cpu_list(raw)
        )
        if (
            not requested_cpus <= allowed_cpus
            or len(expected_slots) > int(status["maximum_slots"])
        ):
            raise MeasurementError(
                "campaign CPU slots exceed the installed CPU-guard capability"
            )
        active = status.get("active_lease")
        if active is None:
            base["outcome"] = "guard-inactive"
            return _seal_cpu_guard_recovery_record(
                results_root, attempt_root, base
            )
        applied = status.get("applied")
        if not isinstance(active, Mapping) or not isinstance(applied, Mapping):
            raise MeasurementError("active CPU-guard status is malformed")
        owned = _owned_stale_cpu_guard_lease(
            results_root,
            campaign_id,
            campaign_lock_sha256,
            active,
            applied,
            expected_slots,
            expected_reserved,
            executable,
        )
        base["stale_lease"] = owned
        lease_id = str(owned["lease_id"])
        release_path = attempt_root / "release.json"
        release_log = attempt_root / "release.log"
        release_control = _run_cpu_guard_control(
            _cpu_guard_release_command(lease_id, release_path),
            evidence_path=release_path,
            log_path=release_log,
            action="release",
            lease_id=lease_id,
            expected_slots=expected_slots,
        )
        release_evidence = read_object(release_path)
        _validate_cpu_guard_release_evidence(
            release_evidence,
            lease_id=lease_id,
            expected_slots=expected_slots,
            allowed_recovery_phases={str(status.get("phase"))},
            allow_already_inactive=False,
        )
        base["release"] = release_control
        base["outcome"] = "released-owned-stale-lease"
        return _seal_cpu_guard_recovery_record(
            results_root, attempt_root, base
        )
    except BaseException as error:
        failure = {
            **base,
            "outcome": "recovery-refused-or-failed",
            "error": {
                "type": type(error).__name__,
                "message": str(error),
            },
        }
        if status_control is not None:
            failure["status"] = status_control
        try:
            _seal_cpu_guard_recovery_record(results_root, attempt_root, failure)
        except BaseException:
            # Preserve the original safety failure.  The request/status/release
            # files in the fresh attempt directory remain available for audit.
            pass
        raise


def _run_cpu_guard_control(
    command: Sequence[str],
    *,
    evidence_path: Path,
    log_path: Path,
    action: str,
    lease_id: str,
    expected_slots: Sequence[str] | None = None,
) -> dict[str, Any]:
    if evidence_path.exists() or evidence_path.is_symlink():
        raise MeasurementError(f"CPU-guard {action} evidence path already exists")
    try:
        with log_path.open("xb") as log:
            os.chmod(log_path, 0o600)
            completed = subprocess.run(
                list(command),
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
    except (OSError, subprocess.SubprocessError) as error:
        raise MeasurementError(f"CPU-guard {action} invocation failed: {error}") from error
    if completed.returncode != 0:
        raise MeasurementError(
            f"CPU-guard {action} failed with exit code {completed.returncode}; "
            f"see {log_path}"
        )
    evidence_file = resolved_regular_file(
        evidence_path, label=f"CPU-guard {action} evidence"
    )
    evidence = read_object(evidence_file)
    expected_kind = (
        CPU_GUARD_ACQUIRE_KIND if action == "acquire" else CPU_GUARD_RELEASE_KIND
    )
    if (
        evidence.get("schema_version") != 1
        or evidence.get("kind") != expected_kind
        or evidence.get("verified") is not True
        or evidence.get("lease_id") != lease_id
        or (action == "release" and evidence.get("released") is not True)
        or (
            expected_slots is not None
            and evidence.get("slots") != list(expected_slots)
        )
    ):
        raise MeasurementError(f"CPU-guard {action} evidence is invalid")
    if action == "acquire":
        if expected_slots is None:
            raise MeasurementError(
                "CPU-guard acquire validation lacks expected slots"
            )
        _validate_cpu_guard_acquire_evidence(
            evidence,
            lease_id=lease_id,
            expected_slots=expected_slots,
        )
    return {
        "command": list(command),
        "evidence": artifact(evidence_file, relative_to=evidence_path.parents[2]),
        "log": artifact(log_path, relative_to=evidence_path.parents[2]),
    }


def _acquire_cpu_guard(
    results_root: Path,
    campaign: Mapping[str, Any],
    slots: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    executable = _cpu_guard_executable_identity()
    pre_acquire = _pre_acquire_cpu_guard_recovery(
        results_root, campaign, slots, executable
    )
    lease_id = _cpu_guard_lease_id(campaign)
    lease_root = _private_cpu_guard_lease_directory(results_root, lease_id)
    evidence_path = lease_root / "acquire.json"
    log_path = lease_root / "acquire.log"
    command = _cpu_guard_acquire_command(lease_id, evidence_path, slots)
    slot_lists = _cpu_guard_slot_lists(slots)
    intent = _write_cpu_guard_acquire_intent(
        results_root,
        lease_root,
        campaign,
        lease_id,
        slot_lists,
        executable,
    )
    lease: dict[str, Any] = {
        "lease_id": lease_id,
        "slots": slot_lists,
        "executable": executable,
        "pre_acquire": pre_acquire,
        "intent": intent,
        "lease_root": str(lease_root.resolve()),
    }
    try:
        lease["acquire"] = _run_cpu_guard_control(
            command,
            evidence_path=evidence_path,
            log_path=log_path,
            action="acquire",
            lease_id=lease_id,
            expected_slots=slot_lists,
        )
        # The root generation lock is held inside each frontend relay, whereas
        # this unprivileged coordinator can only inspect the installed files.
        # Re-authenticate both binaries after the atomic lease acquisition.
        # Once the lease is active, the installer itself refuses to replace a
        # generation; equality here therefore closes the only pre-acquire
        # replacement window before any provider process can start.
        if _cpu_guard_executable_identity() != executable:
            raise MeasurementError(
                "CPU-guard frontend/host-helper generation changed during acquisition"
            )
    except BaseException as acquire_error:
        # A non-zero or malformed response may still follow a partial kernel
        # allocation.  Always ask the narrow guard to roll the named lease
        # back before propagating the acquisition failure.
        try:
            _release_cpu_guard(results_root, lease, emergency=True)
        except BaseException as release_error:
            raise MeasurementError(
                "CPU-guard acquisition failed and emergency release also failed: "
                f"acquire={acquire_error}; release={release_error}"
            ) from release_error
        raise
    return lease


def _release_cpu_guard(
    results_root: Path,
    lease: Mapping[str, Any],
    *,
    emergency: bool = False,
) -> dict[str, Any]:
    lease_id = lease.get("lease_id")
    lease_root_raw = lease.get("lease_root")
    slots = lease.get("slots")
    if (
        not isinstance(lease_id, str)
        or not isinstance(lease_root_raw, str)
        or not isinstance(slots, list)
        or not slots
        or not all(isinstance(slot, str) for slot in slots)
    ):
        raise MeasurementError("CPU-guard lease state is incomplete")
    lease_root = Path(lease_root_raw)
    try:
        lease_root.resolve().relative_to((results_root / "cpu_guard_leases").resolve())
    except ValueError as error:
        raise MeasurementError("CPU-guard lease state escapes the results root") from error
    evidence_path = lease_root / "release.json"
    log_path = lease_root / "release.log"
    command = _cpu_guard_release_command(lease_id, evidence_path)
    control = _run_cpu_guard_control(
        command,
        evidence_path=evidence_path,
        log_path=log_path,
        action="release",
        lease_id=lease_id,
        expected_slots=None if emergency else slots,
    )
    evidence = read_object(evidence_path)
    _validate_cpu_guard_release_evidence(
        evidence,
        lease_id=lease_id,
        expected_slots=slots,
        allowed_recovery_phases=(
            {"preparing", "active", "releasing"} if emergency else {"active"}
        ),
        allow_already_inactive=emergency,
    )
    return control


def _condition_worker_payload_valid(
    pair_root: Path,
    pair: Mapping[str, Any],
    condition: str,
    lock: Mapping[str, Any],
) -> bool:
    path = pair_root / f"condition-{condition}.worker.json"
    try:
        value = read_object(path, kind="highambench-condition-worker-result")
        payload = dict(value)
        stored = payload.pop("record_sha256", None)
        attempt = value.get("attempt")
        return bool(
            stored == canonical_digest(payload)
            and value.get("schema_version") == 1
            and value.get("pair_id") == pair.get("pair_id")
            and value.get("task_id") == pair.get("task_id")
            and value.get("condition") == condition
            and value.get("complete") is True
            and value.get("infrastructure_failure") is False
            and value.get("campaign_id") == lock.get("campaign_id")
            and value.get("campaign_lock_sha256") == lock.get("record_sha256")
            and value.get("hardware_verification_before")
            == lock.get("hardware_identity")
            and value.get("hardware_verification_after")
            == lock.get("hardware_identity")
            and isinstance(attempt, Mapping)
            and isinstance(attempt.get("returncode"), int)
            and not isinstance(attempt.get("returncode"), bool)
            and isinstance(attempt.get("record"), Mapping)
            and _attempt_terminal_valid(
                _artifact_path(pair_root, attempt["record"]),
                pair_root,
                pair,
                condition,
                lock,
                int(attempt["returncode"]),
                resource_record_path=(
                    pair_root / f"resource_record_{condition}.json"
                ),
            )
        )
    except (KeyError, MeasurementError, OSError, TypeError, ValueError):
        return False


def _launch_condition(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
    pair: Mapping[str, Any],
    condition: str,
    slot: Mapping[str, Any],
    *,
    cpu_guard_lease_id: str,
) -> dict[str, Any]:
    pair_root = _campaign_pair_root(results_root, str(pair["pair_id"]))
    slot_file = pair_root / f"resource_slot_{condition}.json"
    atomic_write_json(slot_file, dict(slot), mode=0o444)
    proof_file = pair_root / f"resource_kernel_proof_{condition}.json"
    child = _condition_worker_command(
        benchmark_root, results_root, pair, condition, slot_file
    )
    unit = (
        "highambench-"
        + re.sub(r"[^A-Za-z0-9_.-]", "-", str(pair["pair_id"]))
        + f"-{condition.lower()}-"
        + uuid.uuid4().hex[:8]
    )
    command = _cpu_guard_launch_command(
        cpu_guard_lease_id,
        unit,
        slot,
        child,
        working_directory=_repository_root(benchmark_root),
        proof_file=proof_file,
    )
    launch_path = pair_root / f"launch_{condition}.json"
    launch_record: dict[str, Any] = {
        "schema_version": 1,
        "kind": "highambench-condition-launch",
        "pair_id": pair["pair_id"],
        "condition": condition,
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "slot": slot,
        "unit": unit,
        "launcher": "privileged-cpu-guard",
        "cpu_guard_lease_id": cpu_guard_lease_id,
        "command": command,
        "started_at_utc": utc_now(),
    }
    atomic_write_json(launch_path, launch_record)
    log_path = pair_root / f"cpu-guard-launch-{condition}.log"
    launch_error: dict[str, str] | None = None
    with log_path.open("wb") as log:
        try:
            process_returncode = subprocess.run(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            ).returncode
        except (OSError, subprocess.SubprocessError) as error:
            process_returncode = 2
            launch_error = {
                "type": type(error).__name__,
                "message": str(error),
            }
            log.write(
                (
                    "\nVSCLReuse launch error: "
                    f"{type(error).__name__}: {error}\n"
                ).encode("utf-8", errors="replace")
            )
    launch_record.update(
        finished_at_utc=utc_now(),
        returncode=process_returncode,
        log=artifact(log_path, relative_to=pair_root),
    )
    if launch_error is not None:
        launch_record["launch_error"] = launch_error
    launch_record["record_sha256"] = canonical_digest(launch_record)
    atomic_write_json(launch_path, launch_record, mode=0o444)
    worker_complete = _condition_worker_payload_valid(
        pair_root, pair, condition, lock
    )
    worker_path = pair_root / f"condition-{condition}.worker.json"
    terminal_record: dict[str, Any] = {
        "schema_version": 1,
        "kind": "highambench-condition-outer-terminal",
        "pair_id": pair["pair_id"],
        "condition": condition,
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "returncode": process_returncode,
        "complete": worker_complete and process_returncode == 0,
        "launch": artifact(launch_path, relative_to=pair_root),
        "worker": (
            artifact(worker_path, relative_to=pair_root)
            if worker_path.is_file() and not worker_path.is_symlink()
            else None
        ),
        "recorded_at_utc": utc_now(),
    }
    terminal_record["record_sha256"] = canonical_digest(terminal_record)
    terminal_path = pair_root / f"condition-{condition}.outer_terminal.json"
    atomic_write_json(terminal_path, terminal_record, mode=0o444)
    return {
        "pair_id": pair["pair_id"],
        "condition": condition,
        "returncode": process_returncode,
        "complete": bool(terminal_record["complete"]),
        "cpu_guard_lease_id": cpu_guard_lease_id,
        "terminal": artifact(terminal_path, relative_to=results_root),
    }


def _finalize_pair(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
    pair: Mapping[str, Any],
    condition_results: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    pair_root = _campaign_pair_root(results_root, str(pair["pair_id"]))
    by_condition = {
        str(result.get("condition")): result for result in condition_results
    }
    workers: list[Mapping[str, Any]] = []
    complete = set(by_condition) == {"N", "L"}
    for condition in ("N", "L"):
        result = by_condition.get(condition)
        if (
            result is None
            or result.get("returncode") != 0
            or result.get("complete") is not True
            or not _condition_worker_payload_valid(
                pair_root, pair, condition, lock
            )
        ):
            complete = False
            continue
        workers.append(
            read_object(
                pair_root / f"condition-{condition}.worker.json",
                kind="highambench-condition-worker-result",
            )
        )
    verification = verify_campaign_inputs(benchmark_root, results_root, lock)
    hardware = _verify_locked_hardware_identity(lock)
    attempts = [worker["attempt"] for worker in workers]
    condition_resources = [
        {
            "condition": worker["condition"],
            "resource": worker["resource"],
            "resource_proof": worker["resource_proof"],
            "resource_worker_proof": worker["resource_worker_proof"],
            "resource_sample": worker["resource_sample"],
            "worker": artifact(
                pair_root / f"condition-{worker['condition']}.worker.json",
                relative_to=pair_root,
            ),
        }
        for worker in workers
    ]
    pair_record: dict[str, Any] = {
        "schema_version": 4,
        "kind": PAIR_KIND,
        "pair_id": pair["pair_id"],
        "task_id": pair["task_id"],
        "repetition_id": pair["repetition_id"],
        "condition_order": list(pair["condition_order"]),
        "condition_order_is_execution_constraint": True,
        "run_ids": list(pair["run_ids"]),
        "complete": complete and len(workers) == 2,
        "infrastructure_failure": not (complete and len(workers) == 2),
        "infrastructure_incidents": [
            artifact(path, relative_to=results_root)
            for path in _incident_records_for_pair(results_root, str(pair["pair_id"]))
        ],
        "attempts": attempts,
        "condition_resources": condition_resources,
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "corpus_verification_before": verification,
        "corpus_verification_after": verification,
        "hardware_verification_before": hardware,
        "hardware_verification_after": hardware,
        "finished_at_utc": utc_now(),
    }
    pair_record["record_sha256"] = canonical_digest(pair_record)
    pair_path = pair_root / "pair.json"
    atomic_write_json(pair_path, pair_record, mode=0o444)
    terminal_record: dict[str, Any] = {
        "schema_version": 2,
        "kind": "highambench-pair-outer-terminal",
        "pair_id": pair["pair_id"],
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "returncode": 0 if pair_record["complete"] else 2,
        "complete": pair_record["complete"],
        "condition_terminals": [
            artifact(
                pair_root / f"condition-{condition}.outer_terminal.json",
                relative_to=pair_root,
            )
            for condition in ("N", "L")
        ],
        "pair": artifact(pair_path, relative_to=pair_root),
        "recorded_at_utc": utc_now(),
    }
    terminal_record["record_sha256"] = canonical_digest(terminal_record)
    terminal_path = pair_root / "outer_terminal.json"
    atomic_write_json(terminal_path, terminal_record, mode=0o444)
    lease_ids = sorted(
        {
            str(result["cpu_guard_lease_id"])
            for result in condition_results
            if isinstance(result.get("cpu_guard_lease_id"), str)
        }
    )
    published_complete = bool(terminal_record["complete"]) and _pair_record_valid(
        pair_root, pair, lock
    )
    return {
        "pair_id": pair["pair_id"],
        "returncode": 0 if published_complete else 2,
        "complete": published_complete,
        "cpu_guard_lease_id": lease_ids[0] if len(lease_ids) == 1 else None,
        "cpu_guard_lease_ids": lease_ids,
        "terminal": artifact(terminal_path, relative_to=results_root),
    }


def _append_campaign_event(
    path: Path, payload: Mapping[str, Any]
) -> dict[str, Any]:
    record = {"schema_version": 1, **dict(payload)}
    record["record_sha256"] = canonical_digest(record)
    append_jsonl(path, record)
    return record


def _campaign_events_for_recovery(
    path: Path, lock: Mapping[str, Any]
) -> tuple[dict[str, Any] | None, set[str]]:
    """Read enough of the audit stream to locate one interrupted invocation.

    This deliberately fails closed on malformed history.  The full verifier
    performs the richer semantic checks; the coordinator only needs a strict
    state machine so it never starts a new preflight while an older invocation
    remains open.
    """

    if not path.exists():
        return None, set()
    event_path = resolved_regular_file(path, label="campaign event log")
    try:
        lines = event_path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as error:
        raise MeasurementError(f"cannot read campaign event log: {error}") from error
    if not lines:
        raise MeasurementError("campaign event log is empty")
    allowed = {
        "campaign-preflight",
        "host-core-locks-acquired",
        "pair-terminal",
        "campaign-terminal",
        "campaign-recovery-terminal",
    }
    active: dict[str, Any] | None = None
    accounted: set[str] = set()
    for line_number, line in enumerate(lines, start=1):
        try:
            event = json.loads(line)
        except json.JSONDecodeError as error:
            raise MeasurementError(
                f"campaign event log line {line_number} is invalid JSON"
            ) from error
        if not isinstance(event, dict):
            raise MeasurementError(
                f"campaign event log line {line_number} is not an object"
            )
        payload = dict(event)
        stored = payload.pop("record_sha256", None)
        kind = event.get("kind")
        if (
            stored != canonical_digest(payload)
            or event.get("schema_version") != 1
            or kind not in allowed
            or event.get("campaign_id") != lock.get("campaign_id")
            or event.get("campaign_lock_sha256") != lock.get("record_sha256")
            or not isinstance(event.get("recorded_at_utc"), str)
        ):
            raise MeasurementError(
                f"campaign event log line {line_number} has invalid identity"
            )
        if kind == "campaign-preflight":
            if active is not None:
                raise MeasurementError("campaign event invocations overlap")
            active = {
                "phase": "preflight",
                "preflight_record_sha256": stored,
                "core_locks_record_sha256": None,
                "pair_events": [],
            }
        elif kind == "host-core-locks-acquired":
            if active is None or active["phase"] != "preflight":
                raise MeasurementError("campaign core locks are out of order")
            recovery_context = event.get("recovery_lock_context")
            if recovery_context is not None and recovery_context != {
                "reacquired_for_interrupted_preflight": True,
                "preflight_record_sha256": active[
                    "preflight_record_sha256"
                ],
            }:
                raise MeasurementError(
                    "campaign recovery core-lock context is invalid"
                )
            if recovery_context is not None and not isinstance(
                event.get("input_verification"), Mapping
            ):
                raise MeasurementError(
                    "campaign recovery core-lock event lacks input verification"
                )
            if recovery_context is not None and (
                event.get("resource_slots") != lock.get("resource_slots")
                or event.get("hardware_identity")
                != lock.get("hardware_identity")
                or not isinstance(event.get("locks"), list)
                or not event["locks"]
            ):
                raise MeasurementError(
                    "campaign recovery core-lock resources are invalid"
                )
            active["phase"] = "locked"
            active["core_locks_record_sha256"] = stored
            active["core_locks_reacquired_for_recovery"] = (
                recovery_context is not None
            )
        elif kind == "pair-terminal":
            if active is None or active["phase"] != "locked":
                raise MeasurementError(
                    "pair terminal event is outside a locked invocation"
                )
            if active.get("core_locks_reacquired_for_recovery") is True:
                raise MeasurementError(
                    "pair terminal follows a synthetic recovery lock event"
                )
            pair_id = event.get("pair_id")
            if not isinstance(pair_id, str) or pair_id in accounted:
                raise MeasurementError("campaign pair terminal is missing or duplicated")
            accounted.add(pair_id)
            active["pair_events"].append(event)
        elif kind == "campaign-terminal":
            if active is None or active["phase"] != "locked":
                raise MeasurementError("campaign terminal event is out of order")
            if active.get("core_locks_reacquired_for_recovery") is True:
                raise MeasurementError(
                    "normal campaign terminal follows a synthetic recovery lock event"
                )
            active = None
        else:
            if active is None or active["phase"] != "locked":
                raise MeasurementError("campaign recovery terminal is out of order")
            recovered = event.get("recovered_pair_results")
            recovered_invocation = event.get("recovered_invocation")
            has_durable_commit = bool(active["pair_events"] or recovered)
            expected_reason = (
                "coordinator-exited-after-durable-pair-commit"
                if has_durable_commit
                else "coordinator-exited-before-campaign-terminal"
            )
            if (
                event.get("reason") != expected_reason
                or event.get("hardware_identity")
                != lock.get("hardware_identity")
                or not isinstance(event.get("input_verification"), Mapping)
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
                or not isinstance(recovered, list)
            ):
                raise MeasurementError("campaign recovery pair results are malformed")
            for result in recovered:
                pair_id = result.get("pair_id") if isinstance(result, Mapping) else None
                returncode = (
                    result.get("returncode")
                    if isinstance(result, Mapping)
                    else None
                )
                if (
                    not isinstance(pair_id, str)
                    or pair_id in accounted
                    or isinstance(returncode, bool)
                    or not isinstance(returncode, int)
                    or result.get("complete") not in (True, False)
                    or not isinstance(result.get("terminal"), Mapping)
                    or (
                        result.get("complete") is True
                        and returncode != 0
                    )
                ):
                    raise MeasurementError(
                        "campaign recovery pair result is missing or duplicated"
                    )
                accounted.add(pair_id)
            active = None
    return active, accounted


def _recover_interrupted_campaign(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
    *,
    input_verification: Mapping[str, Any],
    hardware_identity: Mapping[str, Any],
    host_lock_evidence: Sequence[Mapping[str, Any]],
) -> dict[str, Any] | None:
    """Append a deterministic closure for a safely quiescent crashed run."""

    event_path = results_root / "campaign_events.jsonl"
    active, accounted = _campaign_events_for_recovery(event_path, lock)
    if active is None:
        return None
    if active.get("phase") not in ("preflight", "locked"):
        raise MeasurementError("interrupted campaign has an invalid audit phase")
    ordered_pairs = _order_pairs(benchmark_root)
    expected_by_id = {str(pair["pair_id"]): pair for pair in ordered_pairs}
    pairs_root = _campaign_pairs_root(results_root)

    # Normal pair-terminal events inside the interrupted invocation are part of
    # the closure too.  Authenticate them with the durable pair commit before
    # allowing the recovery event to close the invocation.
    active_pair_hashes: list[str] = []
    for event in active["pair_events"]:
        pair_id = str(event["pair_id"])
        expected = expected_by_id.get(pair_id)
        descriptor = event.get("terminal")
        pair_root = pairs_root / pair_id
        valid_success = bool(
            expected is not None
            and event.get("returncode") == 0
            and event.get("complete") is True
            and isinstance(descriptor, Mapping)
            and _artifact_path(results_root, descriptor)
            == pair_root / "outer_terminal.json"
            and _pair_record_valid(pair_root, expected, lock)
        )
        valid_failure = False
        if expected is not None and event.get("complete") is False:
            try:
                failed_result = _failed_pair_terminal_result(
                    pair_root,
                    expected,
                    lock,
                    relative_to=results_root,
                )
                valid_failure = all(
                    event.get(key) == value
                    for key, value in failed_result.items()
                )
            except (MeasurementError, OSError, KeyError, TypeError, ValueError):
                valid_failure = False
        if not (valid_success or valid_failure):
            raise MeasurementError(
                f"interrupted campaign has an unauthenticated pair event: {pair_id}"
            )
        active_pair_hashes.append(str(event["record_sha256"]))

    recovered_results: list[dict[str, Any]] = []
    for expected in ordered_pairs:
        pair_id = str(expected["pair_id"])
        if pair_id in accounted:
            continue
        pair_root = pairs_root / pair_id
        if not pair_root.exists() and not pair_root.is_symlink():
            continue
        if _pair_record_valid(pair_root, expected, lock):
            terminal_path = pair_root / "outer_terminal.json"
            recovered_results.append(
                {
                    "pair_id": pair_id,
                    "returncode": 0,
                    "complete": True,
                    "terminal": artifact(
                        terminal_path, relative_to=results_root
                    ),
                }
            )
            continue
        try:
            recovered_results.append(
                _failed_pair_terminal_result(
                    pair_root,
                    expected,
                    lock,
                    relative_to=results_root,
                )
            )
        except (MeasurementError, OSError, KeyError, TypeError, ValueError):
            # No durable pair terminal exists.  The new coordinator holds the
            # exclusive CPU lease and archives this partial root immediately
            # after closing the interrupted invocation.
            continue

    # If the old process died after preflight but before its lock event, the
    # new coordinator can truthfully finish that transition because it holds
    # the exact same locked cores now.  This event is appended only after the
    # pair-root scan above has ruled out a possibly live incomplete worker.
    if active["phase"] == "preflight":
        if not host_lock_evidence or not all(
            isinstance(item, Mapping) for item in host_lock_evidence
        ):
            raise MeasurementError(
                "campaign recovery lacks current host-core-lock evidence"
            )
        synthetic_lock = _append_campaign_event(
            event_path,
            {
                "kind": "host-core-locks-acquired",
                "campaign_id": lock["campaign_id"],
                "campaign_lock_sha256": lock["record_sha256"],
                "recorded_at_utc": utc_now(),
                "resource_slots": lock["resource_slots"],
                "hardware_identity": dict(hardware_identity),
                "locks": [dict(item) for item in host_lock_evidence],
                "input_verification": dict(input_verification),
                "recovery_lock_context": {
                    "reacquired_for_interrupted_preflight": True,
                    "preflight_record_sha256": active[
                        "preflight_record_sha256"
                    ],
                },
            },
        )
        active["phase"] = "locked"
        active["core_locks_record_sha256"] = synthetic_lock[
            "record_sha256"
        ]
        active["core_locks_reacquired_for_recovery"] = True

    reason = (
        "coordinator-exited-after-durable-pair-commit"
        if active_pair_hashes or recovered_results
        else "coordinator-exited-before-campaign-terminal"
    )

    payload: dict[str, Any] = {
        "kind": "campaign-recovery-terminal",
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "recorded_at_utc": utc_now(),
        "reason": reason,
        "recovered_invocation": {
            "preflight_record_sha256": active["preflight_record_sha256"],
            "core_locks_record_sha256": active["core_locks_record_sha256"],
            "pair_terminal_record_sha256s": active_pair_hashes,
        },
        "recovered_pair_results": recovered_results,
        "input_verification": dict(input_verification),
        "hardware_identity": dict(hardware_identity),
    }
    _append_campaign_event(event_path, payload)
    return payload


def _archive_unfinished_pairs(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
) -> list[Path]:
    """Make interrupted, uncommitted pairs retryable in this campaign."""

    active, accounted = _campaign_events_for_recovery(
        results_root / "campaign_events.jsonl", lock
    )
    if active is not None:
        raise MeasurementError("cannot archive pairs during an open campaign invocation")
    pairs_root = results_root / "pairs"
    if not pairs_root.exists():
        return []
    if pairs_root.is_symlink() or not pairs_root.is_dir():
        raise MeasurementError("campaign pairs directory is invalid")
    archives: list[Path] = []
    for pair in _order_pairs(benchmark_root):
        pair_id = str(pair["pair_id"])
        root = pairs_root / pair_id
        if not root.exists() and not root.is_symlink():
            continue
        if _pair_record_valid(root, pair, lock):
            continue
        if pair_id in accounted:
            raise MeasurementError(
                f"a published failed pair cannot be silently replaced: {pair_id}"
            )
        archives.append(
            _archive_infrastructure_pair(
                results_root,
                lock,
                pair,
                reason="interrupted-before-durable-pair-terminal",
            )
        )
    return archives


@contextlib.contextmanager
def _exclusive_lock_file(path: Path, label: str) -> Iterable[dict[str, Any]]:
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    parent_status = path.parent.lstat()
    if (
        path.parent.is_symlink()
        or not stat.S_ISDIR(parent_status.st_mode)
        or parent_status.st_uid != os.getuid()
        or stat.S_IMODE(parent_status.st_mode) & 0o077
    ):
        raise MeasurementError(f"{label} directory is not private and user-owned")
    flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o600)
    try:
        status = os.fstat(descriptor)
        if (
            not stat.S_ISREG(status.st_mode)
            or status.st_uid != os.getuid()
            or stat.S_IMODE(status.st_mode) & 0o077
        ):
            raise MeasurementError(f"{label} file is not private and user-owned")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise MeasurementError(f"{label} is already held by another runner") from error
        evidence = {
            "kind": "highambench-exclusive-lock",
            "label": label,
            "path": str(path.resolve()),
            "device": status.st_dev,
            "inode": status.st_ino,
            "owner_uid": status.st_uid,
            "acquired": True,
        }
        yield evidence
    finally:
        with contextlib.suppress(OSError):
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _host_lock_root() -> Path:
    external = os.environ.get("HIGHAMBENCH_HOST_LOCK_ROOT")
    if external:
        candidate = Path(external)
        if not candidate.is_absolute() or candidate.is_symlink():
            raise MeasurementError("external host lock root must be an absolute real directory")
        try:
            if __package__:
                from .prepare_runtime import PreparationError, _secure_walk_directory
            else:  # pragma: no cover - direct execution
                from prepare_runtime import PreparationError, _secure_walk_directory  # type: ignore
            _secure_walk_directory(candidate, label="external host lock root", create=True)
        except (OSError, PreparationError) as error:
            raise MeasurementError(f"cannot create external host lock root: {error}") from error
        status = candidate.lstat()
        if (
            not stat.S_ISDIR(status.st_mode)
            or status.st_uid != os.getuid()
            or stat.S_IMODE(status.st_mode) != 0o700
        ):
            raise MeasurementError("external host lock root must be user-owned mode 0700")
        return candidate
    raw = os.environ.get("XDG_RUNTIME_DIR")
    if raw and Path(raw).is_absolute():
        candidate = Path(raw) / f"highambench-resource-locks-{os.getuid()}"
        try:
            candidate.mkdir(parents=True, exist_ok=True, mode=0o700)
        except OSError:
            pass
        else:
            return candidate
    return Path("/tmp") / f"highambench-resource-locks-{os.getuid()}"


@contextlib.contextmanager
def _host_core_locks(
    slots: Sequence[Mapping[str, Any]],
) -> Iterable[list[dict[str, Any]]]:
    identities: set[tuple[int, int, int]] = set()
    for slot in slots:
        cores = slot.get("cores")
        if not isinstance(cores, list):
            raise MeasurementError("resource slot lacks physical-core identities")
        for core in cores:
            if not isinstance(core, Mapping):
                raise MeasurementError("resource slot contains an invalid core")
            identity = (
                int(core["package_id"]),
                int(core["die_id"]),
                int(core["core_id"]),
            )
            if identity in identities:
                raise MeasurementError("campaign resource slots overlap physical cores")
            identities.add(identity)
    root = _host_lock_root()
    evidence: list[dict[str, Any]] = []
    with contextlib.ExitStack() as stack:
        for package_id, die_id, core_id in sorted(identities):
            lock_path = root / f"core-{package_id}-{die_id}-{core_id}.lock"
            record = stack.enter_context(
                _exclusive_lock_file(
                    lock_path,
                    f"physical core ({package_id}, {die_id}, {core_id})",
                )
            )
            record["physical_core"] = {
                "package_id": package_id,
                "die_id": die_id,
                "core_id": core_id,
            }
            evidence.append(record)
        yield evidence


def _run_campaign_locked(
    args: argparse.Namespace,
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
) -> int:
    verification = verify_campaign_inputs(
        benchmark_root, results_root, lock, deep_runtime=True
    )
    profile = lock.get("hardware_identity", {}).get("cpu_profile_id")
    jobs = lock.get("parallel_attempt_workers")
    if not isinstance(profile, str) or not isinstance(jobs, int):
        raise MeasurementError("campaign lock has invalid resource policy")
    # Do not derive this check from the coordinator's current affinity.  A
    # crashed prior coordinator may have left the authenticated partition
    # active, in which case the user session correctly sees only the host
    # complement until `_acquire_cpu_guard` performs owned-stale recovery.
    current_host, slots, identity = _locked_hardware_snapshot(lock)
    if len(slots) != jobs or any(
        slot.get("type_key") != profile for slot in slots
    ):
        raise MeasurementError("campaign lock has inconsistent parallel CPU slots")
    current_memory = current_host.get("memory")
    available = (
        current_memory.get("mem_available_bytes")
        if isinstance(current_memory, Mapping)
        else None
    )
    required_memory = jobs * HOST_MEMORY_ADMISSION_BYTES_PER_ATTEMPT
    if not isinstance(available, int) or available < required_memory:
        raise MeasurementError(
            "current available memory is below the point-in-time 17-GiB-per-attempt "
            "admission threshold (this check does not reserve physical memory)"
        )
    locked_slots = lock.get("resource_slots")
    if not isinstance(locked_slots, list) or slots != locked_slots:
        raise MeasurementError(
            "current exact CPU-slot allocation differs from the campaign lock"
        )
    event_path = results_root / "campaign_events.jsonl"
    # Lock contention is deliberately resolved before publishing a preflight.
    # Thus an unsuccessful competing coordinator cannot leave a half-open
    # invocation in the append-only audit stream.
    with _host_core_locks(slots) as host_lock_evidence:
        lease = _acquire_cpu_guard(results_root, lock, slots)
        lease_id = str(lease["lease_id"])
        release_attempted = False
        try:
            # The outer terminal is the durable pair commit point.  If the
            # previous coordinator died after sealing it but before appending
            # its advisory events, close that invocation before publishing
            # this run's preflight.  Both local locks and the kernel CPU lease
            # are held across recovery and the complete measured invocation.
            _recover_interrupted_campaign(
                benchmark_root,
                results_root,
                lock,
                input_verification=verification,
                hardware_identity=identity,
                host_lock_evidence=host_lock_evidence,
            )
            _seal_interrupted_incident_archives(benchmark_root, results_root, lock)
            _archive_unfinished_pairs(benchmark_root, results_root, lock)
            _append_campaign_event(
                event_path,
                {
                    "kind": "campaign-preflight",
                    "campaign_id": lock["campaign_id"],
                    "campaign_lock_sha256": lock["record_sha256"],
                    "recorded_at_utc": utc_now(),
                    "input_verification": verification,
                    "resource_slots": slots,
                    "hardware_identity": identity,
                    "cpu_guard_lease_id": lease_id,
                },
            )
            _append_campaign_event(
                event_path,
                {
                    "kind": "host-core-locks-acquired",
                    "campaign_id": lock["campaign_id"],
                    "campaign_lock_sha256": lock["record_sha256"],
                    "recorded_at_utc": utc_now(),
                    "resource_slots": slots,
                    "hardware_identity": identity,
                    "locks": host_lock_evidence,
                    "cpu_guard_lease": {
                        key: value
                        for key, value in lease.items()
                        if key != "lease_root"
                    },
                },
            )
            selected: list[dict[str, Any]] = []
            all_results: list[dict[str, Any]] = []
            returncode = 2
            final_verification: Mapping[str, Any] = verification
            final_identity: Mapping[str, Any] = identity
            terminal_error: dict[str, Any] | None = None
            pending_error: BaseException | None = None
            release_error: BaseException | None = None
            release_record: Mapping[str, Any] | None = None
            try:
                selected = _select_pairs(
                    benchmark_root, results_root, args.pair_id, lock=lock
                )
                if len(slots) != 1:
                    raise MeasurementError(
                        "measured-v6 requires exactly one authenticated provider slot"
                    )
                for pair in selected:
                    result: dict[str, Any] | None = None
                    for retry in range(4):
                        (_campaign_pairs_root(results_root) / str(pair["pair_id"])).mkdir(
                            parents=False, mode=0o700
                        )
                        pair_condition_results = [
                            _launch_condition(
                                benchmark_root,
                                results_root,
                                lock,
                                pair,
                                condition,
                                slots[0],
                                cpu_guard_lease_id=lease_id,
                            )
                            for condition in pair["condition_order"]
                        ]
                        if (
                            len(pair_condition_results) != 2
                            or {str(item.get("condition")) for item in pair_condition_results}
                            != {"N", "L"}
                        ):
                            raise MeasurementError(
                                f"campaign scheduler did not produce both conditions "
                                f"for {pair['pair_id']}"
                            )
                        result = _finalize_pair(
                            benchmark_root,
                            results_root,
                            lock,
                            pair,
                            pair_condition_results,
                        )
                        if result.get("complete") is True and result.get("returncode") == 0:
                            break
                        _archive_infrastructure_pair(
                            results_root,
                            lock,
                            pair,
                            reason=f"infrastructure-failure-retry-{retry + 1}",
                        )
                    if result is None or result.get("complete") is not True:
                        raise MeasurementError(
                            f"infrastructure failure persists after four fresh "
                            f"same-campaign attempts: {pair['pair_id']}"
                        )
                    try:
                        _append_campaign_event(
                            event_path,
                            {
                                "kind": "pair-terminal",
                                "campaign_id": lock["campaign_id"],
                                "campaign_lock_sha256": lock["record_sha256"],
                                "recorded_at_utc": utc_now(),
                                **result,
                            },
                        )
                    except BaseException as error:
                        raise _PairTerminalPublicationError(
                            f"could not publish pair terminal for "
                            f"{result.get('pair_id')}: {error}"
                        ) from error
                    all_results.append(result)
                selected_ids = [pair["pair_id"] for pair in selected]
                result_ids = [result.get("pair_id") for result in all_results]
                if (
                    any(not isinstance(pair_id, str) for pair_id in result_ids)
                    or len(result_ids) != len(set(result_ids))
                    or set(result_ids) != set(selected_ids)
                ):
                    raise MeasurementError(
                        "campaign finalization did not produce exact selected-pair "
                        "coverage"
                    )
                failed = [
                    result
                    for result in all_results
                    if result.get("returncode") != 0
                    or result.get("complete") is not True
                ]
                returncode = 1 if failed else 0
                final_verification = verify_campaign_inputs(
                    benchmark_root, results_root, lock, deep_runtime=True
                )
                final_identity = _verify_locked_hardware_identity(lock)
            except BaseException as error:
                pending_error = error
                terminal_error = {
                    "type": type(error).__name__,
                    "message": str(error),
                }
                returncode = 2

            release_attempted = True
            try:
                release_record = _release_cpu_guard(results_root, lease)
            except BaseException as error:
                release_error = error
                returncode = 2
                if terminal_error is None:
                    terminal_error = {
                        "type": type(error).__name__,
                        "message": str(error),
                    }

            if isinstance(pending_error, _PairTerminalPublicationError):
                if release_error is not None:
                    raise MeasurementError(
                        "pair-terminal publication failed and CPU-guard release "
                        f"also failed: publication={pending_error}; "
                        f"release={release_error}"
                    ) from release_error
                raise pending_error.with_traceback(pending_error.__traceback__)

            terminal_payload: dict[str, Any] = {
                "kind": "campaign-terminal",
                "campaign_id": lock["campaign_id"],
                "campaign_lock_sha256": lock["record_sha256"],
                "recorded_at_utc": utc_now(),
                "returncode": returncode,
                "selected_pair_ids": [pair["pair_id"] for pair in selected],
                "pair_results": sorted(
                    all_results, key=lambda result: str(result.get("pair_id"))
                ),
                "input_verification": final_verification,
                "hardware_identity": final_identity,
                "cpu_guard_lease_id": lease_id,
                "cpu_guard_release": release_record,
            }
            if terminal_error is not None:
                terminal_payload["error"] = terminal_error
            if release_error is not None and pending_error is not None:
                terminal_payload["cpu_guard_release_error"] = {
                    "type": type(release_error).__name__,
                    "message": str(release_error),
                }
            _append_campaign_event(event_path, terminal_payload)

            if pending_error is not None:
                raise pending_error.with_traceback(pending_error.__traceback__)
            if release_error is not None:
                raise release_error.with_traceback(release_error.__traceback__)
            if not selected:
                print("no pending pairs")
            return returncode
        finally:
            # Failures before the invocation's preflight/terminal sequence is
            # opened still must not leak a privileged CPU reservation.
            if not release_attempted:
                _release_cpu_guard(results_root, lease)


def run_campaign(args: argparse.Namespace) -> int:
    if not args.acknowledge_provider_use:
        raise MeasurementError(
            "campaign execution may make paid provider calls; pass "
            "--acknowledge-provider-use only for an authorized measurement"
    )
    benchmark_root = args.benchmark_root.resolve()
    results_root = _external_private_directory(
        args.results_root, "campaign results root", create=False
    )
    lock = _load_campaign(results_root)
    with _exclusive_lock_file(
        results_root / ".campaign-coordinator.lock",
        "campaign coordinator",
    ):
        return _run_campaign_locked(args, benchmark_root, results_root, lock)


def _condition_attempt_command(
    benchmark_root: Path,
    results_root: Path,
    lock: Mapping[str, Any],
    pair: Mapping[str, Any],
    condition: str,
    attempt_root: Path,
    resource_record: Path,
    condition_resource_record: Path,
) -> list[str]:
    run_ids = pair["run_ids"]
    order = pair["condition_order"]
    run_id = run_ids[order.index(condition)]
    runtime_snapshot = _artifact_path(results_root, lock["runtime_snapshot"])
    offline_shell = _artifact_path(results_root, lock["offline_shell"])
    agent = lock["agent"]
    command = [
        sys.executable,
        str(_script_path(benchmark_root, "run_attempt.py")),
        "--benchmark-root",
        str(benchmark_root),
        "--attempt-root",
        str(attempt_root),
        "--results-root",
        str(results_root),
        "--campaign-lock-sha256",
        str(lock["record_sha256"]),
        "--run-id",
        str(run_id),
        "--pair-id",
        str(pair["pair_id"]),
        "--task-id",
        str(pair["task_id"]),
        "--condition",
        condition,
        "--runtime-snapshot",
        str(runtime_snapshot),
        "--resource-record",
        str(resource_record),
        "--condition-resource-record",
        str(condition_resource_record),
        "--codex",
        str(agent["path"]),
        "--code-mode-host",
        str(agent["code_mode_host"]["path"]),
        "--auth-file",
        str(lock["auth"]["path"]),
        "--offline-shell",
        str(offline_shell),
        "--bwrap",
        str(lock["runtime_tools"]["bubblewrap"]["path"]),
        "--toolchain-root",
        str(lock["toolchain_root"]),
        "--shared-olean-root",
        str(Path(str(lock["shared_olean_root"])) / str(pair["task_id"]).split("-")[0]),
    ]
    if condition == "L":
        command.extend(
            [
                "--library-runtime-root",
                str(lock["numstability"]["checkout"]),
            ]
        )
    return command


def _resource_contract_identity(proof: Mapping[str, Any]) -> dict[str, Any]:
    expected = proof.get("expected")
    observed = proof.get("observed")
    if not isinstance(expected, Mapping) or not isinstance(observed, Mapping):
        raise MeasurementError("resource proof lacks expected/observed contract data")
    cgroup = observed.get("cgroup")
    files = observed.get("cgroup_files")
    cpu_partition = observed.get("cpu_partition")
    parent_cgroup = observed.get("pair_parent_cgroup")
    parent_controls = observed.get("pair_parent_memory_controls")
    campaign_partition = (
        cpu_partition.get("campaign_partition")
        if isinstance(cpu_partition, Mapping)
        else None
    )
    slot_partition = (
        cpu_partition.get("slot_partition")
        if isinstance(cpu_partition, Mapping)
        else None
    )
    service_cgroup = (
        cpu_partition.get("service_cgroup")
        if isinstance(cpu_partition, Mapping)
        else None
    )
    worker_cgroup = (
        cpu_partition.get("worker_cgroup")
        if isinstance(cpu_partition, Mapping)
        else None
    )
    if (
        not isinstance(cgroup, Mapping)
        or not isinstance(files, Mapping)
        or not isinstance(cpu_partition, Mapping)
        or not isinstance(campaign_partition, Mapping)
        or not isinstance(slot_partition, Mapping)
        or not isinstance(service_cgroup, Mapping)
        or not isinstance(worker_cgroup, Mapping)
        or not isinstance(parent_cgroup, Mapping)
        or not isinstance(parent_controls, Mapping)
    ):
        raise MeasurementError(
            "resource proof lacks cgroup, CPU-partition, or memory identity"
        )
    return {
        "expected": dict(expected),
        "sched_getaffinity": observed.get("sched_getaffinity"),
        "sched_setaffinity_probe": observed.get("sched_setaffinity_probe"),
        "cgroup": {
            key: cgroup.get(key)
            for key in (
                "membership_path",
                "mount_root",
                "mount_point",
                "directory",
            )
        },
        "cgroup_limits": {
            key: files.get(key)
            for key in (
                "memory.max",
                "memory.high",
                "memory.swap.max",
                "memory.oom.group",
            )
        },
        "cpu_partition": {
            "verified": cpu_partition.get("verified"),
            "mode": cpu_partition.get("mode"),
            "campaign_partition": dict(campaign_partition),
            "slot_partition": dict(slot_partition),
            "service_cgroup": dict(service_cgroup),
            "worker_cgroup": dict(worker_cgroup),
            "service_cpuset_cpus_effective": cpu_partition.get(
                "service_cpuset_cpus_effective"
            ),
            "service_cpuset_cpus_effective_parsed": cpu_partition.get(
                "service_cpuset_cpus_effective_parsed"
            ),
        },
        "pair_parent_cgroup": {
            key: parent_cgroup.get(key)
            for key in ("directory", "device", "inode")
        },
        "pair_parent_memory_controls": dict(parent_controls),
    }


def run_condition_worker(args: argparse.Namespace) -> int:
    benchmark_root = args.benchmark_root.resolve()
    results_root = _external_private_directory(
        args.results_root, "campaign results root", create=False
    )
    lock = _load_campaign(results_root)
    verification_before = verify_campaign_inputs(
        benchmark_root, results_root, lock
    )
    hardware_verification_before = _verify_locked_hardware_identity(lock)
    pairs = {pair["pair_id"]: pair for pair in _order_pairs(benchmark_root)}
    pair = pairs.get(args.pair_id)
    condition = args.condition
    if pair is None or condition not in ("N", "L"):
        raise MeasurementError(
            f"attempt is not in the canonical campaign order: {args.pair_id}-{condition}"
        )
    pair_root = _campaign_pair_root(results_root, args.pair_id)
    slot = read_object(args.slot_file.resolve())
    locked_slots = lock.get("resource_slots")
    if not isinstance(locked_slots, list) or slot not in locked_slots:
        raise MeasurementError(
            "condition worker slot is not one of the campaign-locked slots"
        )
    kernel_proof = resources.verify_current_worker(
        slot, expected_memory_bytes=MANAGER_MEMORY_BYTES
    )
    proof_path = pair_root / f"resource_kernel_proof_{condition}.json"
    if not proof_path.is_file():
        raise MeasurementError("resource wrapper did not publish its kernel proof")
    wrapper_proof = read_object(proof_path)
    if _resource_contract_identity(wrapper_proof) != _resource_contract_identity(
        kernel_proof
    ):
        raise MeasurementError("resource wrapper/worker kernel contracts differ")
    worker_proof_path = pair_root / f"resource_worker_proof_{condition}.json"
    atomic_write_json(worker_proof_path, kernel_proof, mode=0o444)
    resource_record = pair_root / f"resource_record_{condition}.json"
    resource_value = {
        "schema_version": 2,
        "kind": "highambench-attempt-resource",
        "pair_id": args.pair_id,
        "condition": condition,
        "slot": slot,
        "kernel_proof_before_exec": wrapper_proof,
        "kernel_proof_at_attempt_worker_start": kernel_proof,
        "campaign_hardware_identity": lock["hardware_identity"],
        "started_at_utc": utc_now(),
    }
    resource_value["record_sha256"] = canonical_digest(resource_value)
    atomic_write_json(resource_record, resource_value, mode=0o444)

    condition_scope = resources.begin_fresh_condition_cgroup(slot, condition)
    scope_begin_path = pair_root / f"condition_cgroup_begin_{condition}.json"
    atomic_write_json(scope_begin_path, condition_scope.begin_evidence, mode=0o444)
    entry_proof_path = pair_root / f"condition_cgroup_entry_{condition}.json"
    attempt_root = pair_root / f"condition-{condition}"
    attempt_command = _condition_attempt_command(
        benchmark_root,
        results_root,
        lock,
        pair,
        condition,
        attempt_root,
        resource_record,
        scope_begin_path,
    )
    command = condition_scope.wrap_command(
        attempt_command,
        proof_file=entry_proof_path,
    )
    command_log = pair_root / f"condition-{condition}.command.json"
    atomic_write_json(
        command_log,
        {
            "kind": "highambench-condition-command",
            "condition": condition,
            "condition_argv": attempt_command,
            "cgroup_entry_argv": command,
            "started_at_utc": utc_now(),
        },
    )
    process_log = pair_root / f"condition-{condition}.process.log"
    try:
        with process_log.open("wb") as log:
            completed = subprocess.run(
                command,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
        scope_finish = condition_scope.finish()
    finally:
        condition_scope.close()
    scope_finish_path = pair_root / f"condition_cgroup_finish_{condition}.json"
    atomic_write_json(scope_finish_path, scope_finish, mode=0o444)
    if not entry_proof_path.is_file():
        raise MeasurementError(
            f"condition {condition} did not publish its cgroup-entry proof"
        )
    attempt_json = attempt_root / "attempt.json"
    attempt = {
        "condition": condition,
        "returncode": completed.returncode,
        "record": (
            artifact(attempt_json, relative_to=pair_root)
            if attempt_json.is_file()
            else None
        ),
        "process_log": artifact(process_log, relative_to=pair_root),
        "command": artifact(command_log, relative_to=pair_root),
        "condition_resource": artifact(scope_begin_path, relative_to=pair_root),
        "condition_entry_proof": artifact(entry_proof_path, relative_to=pair_root),
    }
    sample_value = resources.verify_current_worker(
        slot, expected_memory_bytes=MANAGER_MEMORY_BYTES
    )
    sample_path = pair_root / f"resource_after_{condition}.json"
    atomic_write_json(sample_path, sample_value, mode=0o444)
    resource_sample = {
        "after_condition": condition,
        "condition_cgroup_begin": artifact(
            scope_begin_path, relative_to=pair_root
        ),
        "condition_cgroup_entry_proof": artifact(
            entry_proof_path, relative_to=pair_root
        ),
        "condition_cgroup_finish": artifact(
            scope_finish_path, relative_to=pair_root
        ),
        "manager_after_condition": artifact(sample_path, relative_to=pair_root),
    }
    complete = bool(
        completed.returncode in (0, 1)
        and attempt_json.is_file()
        and _attempt_terminal_valid(
            attempt_json,
            pair_root,
            pair,
            condition,
            lock,
            completed.returncode,
            resource_record_path=resource_record,
        )
    )
    verification_after = verify_campaign_inputs(
        benchmark_root, results_root, lock
    )
    hardware_verification_after = _verify_locked_hardware_identity(lock)
    worker_record: dict[str, Any] = {
        "schema_version": 1,
        "kind": "highambench-condition-worker-result",
        "pair_id": pair["pair_id"],
        "task_id": pair["task_id"],
        "repetition_id": pair["repetition_id"],
        "condition": condition,
        "complete": complete,
        "infrastructure_failure": not complete,
        "attempt": attempt,
        "resource": artifact(resource_record, relative_to=pair_root),
        "resource_proof": artifact(proof_path, relative_to=pair_root),
        "resource_worker_proof": artifact(
            worker_proof_path, relative_to=pair_root
        ),
        "resource_sample": resource_sample,
        "campaign_id": lock["campaign_id"],
        "campaign_lock_sha256": lock["record_sha256"],
        "corpus_verification_before": verification_before,
        "corpus_verification_after": verification_after,
        "hardware_verification_before": hardware_verification_before,
        "hardware_verification_after": hardware_verification_after,
        "finished_at_utc": utc_now(),
    }
    worker_record["record_sha256"] = canonical_digest(worker_record)
    atomic_write_json(
        pair_root / f"condition-{condition}.worker.json",
        worker_record,
        mode=0o444,
    )
    return 0 if complete else 2


def show_inventory(_args: argparse.Namespace) -> int:
    host = resources.inventory_host()
    host["resource_slots"] = resources.allocate_slots(host)
    print(json.dumps(host, indent=2, sort_keys=True))
    return 0


def status(args: argparse.Namespace) -> int:
    benchmark_root = args.benchmark_root.resolve()
    results_root = _external_private_directory(
        args.results_root, "campaign results root", create=False
    )
    lock = _load_campaign(results_root)
    verification = verify_campaign_inputs(benchmark_root, results_root, lock)
    pairs_root = _campaign_pairs_root(results_root)
    pairs = _order_pairs(benchmark_root)
    complete = sum(
        _pair_record_valid(
            pairs_root / pair["pair_id"], pair, lock
        )
        for pair in pairs
    )
    print(
        json.dumps(
            {
                "campaign_id": lock["campaign_id"],
                "inputs": verification,
                "complete_pairs": complete,
                "total_pairs": len(pairs),
                "complete_attempts": complete * 2,
                "total_attempts": len(pairs) * 2,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parents[1]
    parser.add_argument("--benchmark-root", type=Path, default=here)
    subparsers = parser.add_subparsers(dest="action", required=True)

    subparsers.add_parser("inventory")

    create = subparsers.add_parser("create")
    create.add_argument("--results-root", type=Path, required=True)
    create.add_argument(
        "--runtime-cache-root",
        type=Path,
        required=True,
        help="existing external directory holding the persistent runtime cache",
    )
    create.add_argument(
        "--reuse-runtime-snapshot",
        type=Path,
        help="reuse an existing immutable runtime after a full integrity check",
    )
    create.add_argument("--codex", type=Path, required=True)
    create.add_argument("--auth-file", type=Path, required=True)
    create.add_argument("--toolchain-root", type=Path, required=True)
    create.add_argument(
        "--jobs",
        type=int,
        choices=(1,),
        default=1,
        help="measured-v6 permits one provider-active attempt per authentication",
    )
    create.add_argument("--core-profile")
    create.add_argument(
        "--slot-offset",
        type=int,
        default=0,
        help="select a later homogeneous four-core slot when the default slot is busy",
    )
    create.add_argument("--acknowledge-environment-lock", action="store_true")

    campaign = subparsers.add_parser("campaign")
    campaign.add_argument("--results-root", type=Path, required=True)
    campaign.add_argument("--pair-id", action="append", default=[])
    campaign.add_argument("--acknowledge-provider-use", action="store_true")

    status_parser = subparsers.add_parser("status")
    status_parser.add_argument("--results-root", type=Path, required=True)

    condition_internal = subparsers.add_parser(
        "_run-condition", help=argparse.SUPPRESS
    )
    condition_internal.add_argument("--results-root", type=Path, required=True)
    condition_internal.add_argument("--pair-id", required=True)
    condition_internal.add_argument("--condition", choices=("N", "L"), required=True)
    condition_internal.add_argument("--slot-file", type=Path, required=True)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        if args.action == "inventory":
            return show_inventory(args)
        if args.action == "create":
            return create_campaign(args)
        if args.action == "campaign":
            return run_campaign(args)
        if args.action == "status":
            return status(args)
        if args.action == "_run-condition":
            return run_condition_worker(args)
        raise MeasurementError(f"unsupported action: {args.action}")
    except (MeasurementError, resources.ResourceIsolationError, OSError, ValueError) as error:
        print(f"run-benchmark error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
