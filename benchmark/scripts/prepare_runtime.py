#!/usr/bin/env python3
"""Prepare an immutable, external NumStability runtime for VSCLReuse.

This command uses the exact Higham commit recorded for the paper. It records
that immutable commit, builds only an independently cloned
derived tree, and downloads and authenticates every locked source and binary
input before the first Lake process. Lake is always offline. The preparer then
creates pristine detached NumStability and Mathlib source checkouts from the
private prefetch stores only after every Lake command has finished. The
pristine checkouts are sealed read-only and emitted separately from all derived
packages and build products. Neither pristine source checkout is editable.

The command deliberately never updates, patches, vendors, or copies
NumStability or mathlib into the benchmark repository.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import stat
import subprocess
import sys
import tarfile
import time
try:
    import tomllib
except ModuleNotFoundError:  # Python 3.10 project virtual environments.
    import tomli as tomllib  # type: ignore[no-redef]
import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence
from urllib.parse import unquote, urlsplit, urlunsplit

try:
    from . import host_limits
except ImportError:
    import host_limits


SCHEMA_VERSION = 3
# Format 12 additionally compiles the seven paper-required modules outside
# NumStability.All. An older root-only build is incomplete for the active
# benchmark corpus and must not be reused.
CACHE_FORMAT_VERSION = 12
NUMSTABILITY_REPOSITORY = (
    "https://github.com/AlexGeorgantzas/lean-numerical-stability.git"
)
NUMSTABILITY_REF = "38228c607d62e9485b4fa1fc668cc3cb2857857e"
LIBRARY_LOOKUP = Path("docs/LIBRARY_LOOKUP.md")
LIBRARY_LOOKUP_CHECK = Path("docs/LibraryLookupChecks.lean")
PAPER_REQUIRED_LIBRARY_MODULES = (
    "NumStability.Algorithms.Horner",
    "NumStability.Algorithms.IterativeRefinement",
    "NumStability.Algorithms.QR.GivensSpec",
    "NumStability.Algorithms.QR.HouseholderApply",
    "NumStability.Algorithms.QR.HouseholderQR",
    "NumStability.Analysis.FloatingPointArithmetic",
    "NumStability.Analysis.RoundingProductBounds",
)


def verify_paper_required_library_modules(build_checkout: Path) -> None:
    compiled_root = build_checkout / ".lake" / "build" / "lib" / "lean"
    for module in PAPER_REQUIRED_LIBRARY_MODULES:
        object_file = compiled_root / (module.replace(".", "/") + ".olean")
        if object_file.is_symlink() or not object_file.is_file():
            raise PreparationError(
                f"paper-required NumStability module was not compiled: {module}"
            )


COMMIT_RE = re.compile(r"^[0-9a-f]{40}(?:[0-9a-f]{24})?$")
FLOATING_REVISIONS = frozenset(
    {"head", "main", "master", "stable", "nightly", "latest", "develop"}
)
MATHLIB_CACHE_BASE_URL = "https://lakecache.blob.core.windows.net/mathlib4"
SUPPORTED_MATHLIB_COMMIT = "e8ea1afc32790ce1d4e1a4e45cc412ba9388716b"
MATHLIB_COMMIT_MANIFEST_SHA256 = (
    "2ff9a9c943dc1c6f8df203135f7de550555235f7c535c9be3322b072c2f9e0ae"
)
MATHLIB_COMMIT_MANIFEST_BYTES = 163_719
MATHLIB_COMMIT_MANIFEST_RELATIVE_PATH = (
    "scripts/mathlib_cache_commit_manifest.txt"
)
MATHLIB_COMMIT_MANIFEST_PATH = Path(__file__).with_name(
    "mathlib_cache_commit_manifest.txt"
)
MATHLIB_CACHE_FILENAME_SET_SHA256 = (
    "664cb1e03a33504b6f333678859396a1d9ae7de0405811f3884ff92f1f65b1f3"
)
MATHLIB_CACHE_ARTIFACT_COUNT = 8_033
MATHLIB_CACHE_ARTIFACT_BYTES = 393_376_909
MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256 = (
    "7b56da3bb98c5dc8ed297cfb72048cc308c7245f7bef217f71050da9ab891973"
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
SUPPORTED_PROOFWIDGETS_COMMIT = "212dc300449e436298804f09b264f624667106f8"
PROOFWIDGETS_RELEASE_URL = (
    "https://github.com/leanprover-community/ProofWidgets4/releases/download/"
    "v0.0.90/ProofWidgets4.tar.gz"
)
PROOFWIDGETS_RELEASE_SHA256 = (
    "a6dc87b48d55b3507ccbe73248fc9762421c862bcf214e0cf16509dea376e0d5"
)
PROOFWIDGETS_RELEASE_BYTES = 13_616_644
LEANTAR_VERSION = "0.1.16"
LEANTAR_ARCHIVE_SHA256 = (
    "2cbc40ca214227a0e536721c021bad719a802dd86b1f2d8989571efafbfbd3d1"
)
LEANTAR_BINARY_SHA256 = (
    "08546cc20f71916656df14ee0dee03e908530f7370ebfaaf276f3d8e8c548d9f"
)
SUPPORTED_LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc3"
LEAN_TOOLCHAIN_ARCHIVE_URL = (
    "https://releases.lean-lang.org/lean4/v4.29.0-rc3/"
    "lean-4.29.0-rc3-linux.tar.zst"
)
LEAN_TOOLCHAIN_ARCHIVE_ROOT = "lean-4.29.0-rc3-linux"
LEAN_TOOLCHAIN_ARCHIVE_BYTES = 537_223_656
LEAN_TOOLCHAIN_ARCHIVE_SHA256 = (
    "6a8de92790c716de3083c4b5828f1dcc1c83f4cd9770b3dad7ad5c7c22db6012"
)
LEAN_TOOLCHAIN_INTEGRITY = {
    "algorithm": "sha256-complete-tree-v2-with-link-count",
    "digest": "a59ea7e8f02b0d8d2c441df5b8e97e679ed4e7f1d53f5742b855f4da8b22f979",
    "regular_files": 13_334,
    "directories": 533,
    "symlinks": 12,
    "regular_file_bytes": 2_791_170_725,
    "git_administrative_directories_included": True,
}
LEAN_TOOLCHAIN_LAKE_SHA256 = (
    "a608ff084d7e2af228b92a29d7c2fd083ba0580e46889175ec74a81678c98359"
)
LEAN_TOOLCHAIN_LEAN_SHA256 = (
    "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
)
MAX_LEAN_TOOLCHAIN_TAR_BYTES = 4 * 1024 * 1024 * 1024
MAX_CACHE_ARTIFACTS = 20_000
MAX_CACHE_ARTIFACT_BYTES = 512 * 1024 * 1024
MAX_CACHE_TOTAL_BYTES = 8 * 1024 * 1024 * 1024


class PreparationError(RuntimeError):
    """A preparation invariant was not satisfied."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode(
        "utf-8"
    )


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def display_repository(repository: str) -> str:
    """Return a manifest-safe URL and reject embedded HTTP credentials."""

    parts = urlsplit(repository)
    if parts.scheme in {"http", "https"} and (parts.username or parts.password):
        raise PreparationError("repository URLs with embedded credentials are forbidden")
    if parts.scheme in {"http", "https"}:
        return urlunsplit((parts.scheme, parts.hostname or "", parts.path, "", ""))
    return repository


def is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def absolute_without_resolving(path: Path) -> Path:
    return Path(os.path.abspath(os.fspath(path.expanduser())))


def _nearest_real_directory(path: Path, label: str) -> Path:
    cursor = Path(path.anchor)
    nearest = cursor
    for component in path.parts[1:]:
        cursor /= component
        try:
            metadata = cursor.lstat()
        except FileNotFoundError:
            return nearest
        except OSError as error:
            raise PreparationError(
                f"cannot inspect {label} path component: {cursor}"
            ) from error
        if stat.S_ISLNK(metadata.st_mode):
            raise PreparationError(
                f"{label} contains a symlink component: {cursor}"
            )
        if not stat.S_ISDIR(metadata.st_mode):
            raise PreparationError(
                f"{label} contains a non-directory component: {cursor}"
            )
        nearest = cursor
    return nearest


def _assert_directory_edge_not_replaceable(
    parent: os.stat_result,
    child: os.stat_result,
    *,
    label: str,
    child_path: Path,
) -> None:
    """Reject ancestry another OS user could rename during preparation."""

    if not parent.st_mode & (stat.S_IWGRP | stat.S_IWOTH):
        return
    trusted_owners = {0, os.getuid()}
    if (
        parent.st_mode & stat.S_ISVTX
        and child.st_uid in trusted_owners
    ):
        return
    raise PreparationError(
        f"{label} must have private, user-owned ancestry; a directory entry is "
        f"replaceable by another user: {child_path}"
    )


def _secure_walk_directory(
    path: Path, *, label: str, create: bool
) -> Path:
    """Walk/create an absolute directory with pinned, no-symlink dirfds.

    If ``create`` is false, return the nearest existing directory.  Every
    traversed entry is protected against renames by a different OS user; races
    by the current UID are outside the boundary because that UID can already
    chmod and modify the private cache directly.
    """

    if not path.is_absolute() or path.anchor != os.sep:
        raise PreparationError(f"{label} must be an absolute POSIX path")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
    current_path = Path(path.anchor)
    try:
        current_fd = os.open(path.anchor, flags)
    except OSError as error:
        raise PreparationError(f"cannot open filesystem root for {label}") from error
    current_metadata = os.fstat(current_fd)
    try:
        for component in path.parts[1:]:
            child_path = current_path / component
            created = False
            try:
                child_fd = os.open(component, flags, dir_fd=current_fd)
            except FileNotFoundError:
                if not create:
                    return current_path
                try:
                    os.mkdir(component, mode=0o700, dir_fd=current_fd)
                    created = True
                except FileExistsError:
                    pass
                except OSError as error:
                    raise PreparationError(
                        f"cannot create {label} component: {child_path}"
                    ) from error
                try:
                    child_fd = os.open(component, flags, dir_fd=current_fd)
                except OSError as error:
                    raise PreparationError(
                        f"{label} component was replaced during creation: {child_path}"
                    ) from error
            except OSError as error:
                raise PreparationError(
                    f"{label} contains a symlink component or non-directory: "
                    f"{child_path}"
                ) from error
            child_metadata = os.fstat(child_fd)
            try:
                _assert_directory_edge_not_replaceable(
                    current_metadata,
                    child_metadata,
                    label=label,
                    child_path=child_path,
                )
                if created:
                    os.fchmod(child_fd, 0o700)
                    child_metadata = os.fstat(child_fd)
            except BaseException:
                os.close(child_fd)
                raise
            os.close(current_fd)
            current_fd = child_fd
            current_metadata = child_metadata
            current_path = child_path

        try:
            pathname_metadata = os.stat(path, follow_symlinks=False)
        except OSError as error:
            raise PreparationError(f"cannot revalidate {label}: {path}") from error
        if (
            pathname_metadata.st_dev != current_metadata.st_dev
            or pathname_metadata.st_ino != current_metadata.st_ino
        ):
            raise PreparationError(f"{label} changed during directory validation")
        return current_path
    finally:
        os.close(current_fd)


def _reject_git_worktree(directory: Path, label: str, git_bin: Path) -> None:
    environment = command_environment()
    environment["GIT_DISCOVERY_ACROSS_FILESYSTEM"] = "1"
    completed = subprocess.run(
        [os.fspath(git_bin), "-C", os.fspath(directory), "rev-parse", "--show-toplevel"],
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
        check=False,
    )
    if completed.returncode == 0:
        worktree = completed.stdout.strip()
        raise PreparationError(
            f"{label} must be outside every Git worktree; found {worktree or 'unknown'}"
        )
    if "not a git repository" not in completed.stderr.lower():
        raise PreparationError(
            f"cannot prove {label} is outside every Git worktree: "
            f"{completed.stderr.strip()}"
        )


def require_external_private_directory(
    raw: Path, *, label: str, git_bin: Path, create: bool
) -> Path:
    """Require a real private directory outside every Git worktree."""

    expanded = raw.expanduser()
    if ".." in expanded.parts:
        raise PreparationError(f"{label} must not contain '..' path components")
    path = absolute_without_resolving(expanded)
    nearest = _secure_walk_directory(path, label=label, create=False)
    _reject_git_worktree(nearest, label, git_bin)
    if create:
        completed = _secure_walk_directory(path, label=label, create=True)
        if completed != path:
            raise PreparationError(f"unable to create {label}: {path}")
    elif nearest != path:
        raise PreparationError(f"{label} does not exist: {path}")
    if _secure_walk_directory(path, label=label, create=False) != path:
        raise PreparationError(f"{label} is not an existing directory: {path}")
    _reject_git_worktree(path, label, git_bin)
    metadata = path.lstat()
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != os.getuid()
        or stat.S_IMODE(metadata.st_mode) != 0o700
    ):
        raise PreparationError(
            f"{label} must be a real, user-owned directory with exact mode 0700"
        )
    return path


def require_external_local_mirror(
    repository: str, repository_root: Path
) -> Path | None:
    """If a local test/audited mirror is used, require it to be external too."""

    parts = urlsplit(repository)
    local: Path | None = None
    if parts.scheme == "file":
        local = Path(unquote(parts.path))
    elif parts.scheme == "" and Path(repository).expanduser().exists():
        local = Path(repository)
    if local is None:
        return None
    lexical_local = absolute_without_resolving(local)
    if _secure_walk_directory(
        lexical_local, label="local repository mirror", create=False
    ) != lexical_local:
        raise PreparationError("local repository mirror is not a real directory")
    lexical_repo = absolute_without_resolving(repository_root)
    resolved_local = lexical_local.resolve(strict=True)
    resolved_repo = lexical_repo.resolve(strict=True)
    if (
        is_within(lexical_local, lexical_repo)
        or is_within(lexical_repo, lexical_local)
        or is_within(resolved_local, resolved_repo)
        or is_within(resolved_repo, resolved_local)
    ):
        raise PreparationError(
            "a local NumStability mirror must be external to the benchmark repository"
        )
    return resolved_local


def local_repository_path(repository: object) -> Path | None:
    """Resolve a local/file repository URL for an explicit read-only mount."""

    if not isinstance(repository, str):
        return None
    parts = urlsplit(repository)
    if parts.scheme == "file":
        if parts.netloc not in {"", "localhost"}:
            raise PreparationError("file repository URL must not name a remote host")
        candidate = Path(unquote(parts.path))
    elif parts.scheme == "" and Path(repository).expanduser().exists():
        candidate = Path(repository).expanduser()
    else:
        return None
    try:
        return candidate.resolve(strict=True)
    except OSError as error:
        raise PreparationError(f"local repository does not exist: {candidate}") from error


def validate_repository_transport(repository: object, *, label: str) -> Path | None:
    """Allow only HTTPS or an existing operator-visible local Git repository."""

    if not isinstance(repository, str) or not repository:
        raise PreparationError(f"{label} repository URL is invalid")
    local = local_repository_path(repository)
    if local is not None:
        return local
    parts = urlsplit(repository)
    if (
        parts.scheme != "https"
        or not parts.hostname
        or parts.username is not None
        or parts.password is not None
        or parts.query
        or parts.fragment
    ):
        raise PreparationError(
            f"{label} repository must use credential-free HTTPS or an explicitly "
            "validated local path"
        )
    return None


def git_transport_repository(repository: str) -> str:
    """Force local mirrors through Git's copy transport, never inode sharing."""

    local = local_repository_path(repository)
    return local.as_uri() if local is not None else repository


def authorize_prefetch_sources(
    repository: str,
    pins: Mapping[str, Any],
    explicit_local_dependency_mirrors: Sequence[Path],
) -> tuple[Path, ...]:
    """Validate local repositories that trusted host-side Git may prefetch."""

    authorized_dependencies = {
        mirror.resolve(strict=True) for mirror in explicit_local_dependency_mirrors
    }
    repositories: list[tuple[str, object, bool]] = [
        ("NumStability source mirror", repository, True)
    ]
    dependencies = pins.get("dependencies")
    if not isinstance(dependencies, list):
        raise PreparationError("upstream dependency pin list is invalid")
    repositories.extend(
        (
            f"dependency {dependency.get('name', '<unknown>')}",
            dependency.get("repository"),
            False,
        )
        for dependency in dependencies
        if isinstance(dependency, Mapping)
    )
    local_sources: set[Path] = set()
    for label, candidate, is_primary in repositories:
        local = validate_repository_transport(candidate, label=label)
        if local is None:
            continue
        if not is_primary and local not in authorized_dependencies:
            raise PreparationError(
                f"{label} is a local path not authorized by "
                "--local-dependency-mirror"
            )
        assert_no_special_files(local, label=label)
        assert_nonexecuting_git_config(local, label=label)
        local_sources.add(local)
    unused = authorized_dependencies - local_sources
    if unused:
        raise PreparationError(
            "explicit local dependency mirror is not named by the locked manifest: "
            + ", ".join(sorted(map(os.fspath, unused)))
        )
    return tuple(sorted(local_sources, key=os.fspath))


@dataclass(frozen=True)
class CommandRecord:
    argv: tuple[str, ...]
    cwd: str | None
    started_at: str
    finished_at: str
    duration_seconds: float
    returncode: int
    stdout: str
    stderr: str
    file_size_limit_bytes: int | None = None
    role: str = "command"
    orchestration_id: str | None = None
    timed_out: bool = False

    def as_json(self) -> dict[str, Any]:
        return {
            "argv": list(self.argv),
            "cwd": self.cwd,
            "started_at": self.started_at,
            "finished_at": self.finished_at,
            "duration_seconds": self.duration_seconds,
            "returncode": self.returncode,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "role": self.role,
            "orchestration_id": self.orchestration_id,
            "timed_out": self.timed_out,
            "file_size_limit_bytes": self.file_size_limit_bytes,
            "stdout_sha256": sha256_bytes(self.stdout.encode("utf-8")),
            "stderr_sha256": sha256_bytes(self.stderr.encode("utf-8")),
        }


def run_command(
    argv: Sequence[str],
    *,
    cwd: Path | None = None,
    timeout: float | None = None,
    recorder: list[CommandRecord] | None = None,
    file_size_limit_bytes: int | None = None,
) -> subprocess.CompletedProcess[str]:
    started_at = utc_now()
    before = time.monotonic()
    environment = command_environment()
    if file_size_limit_bytes is not None and file_size_limit_bytes <= 0:
        raise PreparationError("command file-size limit must be positive")

    def apply_file_size_limit() -> None:
        if file_size_limit_bytes is not None:
            resource.setrlimit(
                resource.RLIMIT_FSIZE,
                (file_size_limit_bytes, file_size_limit_bytes),
            )
    try:
        result = subprocess.run(
            [os.fspath(part) for part in argv],
            cwd=os.fspath(cwd) if cwd is not None else None,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
            preexec_fn=(
                apply_file_size_limit if file_size_limit_bytes is not None else None
            ),
        )
    except FileNotFoundError as error:
        raise PreparationError(f"required executable not found: {argv[0]}") from error
    except subprocess.TimeoutExpired as error:
        raise PreparationError(
            f"command timed out after {timeout} seconds: {' '.join(argv)}"
        ) from error
    duration = time.monotonic() - before
    record = CommandRecord(
        argv=tuple(str(part) for part in argv),
        cwd=os.fspath(cwd.resolve()) if cwd is not None else None,
        started_at=started_at,
        finished_at=utc_now(),
        duration_seconds=duration,
        returncode=result.returncode,
        stdout=result.stdout,
        stderr=result.stderr,
        file_size_limit_bytes=file_size_limit_bytes,
    )
    if recorder is not None:
        recorder.append(record)
    if result.returncode != 0:
        stdout = result.stdout[-4000:]
        stderr = result.stderr[-4000:]
        raise PreparationError(
            f"command failed ({result.returncode}): {' '.join(argv)}\n"
            f"stdout:\n{stdout}\nstderr:\n{stderr}"
        )
    return result


def command_environment() -> dict[str, str]:
    """Return a minimal environment for trusted host-side subprocesses."""

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
            # Verification must neither execute nor inherit host Git policy.
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


def locate_executable(value: str) -> Path:
    candidate = shutil.which(value)
    if candidate is None:
        raise PreparationError(f"required executable not found: {value}")
    return Path(candidate).resolve()


PREPARATION_ISOLATION = {
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


def create_lake_sandbox_directory(checkout: Path) -> Path:
    """Create private scratch space strictly inside the derived checkout."""

    lake_directory = checkout / ".lake"
    if lake_directory.exists() or lake_directory.is_symlink():
        metadata = lake_directory.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
            raise PreparationError("derived .lake path is not a real directory")
    else:
        lake_directory.mkdir(mode=0o700)
    sandbox = lake_directory / ".highambench-preparation-sandbox"
    if sandbox.exists() or sandbox.is_symlink():
        raise PreparationError("derived Lake sandbox scratch path already exists")
    sandbox.mkdir(mode=0o700)
    for name in ("home", "tmp", "cache", "config", "etc"):
        (sandbox / name).mkdir(mode=0o700)
    synthetic_files = {
        "resolv.conf": "# Lake preparation is intentionally offline.\n",
        "hosts": "127.0.0.1 localhost\n::1 localhost\n",
        "nsswitch.conf": "hosts: files\n",
        "passwd": "root:x:0:0:VSCLReuse:/nonexistent:/usr/sbin/nologin\n",
        "group": "root:x:0:\n",
    }
    for name, content in synthetic_files.items():
        path = sandbox / "etc" / name
        path.write_text(content, encoding="utf-8")
        path.chmod(0o444)
    return sandbox.resolve(strict=True)


def remove_lake_sandbox_directory(sandbox: Path) -> None:
    """Remove scratch state from the disposable derived checkout."""

    if sandbox.is_symlink():
        sandbox.unlink()
    elif sandbox.exists():
        make_owner_writable(sandbox)
        shutil.rmtree(sandbox)


def sandboxed_lake_command(
    *,
    checkout: Path,
    sandbox: Path,
    unshare_bin: Path,
    bwrap_bin: Path,
    lake_bin: Path,
    lake_arguments: Sequence[str],
    read_only_checkout_git_directories: Sequence[Path],
    read_only_inputs: Sequence[Path] = (),
) -> list[str]:
    """Return the exact capability-limited command for one Lake invocation."""

    checkout = checkout.resolve(strict=True)
    sandbox = sandbox.resolve(strict=True)
    try:
        sandbox.relative_to(checkout)
    except ValueError as error:
        raise PreparationError("Lake sandbox scratch path escapes derived build") from error
    search_path = ":".join(
        dict.fromkeys(
            [
                os.fspath(lake_bin.parent),
                "/usr/local/bin",
                "/usr/bin",
                "/bin",
            ]
        )
    )
    command = [
        os.fspath(unshare_bin),
        "--user",
        "--map-root-user",
        "--net",
        "--",
        os.fspath(bwrap_bin),
        "--unshare-all",
        "--unshare-user",
        # Bubblewrap inherits the already-private namespace created above.
        "--share-net",
        "--disable-userns",
        "--assert-userns-disabled",
        "--die-with-parent",
        "--new-session",
        "--cap-drop",
        "ALL",
        # Start from Bubblewrap's empty root.  Mount only the system runtime,
        # certificates, exact toolchain/local repositories, and the derived
        # checkout.  In particular, host /home, /run, and /tmp are not exposed.
        "--tmpfs",
        "/tmp",
        "--tmpfs",
        "/run",
        "--dir",
        "/etc",
        "--ro-bind",
        "/usr",
        "/usr",
        "--symlink",
        "usr/bin",
        "/bin",
        "--symlink",
        "usr/sbin",
        "/sbin",
        "--symlink",
        "usr/lib",
        "/lib",
        "--symlink",
        "usr/lib64",
        "/lib64",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
    ]
    for name in ("resolv.conf", "hosts", "nsswitch.conf", "passwd", "group"):
        command.extend(
            [
                "--ro-bind",
                os.fspath(sandbox / "etc" / name),
                os.fspath(Path("/etc") / name),
            ]
        )

    explicit_read_only = {path.resolve(strict=True) for path in read_only_inputs}
    if not is_within(lake_bin, Path("/usr")):
        lake_mount = (
            lake_bin.parent.parent
            if lake_bin.parent.name == "bin"
            else lake_bin
        ).resolve(strict=True)
        explicit_read_only.add(lake_mount)
    for source in sorted(explicit_read_only, key=os.fspath):
        if is_within(checkout, source):
            raise PreparationError(
                "derived checkout must not be nested in a read-only Lake input"
            )
        if is_within(source, checkout):
            continue
        command.extend(
            ["--ro-bind", os.fspath(source), os.fspath(source)]
        )

    protected_git_directories: set[Path] = set()
    for original in read_only_checkout_git_directories:
        if original.is_symlink():
            raise PreparationError(
                "derived Git administrative overlay is a symbolic link"
            )
        try:
            metadata = original.lstat()
            source = original.resolve(strict=True)
        except OSError as error:
            raise PreparationError(
                "derived Git administrative overlay does not exist"
            ) from error
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or source.name != ".git"
            or not is_within(source, checkout)
        ):
            raise PreparationError(
                "derived Git administrative overlay is not a checkout .git directory"
            )
        protected_git_directories.add(source)
    packages_root = checkout / ".lake" / "packages"
    if packages_root.is_symlink() or not packages_root.is_dir():
        raise PreparationError("derived packages root is unavailable to Lake")
    expected_git_directories = {(checkout / ".git").resolve(strict=True)}
    for package in packages_root.iterdir():
        if package.is_symlink() or not package.is_dir():
            raise PreparationError("derived package entry is not a real directory")
        git_directory = package / ".git"
        if git_directory.is_symlink() or not git_directory.is_dir():
            raise PreparationError("derived package has no real .git directory")
        expected_git_directories.add(git_directory.resolve(strict=True))
    if (
        len(protected_git_directories) != len(read_only_checkout_git_directories)
        or protected_git_directories != expected_git_directories
    ):
        raise PreparationError(
            "derived Git administrative overlays are incomplete or duplicated"
        )

    command.extend(
        [
        "--bind",
        os.fspath(checkout),
        os.fspath(checkout),
        ]
    )
    for source in sorted(protected_git_directories, key=os.fspath):
        command.extend(
            ["--ro-bind", os.fspath(source), os.fspath(source)]
        )
    command.extend(
        [
        "--clearenv",
        "--setenv",
        "HOME",
        os.fspath(sandbox / "home"),
        "--setenv",
        "TMPDIR",
        os.fspath(sandbox / "tmp"),
        "--setenv",
        "XDG_CACHE_HOME",
        os.fspath(sandbox / "cache"),
        "--setenv",
        "XDG_CONFIG_HOME",
        os.fspath(sandbox / "config"),
        "--setenv",
        "MATHLIB_CACHE_DIR",
        os.fspath(sandbox / "cache" / "mathlib"),
        "--setenv",
        "LAKE_NO_CACHE",
        "1",
        "--setenv",
        "LEAN_NUM_THREADS",
        "1",
        "--setenv",
        "PATH",
        search_path,
        "--setenv",
        "GIT_OPTIONAL_LOCKS",
        "0",
        "--setenv",
        "GIT_CONFIG_NOSYSTEM",
        "1",
        "--setenv",
        "GIT_CONFIG_GLOBAL",
        "/dev/null",
        "--setenv",
        "GIT_ATTR_NOSYSTEM",
        "1",
        "--setenv",
        "GIT_NO_REPLACE_OBJECTS",
        "1",
        "--setenv",
        "GIT_TERMINAL_PROMPT",
        "0",
        "--setenv",
        "LANG",
        "C",
        "--setenv",
        "LC_ALL",
        "C",
        "--chdir",
        os.fspath(checkout),
        "--",
        os.fspath(lake_bin),
        *[os.fspath(argument) for argument in lake_arguments],
        ]
    )
    return command


def run_offline_lake(
    lake_arguments: Sequence[str],
    *,
    checkout: Path,
    sandbox: Path,
    unshare_bin: Path,
    bwrap_bin: Path,
    lake_bin: Path,
    read_only_checkout_git_directories: Sequence[Path],
    timeout: float | None = None,
    recorder: list[CommandRecord] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run Lake with no network interface or egress process attached."""

    command = sandboxed_lake_command(
        checkout=checkout,
        sandbox=sandbox,
        unshare_bin=unshare_bin,
        bwrap_bin=bwrap_bin,
        lake_bin=lake_bin,
        lake_arguments=lake_arguments,
        read_only_checkout_git_directories=(
            read_only_checkout_git_directories
        ),
        read_only_inputs=(),
    )
    # A compiler crash or resource failure must stop preparation. Repeated
    # automatic builds can repeat the same host-level fault and hide evidence.
    local_records: list[CommandRecord] = []
    try:
        with host_limits.command_scope(
            command, timeout=timeout or 3600, cwd=checkout,
            environment=command_environment(),
        ) as bounded:
            return run_command(
                bounded, cwd=checkout, timeout=timeout or 3600,
                recorder=local_records,
            )
    except (RuntimeError, OSError) as error:
        raise PreparationError(
            'offline Lake command failed; automatic build retries are disabled: ' + str(error)
        ) from error
    finally:
        if recorder is not None:
            for record in local_records:
                recorder.append(
                    CommandRecord(
                        argv=record.argv,
                        cwd=record.cwd,
                        started_at=record.started_at,
                        finished_at=record.finished_at,
                        duration_seconds=record.duration_seconds,
                        returncode=record.returncode,
                        stdout=record.stdout,
                        stderr=record.stderr,
                        file_size_limit_bytes=record.file_size_limit_bytes,
                        role="lake-bwrap-offline-network",
                    )
                )


def repository_root(benchmark_root: Path, git_bin: Path) -> Path:
    result = run_command(
        [os.fspath(git_bin), "-C", os.fspath(benchmark_root), "rev-parse", "--show-toplevel"]
    )
    root = Path(result.stdout.strip()).resolve(strict=True)
    if not is_within(benchmark_root.resolve(strict=True), root):
        raise PreparationError("benchmark root is not contained in its Git repository")
    return root


def resolve_numstability_commit(
    git_bin: Path, repository: str, recorder: list[CommandRecord]
) -> str:
    # Fetching and checkout authentication below verify availability and bytes.
    # Reproduction never substitutes the current head of a moving branch.
    return exact_commit(NUMSTABILITY_REF, "paper Higham snapshot")


def exact_commit(value: Any, label: str) -> str:
    if not isinstance(value, str) or not COMMIT_RE.fullmatch(value.lower()):
        raise PreparationError(f"{label} must be an exact Git commit, got {value!r}")
    return value.lower()


def regular_file(root: Path, relative: Path) -> Path:
    path = root / relative
    if path.is_symlink() or not path.is_file():
        raise PreparationError(f"required regular file is missing: {relative}")
    return path


def safe_relative_directory(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise PreparationError(f"{label} must be a nonempty relative directory")
    path = Path(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise PreparationError(f"{label} is not a safe relative directory: {value!r}")
    return path.as_posix()


def safe_package_name(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise PreparationError(f"{label} must be a nonempty package name")
    path = Path(value)
    if len(path.parts) != 1 or path.name != value or value in {".", ".."}:
        raise PreparationError(f"{label} is not a safe package name: {value!r}")
    return value


def inspect_upstream_pins(checkout: Path) -> dict[str, Any]:
    toolchain_path = regular_file(checkout, Path("lean-toolchain"))
    lakefile_path = regular_file(checkout, Path("lakefile.toml"))
    lake_manifest_path = regular_file(checkout, Path("lake-manifest.json"))
    lookup_path = regular_file(checkout, LIBRARY_LOOKUP)
    lookup_check_path = regular_file(checkout, LIBRARY_LOOKUP_CHECK)

    lean_toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    if (
        not lean_toolchain.startswith("leanprover/lean4:")
        or lean_toolchain.rsplit(":", 1)[-1].lower() in FLOATING_REVISIONS
        or any(character.isspace() for character in lean_toolchain)
    ):
        raise PreparationError(
            f"upstream lean-toolchain is not an exact version pin: {lean_toolchain!r}"
        )

    with lakefile_path.open("rb") as stream:
        lakefile = tomllib.load(stream)
    requires = lakefile.get("require")
    if not isinstance(requires, list):
        raise PreparationError("upstream lakefile.toml has no [[require]] list")
    lakefile_mathlib = [entry for entry in requires if entry.get("name") == "mathlib"]
    if len(lakefile_mathlib) != 1:
        raise PreparationError("upstream lakefile.toml must require mathlib exactly once")
    lakefile_mathlib_commit = exact_commit(
        lakefile_mathlib[0].get("rev"), "lakefile.toml mathlib revision"
    )

    try:
        manifest = json.loads(lake_manifest_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise PreparationError("upstream lake-manifest.json is not valid JSON") from error
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        raise PreparationError("upstream lake-manifest.json has no packages list")
    packages_directory = safe_relative_directory(
        manifest.get("packagesDir", ".lake/packages"), "manifest packagesDir"
    )
    lake_directory = safe_relative_directory(
        manifest.get("lakeDir", ".lake"), "manifest lakeDir"
    )
    if lake_directory != ".lake" or packages_directory != ".lake/packages":
        raise PreparationError(
            "upstream Lake layout must be exactly .lake and .lake/packages"
        )
    mathlib_packages = [entry for entry in packages if entry.get("name") == "mathlib"]
    if len(mathlib_packages) != 1:
        raise PreparationError("upstream manifest must contain mathlib exactly once")
    mathlib = mathlib_packages[0]
    if mathlib.get("type") != "git":
        raise PreparationError("upstream mathlib dependency is not a Git dependency")
    mathlib_repository = mathlib.get("url")
    if not isinstance(mathlib_repository, str) or not mathlib_repository:
        raise PreparationError("upstream mathlib dependency has no Git repository")
    mathlib_repository = display_repository(mathlib_repository)
    mathlib_commit = exact_commit(mathlib.get("rev"), "manifest mathlib revision")
    mathlib_input = exact_commit(
        mathlib.get("inputRev"), "manifest mathlib input revision"
    )
    if mathlib_commit != lakefile_mathlib_commit or mathlib_input != mathlib_commit:
        raise PreparationError(
            "upstream lakefile and manifest do not agree on the exact mathlib commit"
        )

    dependency_pins: list[dict[str, Any]] = []
    dependency_names: set[str] = set()
    for package in packages:
        name = safe_package_name(
            package.get("name"), "upstream manifest package name"
        )
        if name in dependency_names:
            raise PreparationError(f"upstream manifest repeats package {name!r}")
        dependency_names.add(name)
        if package.get("type") != "git":
            raise PreparationError(f"manifest {name} dependency is not a Git dependency")
        repository = package.get("url")
        if not isinstance(repository, str) or not repository:
            raise PreparationError(f"manifest {name} dependency has no Git repository")
        repository = display_repository(repository)
        revision = exact_commit(package.get("rev"), f"manifest {name} revision")
        subdirectory = package.get("subDir")
        if subdirectory is not None:
            subdirectory = safe_relative_directory(
                subdirectory, f"manifest {name} subDir"
            )
        dependency_pins.append(
            {
                "name": name,
                "repository": repository,
                "commit": revision,
                "input_revision": package.get("inputRev"),
                "inherited": bool(package.get("inherited", False)),
                "subdirectory": subdirectory,
            }
        )

    for required_document in (lookup_path, lookup_check_path):
        if required_document.stat().st_size == 0:
            raise PreparationError(
                f"{required_document.relative_to(checkout)} is empty"
            )

    return {
        "lean": {
            "toolchain": lean_toolchain,
            "toolchain_file_sha256": sha256_file(toolchain_path),
        },
        "mathlib": {
            "repository": mathlib_repository,
            "commit": mathlib_commit,
            "input_revision": mathlib_input,
        },
        "dependencies": dependency_pins,
        "lake": {
            "directory": lake_directory,
            "packages_directory": packages_directory,
        },
        "files": {
            "lakefile.toml": sha256_file(lakefile_path),
            "lake-manifest.json": sha256_file(lake_manifest_path),
            "lean-toolchain": sha256_file(toolchain_path),
            os.fspath(LIBRARY_LOOKUP): sha256_file(lookup_path),
            os.fspath(LIBRARY_LOOKUP_CHECK): sha256_file(lookup_check_path),
        },
    }


def git_output(git_bin: Path, checkout: Path, *arguments: str) -> str:
    return run_command(
        [os.fspath(git_bin), "-C", os.fspath(checkout), *arguments],
        timeout=120.0,
    ).stdout.strip()


_DANGEROUS_GIT_SECTIONS = frozenset(
    {
        "alias",
        "credential",
        "diff",
        "filter",
        "fsck",
        "gpg",
        "include",
        "includeif",
        "interactive",
        "pager",
        "sequence",
        "url",
        "uploadpack",
    }
)
_DANGEROUS_CORE_KEYS = frozenset(
    {
        "attributesfile",
        "askpass",
        "alternaterefscommand",
        "editor",
        "excludesfile",
        "fsmonitor",
        "gitproxy",
        "hookspath",
        "pager",
        "sshcommand",
        "worktree",
    }
)


def assert_nonexecuting_git_config(checkout: Path, *, label: str) -> None:
    """Reject repository-local Git configuration that can execute host code.

    This parser is deliberately conservative and runs without invoking Git.  It
    is called before every Git-based checkout verification, so a derived Lake
    process cannot install an fsmonitor, hook path, include, filter, or similar
    executable configuration and have the trusted verifier trigger it later.
    """

    git_directory = checkout / ".git"
    try:
        git_metadata = git_directory.lstat()
    except OSError as error:
        raise PreparationError(f"{label} has no inspectable .git directory") from error
    if stat.S_ISLNK(git_metadata.st_mode) or not stat.S_ISDIR(git_metadata.st_mode):
        raise PreparationError(f"{label} .git must be a real directory")
    assert_passive_git_administrative_tree(git_directory, label=label)
    common_directory = git_directory / "commondir"
    if common_directory.exists() or common_directory.is_symlink():
        raise PreparationError(
            f"{label} uses unsupported .git/commondir indirection"
        )

    config_path = git_directory / "config"
    try:
        config_metadata = config_path.lstat()
    except OSError as error:
        raise PreparationError(f"{label} has no inspectable .git/config") from error
    if (
        stat.S_ISLNK(config_metadata.st_mode)
        or not stat.S_ISREG(config_metadata.st_mode)
        or config_metadata.st_size > 1024 * 1024
    ):
        raise PreparationError(f"{label} .git/config is not a small regular file")
    try:
        config_text = config_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise PreparationError(f"{label} .git/config is not safe UTF-8 text") from error
    if "\x00" in config_text or re.search(r"\\\s*$", config_text, re.MULTILINE):
        raise PreparationError(f"{label} .git/config uses unsupported continuation data")

    section: str | None = None
    for line_number, raw_line in enumerate(config_text.splitlines(), start=1):
        line = raw_line.strip()
        if not line or line.startswith(("#", ";")):
            continue
        if line.startswith("["):
            match = re.fullmatch(r'\[\s*([A-Za-z0-9.-]+)(?:\s+"(?:[^"\\]|\\.)*")?\s*\]', line)
            if match is None:
                raise PreparationError(
                    f"{label} .git/config has unsupported section syntax on line "
                    f"{line_number}"
                )
            section = match.group(1).lower()
            if any(
                section == dangerous or section.startswith(f"{dangerous}.")
                for dangerous in _DANGEROUS_GIT_SECTIONS
            ):
                raise PreparationError(
                    f"{label} .git/config contains forbidden [{section}] policy"
                )
            continue
        if section is None:
            raise PreparationError(
                f"{label} .git/config has a key outside a section on line {line_number}"
            )
        key_match = re.match(r"([A-Za-z][A-Za-z0-9-]*)(?:\s|=|$)", line)
        if key_match is None:
            raise PreparationError(
                f"{label} .git/config has unsupported key syntax on line {line_number}"
            )
        key = key_match.group(1).lower()
        raw_value = line[key_match.end() :].lstrip()
        if raw_value.startswith("="):
            raw_value = raw_value[1:].strip()
        value = raw_value.strip().strip('"').lower()
        if section == "core" and key in _DANGEROUS_CORE_KEYS:
            raise PreparationError(
                f"{label} .git/config contains forbidden core.{key} policy"
            )
        if (
            section == "remote" or section.startswith("remote.")
        ) and key in {"receivepack", "uploadpack"}:
            raise PreparationError(
                f"{label} .git/config contains executable remote.{key} policy"
            )
        if (
            section == "remote" or section.startswith("remote.")
        ) and key in {"promisor", "partialclonefilter"}:
            raise PreparationError(
                f"{label} .git/config contains forbidden lazy-fetch policy"
            )
        if (
            section == "remote" or section.startswith("remote.")
        ) and key in {"url", "pushurl"} and not (
            value.startswith(("https://", "file://", "/"))
        ):
            raise PreparationError(
                f"{label} .git/config contains an unsafe remote transport"
            )
        if section == "extensions" and key == "partialclone":
            raise PreparationError(
                f"{label} .git/config contains forbidden partial-clone policy"
            )
        if (
            section == "submodule" or section.startswith("submodule.")
        ) and key in {"update", "command"}:
            raise PreparationError(
                f"{label} .git/config contains executable submodule.{key} policy"
            )

    worktree_config = git_directory / "config.worktree"
    if worktree_config.exists() or worktree_config.is_symlink():
        raise PreparationError(f"{label} has an unsupported .git/config.worktree")
    hooks = git_directory / "hooks"
    if hooks.is_symlink() or not hooks.is_dir():
        raise PreparationError(f"{label} .git/hooks must be a real directory")
    for hook in hooks.iterdir():
        metadata = hook.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise PreparationError(f"{label} .git/hooks contains a symbolic link")
        if hook.name.endswith(".sample") and stat.S_ISREG(metadata.st_mode):
            continue
        raise PreparationError(f"{label} .git/hooks contains executable policy: {hook.name}")


def assert_index_exactly_matches_head(
    checkout: Path, git_bin: Path, *, label: str
) -> None:
    """Compare HEAD and index without diff drivers or submodule recursion."""

    head_output = git_output(
        git_bin, checkout, "ls-tree", "-r", "-z", "--full-tree", "HEAD"
    )
    index_output = git_output(git_bin, checkout, "ls-files", "--stage", "-z")
    head_entries: list[tuple[str, str, str]] = []
    index_entries: list[tuple[str, str, str]] = []
    try:
        for record in head_output.split("\0"):
            if not record:
                continue
            metadata, path = record.split("\t", 1)
            mode, object_type, object_id = metadata.split(" ", 2)
            if object_type not in {"blob", "commit"}:
                raise ValueError("unsupported HEAD object type")
            if mode == "160000" or object_type == "commit":
                raise PreparationError(
                    f"{label} contains an unsupported Git submodule/gitlink"
                )
            head_entries.append((mode, object_id, path))
        for record in index_output.split("\0"):
            if not record:
                continue
            metadata, path = record.split("\t", 1)
            mode, object_id, stage = metadata.split(" ", 2)
            if stage != "0" or mode == "160000":
                raise PreparationError(
                    f"{label} index contains a conflict or Git submodule/gitlink"
                )
            index_entries.append((mode, object_id, path))
    except ValueError as error:
        raise PreparationError(f"{label} Git index/tree metadata is malformed") from error
    if sorted(head_entries) != sorted(index_entries):
        raise PreparationError(f"{label} index differs from locked HEAD")


def assert_clean_detached_checkout(
    checkout: Path,
    git_bin: Path,
    expected_commit: str,
    *,
    label: str,
    include_ignored: bool = False,
) -> str:
    assert_nonexecuting_git_config(checkout, label=label)
    head = git_output(git_bin, checkout, "rev-parse", "HEAD").lower()
    if head != expected_commit:
        raise PreparationError(f"{label} HEAD is {head}, expected {expected_commit}")
    symbolic = subprocess.run(
        [os.fspath(git_bin), "-C", os.fspath(checkout), "symbolic-ref", "-q", "HEAD"],
        env=command_environment(),
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=120.0,
        check=False,
    )
    if symbolic.returncode == 0:
        raise PreparationError(f"{label} checkout is attached to {symbolic.stdout.strip()}")
    if symbolic.returncode not in {1}:
        raise PreparationError(f"unable to verify detached {label} checkout")
    assert_index_exactly_matches_head(checkout, git_bin, label=label)
    status_arguments = [
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=all",
    ]
    if include_ignored:
        status_arguments.append("--ignored=matching")
    status = git_output(git_bin, checkout, *status_arguments)
    if status:
        raise PreparationError(f"{label} checkout is dirty:\n{status}")
    run_command(
        [os.fspath(git_bin), "-C", os.fspath(checkout), "fsck", "--full"],
        timeout=120.0,
    )
    return git_output(git_bin, checkout, "rev-parse", "HEAD^{tree}").lower()


def assert_no_lake_directory(checkout: Path, *, label: str) -> None:
    """Reject even ignored Lake state in a checkout represented as pristine."""

    for directory, directory_names, file_names in os.walk(checkout):
        base = Path(directory)
        for name in [*directory_names, *file_names]:
            if name == ".lake":
                raise PreparationError(
                    f"{label} pristine checkout contains ignored .lake state: "
                    f"{base / name}"
                )


def assert_disjoint_trees(*trees: Path) -> None:
    resolved = [tree.resolve(strict=True) for tree in trees]
    for index, left in enumerate(resolved):
        for right in resolved[index + 1 :]:
            if left == right or is_within(left, right) or is_within(right, left):
                raise PreparationError(
                    f"runtime trees must be disjoint: {left} and {right}"
                )


def package_checkout(checkout: Path, package_dir: str, name: str) -> Path:
    result = (checkout / package_dir / name).resolve(strict=False)
    if not is_within(result, checkout.resolve(strict=True)):
        raise PreparationError("upstream packages directory escapes the checkout")
    return result


def verify_mathlib_checkout(
    checkout: Path, git_bin: Path, pins: Mapping[str, Any], *, required: bool
) -> Path | None:
    packages_dir = pins["lake"]["packages_directory"]
    mathlib = package_checkout(checkout, packages_dir, "mathlib")
    if not mathlib.exists():
        if required:
            raise PreparationError("lake build did not materialize the pinned mathlib checkout")
        return None
    if not mathlib.is_dir() or mathlib.is_symlink():
        raise PreparationError("mathlib checkout is not a regular directory")
    assert_clean_detached_checkout(
        mathlib,
        git_bin,
        pins["mathlib"]["commit"],
        label="mathlib",
    )
    return mathlib


def clone_detached(
    staging: Path,
    git_bin: Path,
    repository: str,
    commit: str,
    recorder: list[CommandRecord],
) -> None:
    local_repository = validate_repository_transport(
        repository, label="source clone"
    )
    if local_repository is not None:
        assert_no_special_files(local_repository, label="local source mirror")
        assert_nonexecuting_git_config(
            local_repository, label="local source mirror"
        )
    staging.mkdir(mode=0o700)
    run_command(
        [os.fspath(git_bin), "init", "--quiet", os.fspath(staging)],
        recorder=recorder,
    )
    run_command(
        [
            os.fspath(git_bin),
            "-C",
            os.fspath(staging),
            "remote",
            "add",
            "origin",
            git_transport_repository(repository),
        ],
        recorder=recorder,
    )
    run_command(
        [
            os.fspath(git_bin),
            "-C",
            os.fspath(staging),
            "fetch",
            "--quiet",
            "--depth=1",
            "origin",
            commit,
        ],
        recorder=recorder,
    )
    run_command(
        [
            os.fspath(git_bin),
            "-C",
            os.fspath(staging),
            "checkout",
            "--quiet",
            "--detach",
            "FETCH_HEAD",
        ],
        recorder=recorder,
    )


def prefetch_dependency_sources(
    *,
    source_store: Path,
    checkout: Path,
    pins: Mapping[str, Any],
    git_bin: Path,
    recorder: list[CommandRecord],
) -> list[dict[str, Any]]:
    """Fetch every locked package before Lake, then clone only from local stores."""

    dependencies = pins.get("dependencies")
    if not isinstance(dependencies, list) or not dependencies:
        raise PreparationError("locked manifest has no dependency packages to prefetch")
    packages_directory = str(pins["lake"]["packages_directory"])
    packages_root = package_checkout(checkout, packages_directory, "placeholder").parent
    if packages_root.exists() or packages_root.is_symlink():
        raise PreparationError("derived packages directory already exists before prefetch")
    packages_root.mkdir(parents=True, mode=0o700)
    source_store.mkdir(mode=0o700)
    records: list[dict[str, Any]] = []
    for dependency in dependencies:
        if not isinstance(dependency, Mapping):
            raise PreparationError("locked dependency record is invalid")
        name = safe_package_name(dependency.get("name"), "locked dependency name")
        repository = dependency.get("repository")
        if not isinstance(repository, str):
            raise PreparationError(f"locked dependency {name} has no repository")
        commit = exact_commit(
            dependency.get("commit"), f"locked dependency {name} commit"
        )
        fetched = source_store / name
        derived = packages_root / name
        clone_detached(fetched, git_bin, repository, commit, recorder)
        assert_no_special_files(fetched, label=f"prefetched {name} source")
        assert_no_hardlinked_regular_files(
            fetched, label=f"prefetched {name} source"
        )
        fetched_tree = assert_clean_detached_checkout(
            fetched,
            git_bin,
            commit,
            label=f"prefetched {name} source",
            include_ignored=True,
        )
        clone_detached(derived, git_bin, os.fspath(fetched), commit, recorder)
        assert_no_special_files(derived, label=f"derived {name} package")
        assert_no_hardlinked_regular_files(derived, label=f"derived {name} package")
        derived_tree = assert_clean_detached_checkout(
            derived,
            git_bin,
            commit,
            label=f"derived {name} package before Lake",
            include_ignored=True,
        )
        if derived_tree != fetched_tree:
            raise PreparationError(f"derived {name} tree differs from its source prefetch")
        records.append(
            {
                "name": name,
                "repository": display_repository(repository),
                "commit": commit,
                "git_tree": fetched_tree,
                "source_store_git_integrity": cache_integrity(fetched / ".git"),
                "derived_git_integrity_before_lake": cache_integrity(derived / ".git"),
            }
        )
    return records


def derived_git_administrative_directories(
    checkout: Path, pins: Mapping[str, Any]
) -> tuple[Path, ...]:
    """Resolve the exact root and dependency .git trees Lake must only read."""

    checkout = checkout.resolve(strict=True)
    dependencies = pins.get("dependencies")
    if not isinstance(dependencies, list):
        raise PreparationError("locked dependency list is invalid")
    packages_directory = str(pins["lake"]["packages_directory"])
    candidates = [checkout / ".git"]
    names: set[str] = set()
    for dependency in dependencies:
        if not isinstance(dependency, Mapping):
            raise PreparationError("locked dependency record is invalid")
        name = safe_package_name(dependency.get("name"), "locked dependency name")
        if name in names:
            raise PreparationError("locked dependency list contains a duplicate")
        names.add(name)
        candidates.append(
            package_checkout(checkout, packages_directory, name) / ".git"
        )

    resolved: list[Path] = []
    for candidate in candidates:
        if candidate.is_symlink():
            raise PreparationError(
                "derived Git administrative directory is a symbolic link"
            )
        try:
            metadata = candidate.lstat()
            directory = candidate.resolve(strict=True)
        except OSError as error:
            raise PreparationError(
                "derived Git administrative directory does not exist"
            ) from error
        if (
            not stat.S_ISDIR(metadata.st_mode)
            or directory.name != ".git"
            or not is_within(directory, checkout)
        ):
            raise PreparationError(
                "derived Git administrative path is not a real checkout directory"
            )
        resolved.append(directory)
    if len(set(resolved)) != len(resolved) or len(resolved) != len(dependencies) + 1:
        raise PreparationError(
            "derived Git administrative directory set is incomplete or duplicated"
        )
    return tuple(resolved)


def verify_prefetched_dependency_sources(
    *,
    checkout: Path,
    pins: Mapping[str, Any],
    records: Sequence[Mapping[str, Any]],
    git_bin: Path,
) -> None:
    """Prove that offline Lake neither replaced nor rewired a package checkout."""

    expected = {str(record.get("name")): record for record in records}
    dependencies = pins.get("dependencies")
    if not isinstance(dependencies, list) or len(expected) != len(dependencies):
        raise PreparationError("dependency prefetch record is incomplete")
    packages_directory = str(pins["lake"]["packages_directory"])
    for dependency in dependencies:
        name = str(dependency["name"])
        record = expected.get(name)
        if record is None:
            raise PreparationError(f"dependency prefetch record omits {name}")
        package = package_checkout(checkout, packages_directory, name)
        if package.is_symlink() or not package.is_dir():
            raise PreparationError(f"offline Lake removed prefetched package {name}")
        tree = assert_clean_detached_checkout(
            package,
            git_bin,
            str(dependency["commit"]),
            label=f"derived {name} package after Lake",
        )
        if tree != record.get("git_tree"):
            raise PreparationError(f"offline Lake changed tracked {name} sources")
        if cache_integrity(package / ".git") != record.get(
            "derived_git_integrity_before_lake"
        ):
            raise PreparationError(f"offline Lake changed {name} Git metadata")


def _validated_https_url(url: str, *, label: str) -> str:
    parts = urlsplit(url)
    if (
        parts.scheme != "https"
        or not parts.hostname
        or parts.username is not None
        or parts.password is not None
        or parts.query
        or parts.fragment
    ):
        raise PreparationError(f"{label} must be a credential-free HTTPS URL")
    return url


def download_https_file(
    *,
    curl_bin: Path,
    url: str,
    destination: Path,
    maximum_bytes: int,
    recorder: list[CommandRecord],
) -> dict[str, Any]:
    """Download one bounded HTTPS object to a fresh regular file."""

    url = _validated_https_url(url, label="prefetch URL")
    if destination.exists() or destination.is_symlink():
        raise PreparationError(f"prefetch destination already exists: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.parent / f".{destination.name}.{uuid.uuid4().hex}.part"
    try:
        run_command(
            [
                os.fspath(curl_bin),
                "--fail",
                "--fail-early",
                "--silent",
                "--show-error",
                "--location",
                "--proto",
                "=https",
                "--proto-redir",
                "=https",
                "--retry",
                "5",
                "--retry-all-errors",
                "--connect-timeout",
                "30",
                "--max-time",
                "1800",
                "--max-filesize",
                str(maximum_bytes),
                "--output",
                os.fspath(temporary),
                url,
            ],
            timeout=1860.0,
            recorder=recorder,
            file_size_limit_bytes=maximum_bytes,
        )
        metadata = temporary.lstat()
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_size <= 0
            or metadata.st_size > maximum_bytes
        ):
            raise PreparationError(f"downloaded object is invalid: {url}")
        os.replace(temporary, destination)
        return {
            "url": url,
            "size": metadata.st_size,
            "sha256": sha256_file(destination),
            "kernel_file_size_limit_bytes": maximum_bytes,
        }
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_mathlib_commit_manifest(payload: bytes) -> list[str]:
    """Authenticate and parse the fixed cache-key list for locked Mathlib."""

    if sha256_bytes(payload) != MATHLIB_COMMIT_MANIFEST_SHA256:
        raise PreparationError("Mathlib cache commit manifest SHA-256 mismatch")
    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as error:
        raise PreparationError("Mathlib cache commit manifest is not ASCII") from error
    if not text.endswith("\n") or "\r" in text:
        raise PreparationError("Mathlib cache commit manifest is not canonical")
    rows = text[:-1].split("\n")
    if len(rows) != MATHLIB_CACHE_ARTIFACT_COUNT:
        raise PreparationError("Mathlib cache commit manifest has the wrong file count")
    values: list[int] = []
    for row in rows:
        if not row or not row.isascii() or not row.isdecimal():
            raise PreparationError("Mathlib cache commit manifest has an invalid hash")
        value = int(row, 10)
        if value > (1 << 64) - 1 or str(value) != row:
            raise PreparationError("Mathlib cache commit manifest has a noncanonical hash")
        values.append(value)
    if values != sorted(set(values)):
        raise PreparationError("Mathlib cache commit manifest is not strictly sorted")
    filenames = [f"{value:016x}.ltar" for value in values]
    filename_set = "".join(f"{name}\n" for name in filenames).encode("ascii")
    if sha256_bytes(filename_set) != MATHLIB_CACHE_FILENAME_SET_SHA256:
        raise PreparationError("Mathlib cache filename set does not match the lock")
    return filenames


def load_tracked_mathlib_commit_manifest() -> tuple[list[str], dict[str, Any]]:
    """Load the content-locked cache-key list without a mutable network marker.

    The official cache's ``c/<commit>`` object is an index rather than a build
    dependency, and old index objects may disappear while their immutable
    ``f/<hash>.ltar`` artifacts remain available.  Keeping the already-locked
    index in the controlled runner makes preparation independent of that
    retention policy.  The parser still authenticates its exact SHA-256,
    canonical order, count, and derived filename-set digest before any cache
    artifact is requested.
    """

    path = MATHLIB_COMMIT_MANIFEST_PATH
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise PreparationError(
            f"cannot open tracked Mathlib cache commit manifest: {path}"
        ) from error
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & 0o022
            or metadata.st_size != MATHLIB_COMMIT_MANIFEST_BYTES
        ):
            raise PreparationError(
                "tracked Mathlib cache commit manifest has unsafe metadata"
            )
        payload = bytearray()
        while len(payload) <= MATHLIB_COMMIT_MANIFEST_BYTES:
            chunk = os.read(
                descriptor,
                min(
                    64 * 1024,
                    MATHLIB_COMMIT_MANIFEST_BYTES + 1 - len(payload),
                ),
            )
            if not chunk:
                break
            payload.extend(chunk)
    finally:
        os.close(descriptor)
    if len(payload) != MATHLIB_COMMIT_MANIFEST_BYTES:
        raise PreparationError(
            "tracked Mathlib cache commit manifest changed while being read"
        )
    locked_payload = bytes(payload)
    filenames = parse_mathlib_commit_manifest(locked_payload)
    return filenames, dict(MATHLIB_COMMIT_MANIFEST_RECORD)


def download_mathlib_cache_artifacts(
    *,
    curl_bin: Path,
    filenames: Sequence[str],
    cache_directory: Path,
    recorder: list[CommandRecord],
) -> dict[str, Any]:
    """Fetch the complete fixed LTAR set and authenticate every resulting byte."""

    if len(filenames) > MAX_CACHE_ARTIFACTS:
        raise PreparationError("Mathlib cache artifact count exceeds the safety bound")
    cache_directory.mkdir(parents=True, mode=0o700)
    batch_size = 128
    downloaded_bytes = 0
    for start in range(0, len(filenames), batch_size):
        batch = filenames[start : start + batch_size]
        remaining_bytes = MAX_CACHE_TOTAL_BYTES - downloaded_bytes
        per_file_limit = min(
            MAX_CACHE_ARTIFACT_BYTES, remaining_bytes // len(batch)
        )
        if per_file_limit < 12:
            raise PreparationError("Mathlib cache exceeds the total safety bound")
        command = [
            os.fspath(curl_bin),
            "--fail",
            "--fail-early",
            "--silent",
            "--show-error",
            "--location",
            "--proto",
            "=https",
            "--proto-redir",
            "=https",
            "--retry",
            "5",
            "--retry-all-errors",
            "--connect-timeout",
            "30",
            "--max-time",
            "1800",
            "--max-filesize",
            str(per_file_limit),
            "--parallel",
            "--parallel-immediate",
            "--parallel-max",
            "16",
        ]
        temporary_paths: list[tuple[Path, Path]] = []
        try:
            for name in batch:
                if not re.fullmatch(r"[0-9a-f]{16}\.ltar", name):
                    raise PreparationError(f"invalid locked cache filename: {name!r}")
                final = cache_directory / name
                temporary = cache_directory / f".{name}.{uuid.uuid4().hex}.part"
                if final.exists() or final.is_symlink() or temporary.exists():
                    raise PreparationError(f"cache prefetch path already exists: {final}")
                url = _validated_https_url(
                    f"{MATHLIB_CACHE_BASE_URL}/f/{name}", label="Mathlib LTAR URL"
                )
                command.extend(
                    ["--url", url, "--output", os.fspath(temporary)]
                )
                temporary_paths.append((temporary, final))
            run_command(
                command,
                timeout=1860.0,
                recorder=recorder,
                file_size_limit_bytes=per_file_limit,
            )
            batch_bytes = 0
            for temporary, final in temporary_paths:
                metadata = temporary.lstat()
                if (
                    not stat.S_ISREG(metadata.st_mode)
                    or metadata.st_nlink != 1
                    or metadata.st_size < 12
                    or metadata.st_size > per_file_limit
                ):
                    raise PreparationError(f"invalid downloaded LTAR: {final.name}")
                batch_bytes += metadata.st_size
                with temporary.open("rb") as stream:
                    magic = stream.read(4)
                if magic not in {b"LTAR", b"LTR2", b"LTR3"}:
                    raise PreparationError(f"invalid LTAR magic: {final.name}")
            if downloaded_bytes + batch_bytes > MAX_CACHE_TOTAL_BYTES:
                raise PreparationError("Mathlib cache exceeds the total safety bound")
            # Validate the entire parallel batch before installing any member.
            for temporary, final in temporary_paths:
                os.replace(temporary, final)
            downloaded_bytes += batch_bytes
        finally:
            for temporary, _final in temporary_paths:
                if temporary.exists():
                    temporary.unlink()
    return verify_mathlib_cache_artifacts(
        cache_directory=cache_directory, filenames=filenames
    )


def verify_mathlib_cache_artifacts(
    *, cache_directory: Path, filenames: Sequence[str]
) -> dict[str, Any]:
    total_bytes = 0
    canonical = hashlib.sha256()
    for name in filenames:
        path = cache_directory / name
        metadata = path.lstat()
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_size < 12
            or metadata.st_size > MAX_CACHE_ARTIFACT_BYTES
        ):
            raise PreparationError(f"prefetched LTAR is missing or invalid: {name}")
        total_bytes += metadata.st_size
        if total_bytes > MAX_CACHE_TOTAL_BYTES:
            raise PreparationError("Mathlib cache exceeds the total safety bound")
        digest = sha256_file(path)
        canonical.update(f"{name} {metadata.st_size} {digest}\n".encode("ascii"))
    aggregate = canonical.hexdigest()
    if total_bytes != MATHLIB_CACHE_ARTIFACT_BYTES:
        raise PreparationError("Mathlib cache total byte count differs from the lock")
    if aggregate != MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256:
        raise PreparationError("Mathlib cache artifact SHA-256 manifest mismatch")
    return {
        "count": len(filenames),
        "total_bytes": total_bytes,
        "content_manifest_sha256": aggregate,
        "filename_set_sha256": MATHLIB_CACHE_FILENAME_SET_SHA256,
        "every_file_sha256_verified": True,
        "every_file_ltar_magic_verified": True,
    }


def install_locked_leantar(
    *,
    curl_bin: Path,
    work_directory: Path,
    cache_directory: Path,
    recorder: list[CommandRecord],
) -> dict[str, Any]:
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise PreparationError(
            "the locked leantar prefetch currently supports Linux x86_64 only"
        )
    url = (
        "https://github.com/digama0/leangz/releases/download/"
        f"v{LEANTAR_VERSION}/leantar-v{LEANTAR_VERSION}-"
        "x86_64-unknown-linux-musl.tar.gz"
    )
    archive = work_directory / "leantar.tar.gz"
    download = download_https_file(
        curl_bin=curl_bin,
        url=url,
        destination=archive,
        maximum_bytes=64 * 1024 * 1024,
        recorder=recorder,
    )
    if download["sha256"] != LEANTAR_ARCHIVE_SHA256:
        raise PreparationError("leantar release archive SHA-256 mismatch")
    candidates: list[tarfile.TarInfo] = []
    total = 0
    with tarfile.open(archive, mode="r:gz") as bundle:
        members = bundle.getmembers()
        if not members or len(members) > 100:
            raise PreparationError("leantar release archive has an invalid member count")
        seen: set[str] = set()
        for member in members:
            name = member.name.removeprefix("./")
            path = Path(name)
            if (
                not name
                or name in seen
                or "\\" in name
                or "\x00" in name
                or path.is_absolute()
                or any(part in {"", ".", ".."} for part in path.parts)
                or not (member.isdir() or member.isreg())
            ):
                raise PreparationError("leantar release archive has an unsafe member")
            seen.add(name)
            if member.isreg():
                total += member.size
                if total > 128 * 1024 * 1024:
                    raise PreparationError("leantar archive exceeds its size bound")
                if path.name == "leantar":
                    candidates.append(member)
        if len(candidates) != 1:
            raise PreparationError("leantar archive does not contain one binary")
        source = bundle.extractfile(candidates[0])
        if source is None:
            raise PreparationError("unable to read leantar release binary")
        destination = cache_directory / f"leantar-{LEANTAR_VERSION}"
        if destination.exists() or destination.is_symlink():
            raise PreparationError("leantar cache destination already exists")
        with source, destination.open("xb") as output:
            shutil.copyfileobj(source, output, length=1024 * 1024)
    if sha256_file(destination) != LEANTAR_BINARY_SHA256:
        raise PreparationError("leantar binary SHA-256 mismatch")
    destination.chmod(0o555)
    return {
        **download,
        "version": LEANTAR_VERSION,
        "binary_sha256": LEANTAR_BINARY_SHA256,
        "binary_relative_path": destination.relative_to(cache_directory).as_posix(),
    }


def proofwidgets_archive_member_path(member: tarfile.TarInfo) -> Path | None:
    """Return the safe release-relative path, or ``None`` for its root."""

    name = member.name
    while name.startswith("./"):
        name = name[2:]
    if not name or name == ".":
        if not member.isdir():
            raise PreparationError("ProofWidgets archive root is not a directory")
        return None
    path = Path(name)
    if (
        "\\" in name
        or "\x00" in name
        or path.is_absolute()
        or any(part in {"", ".", ".."} for part in path.parts)
        or not path.parts
        or path.parts[0] not in {"js", "lib", "ir"}
        or not (member.isdir() or member.isreg())
    ):
        raise PreparationError("ProofWidgets archive has an unsafe member")
    return path


def install_locked_proofwidgets_release(
    *,
    curl_bin: Path,
    work_directory: Path,
    checkout: Path,
    pins: Mapping[str, Any],
    recorder: list[CommandRecord],
) -> dict[str, Any]:
    dependencies = {
        str(dependency["name"]): dependency for dependency in pins["dependencies"]
    }
    proofwidgets = dependencies.get("proofwidgets")
    if (
        proofwidgets is None
        or proofwidgets.get("commit") != SUPPORTED_PROOFWIDGETS_COMMIT
    ):
        raise PreparationError("ProofWidgets dependency does not match the release lock")
    archive = work_directory / "ProofWidgets4.tar.gz"
    download = download_https_file(
        curl_bin=curl_bin,
        url=PROOFWIDGETS_RELEASE_URL,
        destination=archive,
        maximum_bytes=64 * 1024 * 1024,
        recorder=recorder,
    )
    if (
        download["sha256"] != PROOFWIDGETS_RELEASE_SHA256
        or download["size"] != PROOFWIDGETS_RELEASE_BYTES
    ):
        raise PreparationError("ProofWidgets release archive does not match the lock")
    package = package_checkout(
        checkout, str(pins["lake"]["packages_directory"]), "proofwidgets"
    )
    build_directory = package / ".lake" / "build"
    js_directory = build_directory / "js"
    if build_directory.exists() or build_directory.is_symlink():
        raise PreparationError("ProofWidgets build directory exists before release prefetch")
    js_files = 0
    js_bytes = 0
    regular_files = 0
    directories = 0
    total_bytes = 0
    seen: set[str] = set()
    with tarfile.open(archive, mode="r:gz") as bundle:
        members = bundle.getmembers()
        if len(members) != 563:
            raise PreparationError("ProofWidgets archive member count differs from the lock")
        for member in members:
            path = proofwidgets_archive_member_path(member)
            canonical_name = "." if path is None else path.as_posix()
            if canonical_name in seen:
                raise PreparationError("ProofWidgets archive has an unsafe member")
            seen.add(canonical_name)
            if path is None:
                continue
            if member.isdir():
                directories += 1
                continue
            regular_files += 1
            total_bytes += member.size
            if member.size > 4 * 1024 * 1024 or total_bytes > 64 * 1024 * 1024:
                raise PreparationError("ProofWidgets archive exceeds its size lock")
            if path.parts[0] != "js":
                continue
            js_files += 1
            js_bytes += member.size
            destination = build_directory.joinpath(*path.parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            source = bundle.extractfile(member)
            if source is None:
                raise PreparationError("unable to read ProofWidgets JS member")
            with source, destination.open("xb") as output:
                shutil.copyfileobj(source, output, length=1024 * 1024)
    if (
        regular_files != 540
        or directories != 22
        or total_bytes != 52_275_340
        or js_files != 20
        or js_bytes != 6_902_637
    ):
        raise PreparationError("ProofWidgets archive layout differs from the lock")
    return {
        **download,
        "commit": SUPPORTED_PROOFWIDGETS_COMMIT,
        "js_file_count": js_files,
        "js_total_bytes": js_bytes,
        "js_integrity": cache_integrity(js_directory),
    }


def prefetch_binary_cache(
    *,
    checkout: Path,
    sandbox: Path,
    pins: Mapping[str, Any],
    curl_bin: Path,
    recorder: list[CommandRecord],
) -> tuple[dict[str, Any], list[str]]:
    """Download and authenticate every non-Git input before the first Lake run."""

    mathlib_commit = str(pins["mathlib"]["commit"])
    if mathlib_commit != SUPPORTED_MATHLIB_COMMIT:
        raise PreparationError(
            "Mathlib commit is not covered by the tracked binary-cache lock"
        )
    work_directory = sandbox / "prefetch"
    work_directory.mkdir(mode=0o700)
    cache_directory = sandbox / "cache" / "mathlib"
    filenames, commit_manifest = load_tracked_mathlib_commit_manifest()
    artifacts = download_mathlib_cache_artifacts(
        curl_bin=curl_bin,
        filenames=filenames,
        cache_directory=cache_directory,
        recorder=recorder,
    )
    leantar = install_locked_leantar(
        curl_bin=curl_bin,
        work_directory=work_directory,
        cache_directory=cache_directory,
        recorder=recorder,
    )
    proofwidgets = install_locked_proofwidgets_release(
        curl_bin=curl_bin,
        work_directory=work_directory,
        checkout=checkout,
        pins=pins,
        recorder=recorder,
    )
    return (
        {
            "phase": "completed-before-first-lake-process",
            "mathlib_commit_manifest": commit_manifest,
            "mathlib_ltar_artifacts": artifacts,
            "mathlib_ltar_download_safety": {
                "kernel_file_size_limit_each_curl_process": True,
                "remaining_aggregate_bound_applied_before_each_batch": True,
                "maximum_aggregate_bytes": MAX_CACHE_TOTAL_BYTES,
            },
            "leantar": leantar,
            "proofwidgets_release": proofwidgets,
            "first_download_authentication": (
                "tracked-sha256-lock-plus-credential-free-https"
            ),
        },
        filenames,
    )


def expected_lean_version(toolchain: str) -> str:
    version = toolchain.rsplit(":", 1)[-1]
    return version[1:] if version.startswith("v") else version


def verify_tool_versions(
    checkout: Path,
    lake_bin: Path,
    unshare_bin: Path,
    bwrap_bin: Path,
    curl_bin: Path,
    zstd_bin: Path,
    sandbox: Path,
    pins: Mapping[str, Any],
    read_only_checkout_git_directories: Sequence[Path],
    lean_toolchain_prefetch: Mapping[str, Any],
    recorder: list[CommandRecord],
) -> dict[str, Any]:
    bwrap = run_command(
        [os.fspath(bwrap_bin), "--version"], recorder=recorder
    ).stdout.strip()
    unshare = run_command(
        [os.fspath(unshare_bin), "--version"], recorder=recorder
    ).stdout.strip()
    curl = run_command(
        [os.fspath(curl_bin), "--version"], recorder=recorder
    ).stdout.strip()
    zstd = run_command(
        [os.fspath(zstd_bin), "--version"], recorder=recorder
    ).stdout.strip()
    lake = run_offline_lake(
        ["--version"],
        checkout=checkout,
        sandbox=sandbox,
        unshare_bin=unshare_bin,
        bwrap_bin=bwrap_bin,
        lake_bin=lake_bin,
        read_only_checkout_git_directories=(
            read_only_checkout_git_directories
        ),
        recorder=recorder,
    ).stdout.strip()
    lean = run_offline_lake(
        ["env", "lean", "--version"],
        checkout=checkout,
        sandbox=sandbox,
        unshare_bin=unshare_bin,
        bwrap_bin=bwrap_bin,
        lake_bin=lake_bin,
        read_only_checkout_git_directories=(
            read_only_checkout_git_directories
        ),
        recorder=recorder,
    ).stdout.strip()
    expected = expected_lean_version(pins["lean"]["toolchain"])
    lean_match = re.fullmatch(r"Lean \(version ([^,()\s]+),.*\)", lean)
    lake_match = re.fullmatch(r"Lake version .+ \(Lean version ([^()\s]+)\)", lake)
    if lean_match is None or lean_match.group(1) != expected:
        raise PreparationError(
            f"observed Lean version does not match {pins['lean']['toolchain']}: {lean!r}"
        )
    if lake_match is None or lake_match.group(1) != expected:
        raise PreparationError(
            f"observed Lake toolchain does not match {pins['lean']['toolchain']}: "
            f"{lake!r}"
        )
    if (
        lean_toolchain_prefetch.get("integrity") != LEAN_TOOLCHAIN_INTEGRITY
        or lean_toolchain_prefetch.get("lake_sha256")
        != LEAN_TOOLCHAIN_LAKE_SHA256
        or lean_toolchain_prefetch.get("lean_sha256")
        != LEAN_TOOLCHAIN_LEAN_SHA256
    ):
        raise PreparationError("offline Lake toolchain identity differs from the lock")
    return {
        "preparation_script_sha256": sha256_file(Path(__file__).resolve()),
        "lean_toolchain": SUPPORTED_LEAN_TOOLCHAIN,
        "lean_toolchain_integrity": dict(LEAN_TOOLCHAIN_INTEGRITY),
        "lean_toolchain_archive_sha256": LEAN_TOOLCHAIN_ARCHIVE_SHA256,
        "lake_executable": "private-prefetch/lean-toolchain/bin/lake",
        "lake_executable_sha256": LEAN_TOOLCHAIN_LAKE_SHA256,
        "lean_executable": "private-prefetch/lean-toolchain/bin/lean",
        "lean_executable_sha256": LEAN_TOOLCHAIN_LEAN_SHA256,
        "lake_version": lake,
        "lean_version": lean,
        "bubblewrap_executable": os.fspath(bwrap_bin),
        "bubblewrap_executable_sha256": sha256_file(bwrap_bin),
        "bubblewrap_version": bwrap,
        "unshare_executable": os.fspath(unshare_bin),
        "unshare_executable_sha256": sha256_file(unshare_bin),
        "unshare_version": unshare,
        "curl_executable": os.fspath(curl_bin),
        "curl_executable_sha256": sha256_file(curl_bin),
        "curl_version": curl.splitlines()[0] if curl else curl,
        "zstd_executable": os.fspath(zstd_bin),
        "zstd_executable_sha256": sha256_file(zstd_bin),
        "zstd_version": zstd.splitlines()[0] if zstd else zstd,
        "lake_network": "offline-private-unshare",
        "explicit_local_repository_mounts": [],
        "preparation_isolation": dict(PREPARATION_ISOLATION),
    }


def verify_cached_builder_tools(
    unshare_bin: Path,
    bwrap_bin: Path,
    curl_bin: Path,
    zstd_bin: Path,
    recorded_tools: Mapping[str, Any],
) -> None:
    """Authenticate cached builders without executing removed prefetch inputs."""

    if recorded_tools.get("preparation_script_sha256") != sha256_file(
        Path(__file__).resolve()
    ):
        raise PreparationError(
            "current preparation implementation differs from cached builder"
        )
    if (
        recorded_tools.get("lean_toolchain") != SUPPORTED_LEAN_TOOLCHAIN
        or recorded_tools.get("lean_toolchain_integrity")
        != LEAN_TOOLCHAIN_INTEGRITY
        or recorded_tools.get("lean_toolchain_archive_sha256")
        != LEAN_TOOLCHAIN_ARCHIVE_SHA256
        or recorded_tools.get("lake_executable")
        != "private-prefetch/lean-toolchain/bin/lake"
        or recorded_tools.get("lake_executable_sha256")
        != LEAN_TOOLCHAIN_LAKE_SHA256
        or recorded_tools.get("lean_executable")
        != "private-prefetch/lean-toolchain/bin/lean"
        or recorded_tools.get("lean_executable_sha256")
        != LEAN_TOOLCHAIN_LEAN_SHA256
    ):
        raise PreparationError("cached Lean toolchain lock was tampered")
    if recorded_tools.get("bubblewrap_executable") != os.fspath(bwrap_bin):
        raise PreparationError(
            "current Bubblewrap executable path differs from cached builder"
        )
    if recorded_tools.get("bubblewrap_executable_sha256") != sha256_file(bwrap_bin):
        raise PreparationError("current Bubblewrap executable differs from cached builder")
    if recorded_tools.get("unshare_executable") != os.fspath(unshare_bin):
        raise PreparationError("current unshare executable path differs from cached builder")
    if recorded_tools.get("unshare_executable_sha256") != sha256_file(unshare_bin):
        raise PreparationError("current unshare executable differs from cached builder")
    if (
        recorded_tools.get("curl_executable") != os.fspath(curl_bin)
        or recorded_tools.get("curl_executable_sha256") != sha256_file(curl_bin)
    ):
        raise PreparationError("current curl executable differs from cached builder")
    if (
        recorded_tools.get("zstd_executable") != os.fspath(zstd_bin)
        or recorded_tools.get("zstd_executable_sha256") != sha256_file(zstd_bin)
    ):
        raise PreparationError("current zstd executable differs from cached builder")
    if recorded_tools.get("lake_network") != "offline-private-unshare":
        raise PreparationError("cached Lake network contract is not offline")
    if recorded_tools.get("explicit_local_repository_mounts") != []:
        raise PreparationError("cached Lake unexpectedly mounted a local repository")
    if recorded_tools.get("preparation_isolation") != PREPARATION_ISOLATION:
        raise PreparationError("cached preparation isolation contract was tampered")


def iter_integrity_entries(root: Path) -> Iterable[tuple[str, Path, os.stat_result]]:
    """Yield every cache entry, including Git and ignored build artifacts."""

    pending = [root]
    while pending:
        directory = pending.pop()
        children = sorted(directory.iterdir(), key=lambda item: item.name)
        for child in children:
            metadata = child.lstat()
            relative = child.relative_to(root).as_posix()
            yield relative, child, metadata
            if stat.S_ISDIR(metadata.st_mode):
                pending.append(child)


def assert_no_hardlinked_regular_files(root: Path, *, label: str) -> None:
    """Prove that immutable source bytes have no writable inode alias."""

    for relative, _path, metadata in iter_integrity_entries(root):
        if stat.S_ISREG(metadata.st_mode) and metadata.st_nlink != 1:
            raise PreparationError(
                f"{label} contains a hard-linked regular file: {relative} "
                f"(link count {metadata.st_nlink})"
            )


def assert_no_special_files(root: Path, *, label: str) -> None:
    """Reject host IPC/device capabilities from an explicit read-only input."""

    for relative, _path, metadata in iter_integrity_entries(root):
        if not any(
            predicate(metadata.st_mode)
            for predicate in (stat.S_ISDIR, stat.S_ISREG, stat.S_ISLNK)
        ):
            raise PreparationError(
                f"{label} contains a socket, FIFO, device, or other special entry: "
                f"{relative}"
            )


def assert_passive_git_administrative_tree(
    git_directory: Path, *, label: str
) -> None:
    """Reject Git metadata that could redirect or block a host verifier."""

    for relative, _path, metadata in iter_integrity_entries(git_directory):
        if stat.S_ISLNK(metadata.st_mode):
            raise PreparationError(
                f"{label} .git contains a symbolic link: {relative}"
            )
        if not any(
            predicate(metadata.st_mode) for predicate in (stat.S_ISDIR, stat.S_ISREG)
        ):
            raise PreparationError(
                f"{label} .git contains a non-passive special entry: {relative}"
            )


def cache_integrity(checkout: Path) -> dict[str, Any]:
    digest = hashlib.sha256()
    files = 0
    directories = 0
    symlinks = 0
    total_bytes = 0
    for relative, path, metadata in iter_integrity_entries(checkout):
        mode = stat.S_IMODE(metadata.st_mode)
        executable = bool(mode & 0o111)
        if stat.S_ISDIR(metadata.st_mode):
            kind = "directory"
            content_digest = ""
            directories += 1
        elif stat.S_ISREG(metadata.st_mode):
            kind = "file"
            content_digest = sha256_file(path)
            files += 1
            total_bytes += metadata.st_size
        elif stat.S_ISLNK(metadata.st_mode):
            kind = "symlink"
            content_digest = sha256_bytes(os.readlink(path).encode("utf-8"))
            symlinks += 1
        else:
            raise PreparationError(f"unsupported cache filesystem entry: {relative}")
        digest.update(
            canonical_json_bytes(
                {
                    "path": relative,
                    "kind": kind,
                    "executable": executable,
                    "size": metadata.st_size if kind == "file" else None,
                    "link_count": metadata.st_nlink if kind == "file" else None,
                    "content_sha256": content_digest,
                }
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


def assert_internal_symlinks(root: Path, *, label: str) -> None:
    """Require every symlink in a mounted tree to resolve inside that tree."""

    root = root.resolve(strict=True)
    for relative, path, metadata in iter_integrity_entries(root):
        if not stat.S_ISLNK(metadata.st_mode):
            continue
        target = os.readlink(path)
        if not target or "\x00" in target or Path(target).is_absolute():
            raise PreparationError(f"{label} has an unsafe symlink: {relative}")
        try:
            resolved = path.resolve(strict=True)
        except (OSError, RuntimeError) as error:
            raise PreparationError(
                f"{label} has a broken or cyclic symlink: {relative}"
            ) from error
        if not is_within(resolved, root):
            raise PreparationError(f"{label} symlink escapes its root: {relative}")


def verify_locked_lean_toolchain(root: Path, *, label: str) -> dict[str, Any]:
    """Authenticate the complete official Lean toolchain tree."""

    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise PreparationError(
            "the locked Lean toolchain currently supports Linux x86_64 only"
        )
    if root.is_symlink() or not root.is_dir():
        raise PreparationError(f"{label} root must be a real directory")
    root = root.resolve(strict=True)
    assert_no_special_files(root, label=label)
    assert_no_hardlinked_regular_files(root, label=label)
    assert_internal_symlinks(root, label=label)
    integrity = cache_integrity(root)
    if integrity != LEAN_TOOLCHAIN_INTEGRITY:
        raise PreparationError(f"{label} complete-tree integrity differs from the lock")
    lake = root / "bin" / "lake"
    lean = root / "bin" / "lean"
    for name, executable, expected_sha256 in (
        ("Lake", lake, LEAN_TOOLCHAIN_LAKE_SHA256),
        ("Lean", lean, LEAN_TOOLCHAIN_LEAN_SHA256),
    ):
        metadata = executable.lstat()
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or not metadata.st_mode & 0o111
            or sha256_file(executable) != expected_sha256
        ):
            raise PreparationError(f"{label} {name} executable differs from the lock")
    return {
        "toolchain": SUPPORTED_LEAN_TOOLCHAIN,
        "archive_url": LEAN_TOOLCHAIN_ARCHIVE_URL,
        "archive_size": LEAN_TOOLCHAIN_ARCHIVE_BYTES,
        "archive_sha256": LEAN_TOOLCHAIN_ARCHIVE_SHA256,
        "integrity": integrity,
        "lake_sha256": LEAN_TOOLCHAIN_LAKE_SHA256,
        "lean_sha256": LEAN_TOOLCHAIN_LEAN_SHA256,
    }


def extract_locked_lean_toolchain(
    *, archive: Path, destination: Path
) -> None:
    """Safely extract the already-authenticated official toolchain tar."""

    if destination.exists() or destination.is_symlink():
        raise PreparationError("private Lean toolchain destination already exists")
    directories: dict[str, tarfile.TarInfo] = {}
    regular_files: dict[str, tarfile.TarInfo] = {}
    symlinks: dict[str, tarfile.TarInfo] = {}
    seen: set[str] = set()
    root_seen = False
    regular_bytes = 0
    with tarfile.open(archive, mode="r:") as bundle:
        for member in bundle.getmembers():
            name = member.name
            path = Path(name)
            if (
                not name
                or name in seen
                or "\\" in name
                or "\x00" in name
                or path.is_absolute()
                or any(part in {"", ".", ".."} for part in path.parts)
                or path.parts[0] != LEAN_TOOLCHAIN_ARCHIVE_ROOT
            ):
                raise PreparationError("Lean toolchain archive has an unsafe member")
            seen.add(name)
            if len(path.parts) == 1:
                if root_seen or not member.isdir():
                    raise PreparationError("Lean toolchain archive root is invalid")
                root_seen = True
                continue
            relative = Path(*path.parts[1:]).as_posix()
            if member.isdir():
                if not member.mode & 0o111:
                    raise PreparationError(
                        "Lean toolchain archive has a non-searchable directory"
                    )
                directories[relative] = member
            elif member.isreg():
                regular_files[relative] = member
                regular_bytes += member.size
            elif member.issym():
                target = member.linkname
                if (
                    not target
                    or "\x00" in target
                    or Path(target).is_absolute()
                ):
                    raise PreparationError(
                        "Lean toolchain archive has an unsafe symlink"
                    )
                normalized = os.path.normpath(
                    (Path(relative).parent / target).as_posix()
                )
                if normalized == ".." or normalized.startswith("../"):
                    raise PreparationError(
                        "Lean toolchain archive symlink escapes its root"
                    )
                symlinks[relative] = member
            else:
                raise PreparationError(
                    "Lean toolchain archive contains a hard link or special entry"
                )
        if (
            not root_seen
            or len(directories) != LEAN_TOOLCHAIN_INTEGRITY["directories"]
            or len(regular_files) != LEAN_TOOLCHAIN_INTEGRITY["regular_files"]
            or len(symlinks) != LEAN_TOOLCHAIN_INTEGRITY["symlinks"]
            or regular_bytes
            != LEAN_TOOLCHAIN_INTEGRITY["regular_file_bytes"]
        ):
            raise PreparationError("Lean toolchain archive layout differs from the lock")

        represented_directories = {"", *directories}
        for relative in [*regular_files, *symlinks]:
            parent = Path(relative).parent.as_posix()
            if parent == ".":
                parent = ""
            if parent not in represented_directories:
                raise PreparationError(
                    "Lean toolchain archive omits a required parent directory"
                )

        destination.mkdir(mode=0o700)
        for relative, member in sorted(
            directories.items(), key=lambda item: (len(Path(item[0]).parts), item[0])
        ):
            path = destination.joinpath(*Path(relative).parts)
            path.mkdir(mode=0o755)
            if not member.mode & 0o111:
                raise PreparationError("Lean toolchain directory mode changed")
        for relative, member in regular_files.items():
            path = destination.joinpath(*Path(relative).parts)
            source = bundle.extractfile(member)
            if source is None:
                raise PreparationError("unable to read Lean toolchain archive member")
            with source, path.open("xb") as output:
                shutil.copyfileobj(source, output, length=1024 * 1024)
            metadata = path.lstat()
            if (
                not stat.S_ISREG(metadata.st_mode)
                or metadata.st_nlink != 1
                or metadata.st_size != member.size
            ):
                raise PreparationError("Lean toolchain member extraction was truncated")
            path.chmod(0o555 if member.mode & 0o111 else 0o444)
        for relative, member in symlinks.items():
            destination.joinpath(*Path(relative).parts).symlink_to(member.linkname)
    destination.chmod(0o555)


def prefetch_locked_lean_toolchain(
    *,
    curl_bin: Path,
    zstd_bin: Path,
    destination: Path,
    pins: Mapping[str, Any],
    recorder: list[CommandRecord],
) -> tuple[Path, dict[str, Any]]:
    """Bound, authenticate, extract, and verify the pinned official toolchain."""

    toolchain = pins.get("lean")
    pinned = toolchain.get("toolchain") if isinstance(toolchain, Mapping) else None
    if pinned != SUPPORTED_LEAN_TOOLCHAIN:
        raise PreparationError("Lean toolchain is not covered by the tracked lock")
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise PreparationError(
            "the locked Lean toolchain currently supports Linux x86_64 only"
        )
    archive = destination.parent / "lean-toolchain.tar.zst"
    uncompressed = destination.parent / "lean-toolchain.tar"
    download = download_https_file(
        curl_bin=curl_bin,
        url=LEAN_TOOLCHAIN_ARCHIVE_URL,
        destination=archive,
        maximum_bytes=LEAN_TOOLCHAIN_ARCHIVE_BYTES,
        recorder=recorder,
    )
    if (
        download["size"] != LEAN_TOOLCHAIN_ARCHIVE_BYTES
        or download["sha256"] != LEAN_TOOLCHAIN_ARCHIVE_SHA256
    ):
        raise PreparationError("Lean toolchain release archive differs from the lock")
    run_command(
        [
            os.fspath(zstd_bin),
            "--decompress",
            "--force",
            "--quiet",
            "-o",
            os.fspath(uncompressed),
            os.fspath(archive),
        ],
        timeout=1860.0,
        recorder=recorder,
        file_size_limit_bytes=MAX_LEAN_TOOLCHAIN_TAR_BYTES,
    )
    metadata = uncompressed.lstat()
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_nlink != 1
        or metadata.st_size <= LEAN_TOOLCHAIN_INTEGRITY["regular_file_bytes"]
        or metadata.st_size > MAX_LEAN_TOOLCHAIN_TAR_BYTES
    ):
        raise PreparationError("decompressed Lean toolchain tar is invalid")
    extract_locked_lean_toolchain(archive=uncompressed, destination=destination)
    private_record = verify_locked_lean_toolchain(
        destination, label="private prefetched Lean toolchain"
    )
    archive.unlink()
    uncompressed.unlink()
    private_record.update(
        {
            "phase": "completed-before-first-lake-process",
            "archive_download_observed": True,
            "archive_authenticated_before_extraction": True,
            "archive_kernel_file_size_limit_bytes": download[
                "kernel_file_size_limit_bytes"
            ],
            "decompressed_tar_kernel_file_size_limit_bytes": (
                MAX_LEAN_TOOLCHAIN_TAR_BYTES
            ),
            "private_copy": True,
            "source_tree_not_mounted": True,
            "lake_relative_path": "lean-toolchain/bin/lake",
            "lean_relative_path": "lean-toolchain/bin/lean",
        }
    )
    return destination / "bin" / "lake", private_record


def _fchmod_verified_path(
    path: Path, metadata: os.stat_result, mode: int, *, label: str
) -> None:
    """Change mode through a no-follow FD pinned to the lstat'd inode."""

    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    if stat.S_ISDIR(metadata.st_mode):
        flags |= os.O_DIRECTORY
    try:
        descriptor = os.open(path, flags)
        path_only = False
    except PermissionError:
        try:
            descriptor = os.open(path, os.O_PATH | os.O_CLOEXEC | os.O_NOFOLLOW)
            path_only = True
        except OSError as error:
            raise PreparationError(f"cannot securely open {label}: {path}") from error
    except OSError as error:
        raise PreparationError(f"cannot securely open {label}: {path}") from error
    try:
        opened = os.fstat(descriptor)
        if opened.st_dev != metadata.st_dev or opened.st_ino != metadata.st_ino:
            raise PreparationError(f"{label} changed during mode update: {path}")
        if path_only:
            os.chmod(Path("/proc/self/fd") / str(descriptor), mode)
        else:
            os.fchmod(descriptor, mode)
    finally:
        os.close(descriptor)


def seal_read_only(root: Path) -> None:
    paths: list[Path] = []
    for directory, directory_names, file_names in os.walk(root, topdown=False):
        base = Path(directory)
        paths.extend(base / name for name in file_names)
        paths.extend(base / name for name in directory_names)
    paths.append(root)
    for path in paths:
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            continue
        _fchmod_verified_path(
            path,
            metadata,
            stat.S_IMODE(metadata.st_mode) & ~0o222,
            label="cache entry",
        )


def assert_read_only(root: Path) -> None:
    for directory, directory_names, file_names in os.walk(root):
        for name in [*directory_names, *file_names]:
            path = Path(directory) / name
            metadata = path.lstat()
            if not stat.S_ISLNK(metadata.st_mode) and metadata.st_mode & 0o222:
                raise PreparationError(f"immutable cache has writable entry: {path}")
    if root.lstat().st_mode & 0o222:
        raise PreparationError(f"immutable cache root is writable: {root}")


def write_json_atomic(path: Path, value: Mapping[str, Any], *, mode: int = 0o600) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = canonical_json_bytes(value)
    temporary = path.parent / f".{path.name}.{uuid.uuid4().hex}.tmp"
    try:
        with temporary.open("xb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()
    return sha256_bytes(payload)


def load_state(path: Path) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise PreparationError(f"immutable cache state is missing: {path}")
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise PreparationError(f"invalid immutable cache state: {path}") from error
    if not isinstance(state, dict):
        raise PreparationError(f"invalid immutable cache state object: {path}")
    if path.lstat().st_mode & 0o222:
        raise PreparationError(f"immutable cache state is writable: {path}")
    return state


def state_matches(
    state: Mapping[str, Any],
    repository: str,
    commit: str,
    source_integrity: Mapping[str, Any],
    mathlib_source_integrity: Mapping[str, Any],
    build_integrity: Mapping[str, Any] | None,
    derived_mathlib_integrity: Mapping[str, Any] | None,
) -> None:
    expected = {
        "cache_format_version": CACHE_FORMAT_VERSION,
        "repository": display_repository(repository),
        "ref": NUMSTABILITY_REF,
        "commit": commit,
    }
    for key, value in expected.items():
        if state.get(key) != value:
            raise PreparationError(
                f"immutable cache state mismatch for {key}: {state.get(key)!r} != {value!r}"
            )
    paths = state.get("paths")
    build_record = state.get("build")
    pins_record = state.get("pins")
    lake_record = pins_record.get("lake") if isinstance(pins_record, Mapping) else None
    built = bool(build_record.get("performed")) if isinstance(
        build_record, Mapping
    ) else False
    packages_directory = (
        lake_record.get("packages_directory")
        if isinstance(lake_record, Mapping)
        else None
    )
    expected_paths = {
        "pristine_numstability_source": "source",
        "pristine_mathlib_source": "mathlib-source",
        "derived_numstability_build": "build" if built else None,
        "derived_mathlib_package": (
            (Path("build") / str(packages_directory) / "mathlib").as_posix()
            if built
            else None
        ),
    }
    if paths != expected_paths:
        raise PreparationError("immutable cache path contract was tampered")
    expected_provenance = {
        "derived_numstability_independently_cloned": True,
        "lake_working_directory": "build",
        "all_network_inputs_prefetched_before_first_lake": True,
        "lake_network_egress": "none",
        "lake_commands_completed_before_pristine_checkouts_created": True,
        "pristine_sources_cloned_from_prefetch_after_lake": True,
        "no_lake_commands_after_pristine_checkouts_created": True,
    }
    if state.get("provenance") != expected_provenance:
        raise PreparationError("immutable cache chronology/provenance was tampered")
    if state.get("preparation_isolation") != PREPARATION_ISOLATION:
        raise PreparationError("immutable cache preparation isolation was tampered")
    tools_record = state.get("tools")
    if (
        not isinstance(tools_record, Mapping)
        or tools_record.get("lake_network") != "offline-private-unshare"
    ):
        raise PreparationError("immutable cache Lake network contract was tampered")
    prefetch = state.get("prefetch")
    if (
        not isinstance(prefetch, Mapping)
        or prefetch.get("completed_before_first_lake_process") is not True
        or not isinstance(prefetch.get("dependency_sources"), list)
    ):
        raise PreparationError("immutable cache prefetch record was tampered")
    dependency_records = prefetch["dependency_sources"]
    pinned_dependencies = (
        pins_record.get("dependencies")
        if isinstance(pins_record, Mapping)
        else None
    )
    if (
        not isinstance(pinned_dependencies, list)
        or len(dependency_records) != len(pinned_dependencies)
        or not all(isinstance(record, Mapping) for record in dependency_records)
        or not all(isinstance(dependency, Mapping) for dependency in pinned_dependencies)
        or [
        (record.get("name"), record.get("repository"), record.get("commit"))
        for record in dependency_records
        ] != [
        (dependency.get("name"), dependency.get("repository"), dependency.get("commit"))
        for dependency in pinned_dependencies
        ]
    ):
        raise PreparationError("immutable cache dependency prefetch pins were tampered")
    lean_toolchain_prefetch = prefetch.get("lean_toolchain")
    if (
        not isinstance(lean_toolchain_prefetch, Mapping)
        or lean_toolchain_prefetch.get("phase")
        != "completed-before-first-lake-process"
        or lean_toolchain_prefetch.get("toolchain")
        != SUPPORTED_LEAN_TOOLCHAIN
        or lean_toolchain_prefetch.get("archive_url")
        != LEAN_TOOLCHAIN_ARCHIVE_URL
        or lean_toolchain_prefetch.get("archive_size")
        != LEAN_TOOLCHAIN_ARCHIVE_BYTES
        or lean_toolchain_prefetch.get("archive_sha256")
        != LEAN_TOOLCHAIN_ARCHIVE_SHA256
        or lean_toolchain_prefetch.get("integrity")
        != LEAN_TOOLCHAIN_INTEGRITY
        or lean_toolchain_prefetch.get("lake_sha256")
        != LEAN_TOOLCHAIN_LAKE_SHA256
        or lean_toolchain_prefetch.get("lean_sha256")
        != LEAN_TOOLCHAIN_LEAN_SHA256
        or lean_toolchain_prefetch.get("private_copy") is not True
        or lean_toolchain_prefetch.get("source_tree_not_mounted") is not True
        or lean_toolchain_prefetch.get("archive_download_observed") is not True
        or lean_toolchain_prefetch.get("archive_authenticated_before_extraction")
        is not True
        or lean_toolchain_prefetch.get("archive_kernel_file_size_limit_bytes")
        != LEAN_TOOLCHAIN_ARCHIVE_BYTES
        or lean_toolchain_prefetch.get(
            "decompressed_tar_kernel_file_size_limit_bytes"
        )
        != MAX_LEAN_TOOLCHAIN_TAR_BYTES
    ):
        raise PreparationError("immutable cache Lean toolchain prefetch was tampered")
    binary_prefetch = prefetch.get("binary_cache")
    if built:
        commit_manifest = (
            binary_prefetch.get("mathlib_commit_manifest")
            if isinstance(binary_prefetch, Mapping)
            else None
        )
        artifacts = (
            binary_prefetch.get("mathlib_ltar_artifacts")
            if isinstance(binary_prefetch, Mapping)
            else None
        )
        leantar = (
            binary_prefetch.get("leantar")
            if isinstance(binary_prefetch, Mapping)
            else None
        )
        proofwidgets = (
            binary_prefetch.get("proofwidgets_release")
            if isinstance(binary_prefetch, Mapping)
            else None
        )
        download_safety = (
            binary_prefetch.get("mathlib_ltar_download_safety")
            if isinstance(binary_prefetch, Mapping)
            else None
        )
        if (
            commit_manifest != MATHLIB_COMMIT_MANIFEST_RECORD
            or not isinstance(artifacts, Mapping)
            or artifacts.get("count") != MATHLIB_CACHE_ARTIFACT_COUNT
            or artifacts.get("total_bytes") != MATHLIB_CACHE_ARTIFACT_BYTES
            or artifacts.get("content_manifest_sha256")
            != MATHLIB_CACHE_ARTIFACT_MANIFEST_SHA256
            or binary_prefetch.get("post_lake_artifact_verification") != artifacts
            or not isinstance(leantar, Mapping)
            or leantar.get("version") != LEANTAR_VERSION
            or leantar.get("binary_sha256") != LEANTAR_BINARY_SHA256
            or not isinstance(proofwidgets, Mapping)
            or proofwidgets.get("commit") != SUPPORTED_PROOFWIDGETS_COMMIT
            or proofwidgets.get("sha256") != PROOFWIDGETS_RELEASE_SHA256
            or download_safety
            != {
                "kernel_file_size_limit_each_curl_process": True,
                "remaining_aggregate_bound_applied_before_each_batch": True,
                "maximum_aggregate_bytes": MAX_CACHE_TOTAL_BYTES,
            }
        ):
            raise PreparationError("immutable cache binary prefetch lock was tampered")
    elif binary_prefetch is not None:
        raise PreparationError("no-build cache unexpectedly records binary prefetch")
    pristine = state.get("pristine_sources")
    if not isinstance(pristine, Mapping):
        raise PreparationError("immutable cache has no pristine source records")
    pristine_numstability = pristine.get("numstability")
    pristine_mathlib = pristine.get("mathlib")
    if not isinstance(pristine_numstability, Mapping) or not isinstance(
        pristine_mathlib, Mapping
    ):
        raise PreparationError("immutable cache pristine source records are invalid")
    if (
        state.get("source_integrity") != source_integrity
        or pristine_numstability.get("integrity") != source_integrity
    ):
        raise PreparationError(
            "pristine source cache digest does not match its state"
        )
    if pristine_mathlib.get("integrity") != mathlib_source_integrity:
        raise PreparationError(
            "pristine Mathlib source cache digest does not match its state"
        )
    expected_numstability_metadata = {
        "repository": display_repository(repository),
        "commit": commit,
        "git_tree": state.get("git_tree"),
        "relative_path": "source",
        "detached": True,
        "clean": True,
        "read_only": True,
        "lake_directory_absent": True,
        "integrity": source_integrity,
    }
    mathlib_pin = (
        pins_record.get("mathlib") if isinstance(pins_record, Mapping) else None
    )
    if not isinstance(mathlib_pin, Mapping):
        raise PreparationError("immutable cache has no Mathlib pin")
    expected_mathlib_metadata = {
        "repository": mathlib_pin.get("repository"),
        "commit": mathlib_pin.get("commit"),
        "git_tree": pristine_mathlib.get("git_tree"),
        "relative_path": "mathlib-source",
        "detached": True,
        "clean": True,
        "read_only": True,
        "lake_directory_absent": True,
        "integrity": mathlib_source_integrity,
    }
    if pristine_numstability != expected_numstability_metadata:
        raise PreparationError("pristine NumStability provenance was tampered")
    if pristine_mathlib != expected_mathlib_metadata:
        raise PreparationError("pristine Mathlib provenance was tampered")
    build = state.get("build")
    if not isinstance(build, Mapping) or build.get("integrity") != build_integrity:
        raise PreparationError(
            "derived build cache digest does not match its state"
        )
    derived_mathlib = build.get("mathlib_package")
    if derived_mathlib_integrity is None:
        if derived_mathlib is not None:
            raise PreparationError("unexpected derived Mathlib package state")
    elif (
        not isinstance(derived_mathlib, Mapping)
        or derived_mathlib.get("integrity") != derived_mathlib_integrity
    ):
        raise PreparationError("derived Mathlib package digest does not match its state")
    if derived_mathlib_integrity is not None:
        expected_derived_mathlib = {
            "repository": mathlib_pin.get("repository"),
            "commit": mathlib_pin.get("commit"),
            "git_tree": pristine_mathlib.get("git_tree"),
            "relative_path": expected_paths["derived_mathlib_package"],
            "detached": True,
            "clean": True,
            "read_only": True,
            "derived": True,
            "integrity": derived_mathlib_integrity,
        }
        if derived_mathlib != expected_derived_mathlib:
            raise PreparationError("derived Mathlib package provenance was tampered")


def make_state(
    *,
    repository: str,
    commit: str,
    git_tree: str,
    mathlib_git_tree: str,
    pins: Mapping[str, Any],
    tool_versions: Mapping[str, Any],
    source_integrity: Mapping[str, Any],
    mathlib_source_integrity: Mapping[str, Any],
    build_integrity: Mapping[str, Any] | None,
    derived_mathlib_integrity: Mapping[str, Any] | None,
    derived_mathlib_git_tree: str | None,
    build_performed: bool,
    build_commands: Sequence[Sequence[str]],
    mathlib_materialized: bool,
    prefetch: Mapping[str, Any],
) -> dict[str, Any]:
    derived_mathlib_path = (
        (
            Path("build")
            / str(pins["lake"]["packages_directory"])
            / "mathlib"
        ).as_posix()
        if build_performed
        else None
    )
    return {
        "cache_format_version": CACHE_FORMAT_VERSION,
        "created_at": utc_now(),
        "repository": display_repository(repository),
        "ref": NUMSTABILITY_REF,
        "commit": commit,
        "git_tree": git_tree,
        "detached": True,
        "read_only": True,
        "source_integrity": source_integrity,
        "paths": {
            "pristine_numstability_source": "source",
            "pristine_mathlib_source": "mathlib-source",
            "derived_numstability_build": "build" if build_performed else None,
            "derived_mathlib_package": derived_mathlib_path,
        },
        "provenance": {
            "derived_numstability_independently_cloned": True,
            "lake_working_directory": "build",
            "all_network_inputs_prefetched_before_first_lake": True,
            "lake_network_egress": "none",
            "lake_commands_completed_before_pristine_checkouts_created": True,
            "pristine_sources_cloned_from_prefetch_after_lake": True,
            "no_lake_commands_after_pristine_checkouts_created": True,
        },
        "preparation_isolation": dict(PREPARATION_ISOLATION),
        "prefetch": dict(prefetch),
        "pristine_sources": {
            "numstability": {
                "repository": display_repository(repository),
                "commit": commit,
                "git_tree": git_tree,
                "relative_path": "source",
                "detached": True,
                "clean": True,
                "read_only": True,
                "lake_directory_absent": True,
                "integrity": source_integrity,
            },
            "mathlib": {
                "repository": pins["mathlib"]["repository"],
                "commit": pins["mathlib"]["commit"],
                "git_tree": mathlib_git_tree,
                "relative_path": "mathlib-source",
                "detached": True,
                "clean": True,
                "read_only": True,
                "lake_directory_absent": True,
                "integrity": mathlib_source_integrity,
            },
        },
        "pins": pins,
        "tools": tool_versions,
        "build": {
            "performed": build_performed,
            "commands": [list(command) for command in build_commands],
            "integrity": build_integrity,
            "relative_path": "build" if build_performed else None,
            "derived_numstability_independently_cloned": True,
            "source_checkout_was_never_build_working_directory": True,
            "mathlib_materialized": mathlib_materialized,
            "mathlib_package": (
                {
                    "repository": pins["mathlib"]["repository"],
                    "commit": pins["mathlib"]["commit"],
                    "git_tree": derived_mathlib_git_tree,
                    "relative_path": derived_mathlib_path,
                    "detached": True,
                    "clean": True,
                    "read_only": True,
                    "derived": True,
                    "integrity": derived_mathlib_integrity,
                }
                if build_performed
                else None
            ),
            "tracked_sources_unchanged_after_build": True,
            "lookup_compiler_check_passed": build_performed,
        },
    }


def make_owner_writable(root: Path) -> None:
    """Make a private, uninstalled staging tree removable after a failure."""

    if not root.exists() or root.is_symlink():
        return
    for directory, directory_names, file_names in os.walk(root):
        for name in [*directory_names, *file_names]:
            path = Path(directory) / name
            metadata = path.lstat()
            if not stat.S_ISLNK(metadata.st_mode):
                owner_access = stat.S_IRUSR | stat.S_IWUSR
                if stat.S_ISDIR(metadata.st_mode):
                    owner_access |= stat.S_IXUSR
                _fchmod_verified_path(
                    path,
                    metadata,
                    stat.S_IMODE(metadata.st_mode) | owner_access,
                    label="staging entry",
                )
    root_metadata = root.lstat()
    _fchmod_verified_path(
        root,
        root_metadata,
        stat.S_IMODE(root_metadata.st_mode) | stat.S_IWUSR,
        label="staging root",
    )


@contextlib.contextmanager
def secure_prepare_lock(path: Path) -> Iterable[int]:
    """Open the private cache lock without following or sharing an inode."""

    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_CLOEXEC"):
        raise PreparationError("secure cache-lock open flags are unavailable")
    directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    flags = os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC
    try:
        parent_descriptor = os.open(path.parent, directory_flags)
    except OSError as error:
        raise PreparationError(
            f"cannot securely open cache preparation lock directory: {path.parent}"
        ) from error
    try:
        try:
            descriptor = os.open(path.name, flags, 0o600, dir_fd=parent_descriptor)
        except OSError as error:
            raise PreparationError(
                f"cannot securely open cache preparation lock: {path}"
            ) from error
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX)
            status = os.fstat(descriptor)
            pathname_status = os.stat(
                path.name, dir_fd=parent_descriptor, follow_symlinks=False
            )
            if (
                not stat.S_ISREG(status.st_mode)
                or status.st_uid != os.getuid()
                or stat.S_IMODE(status.st_mode) & 0o077
                or status.st_nlink != 1
                or pathname_status.st_dev != status.st_dev
                or pathname_status.st_ino != status.st_ino
            ):
                raise PreparationError(
                    "cache preparation lock must be a private, linked, "
                    "user-owned regular file"
                )
            yield descriptor
        finally:
            os.close(descriptor)
    finally:
        os.close(parent_descriptor)


def prepare_cache(
    *,
    namespace: Path,
    repository: str,
    commit: str,
    git_bin: Path,
    unshare_bin: Path,
    bwrap_bin: Path,
    curl_bin: Path,
    zstd_bin: Path,
    explicit_local_dependency_mirrors: Sequence[Path],
    no_build: bool,
    build_timeout_seconds: float,
    recorder: list[CommandRecord],
) -> tuple[Path, Path, Path | None, dict[str, Any], bool]:
    namespace.mkdir(parents=True, exist_ok=True)
    if namespace.is_symlink():
        raise PreparationError("cache namespace must not be a symbolic link")
    format_namespace = require_external_private_directory(
        namespace / f"format-{CACHE_FORMAT_VERSION}",
        label="cache format namespace",
        git_bin=git_bin,
        create=True,
    )
    entry = format_namespace / commit
    state_path = entry / "state.json"
    lock_path = namespace / ".prepare.lock"

    with secure_prepare_lock(lock_path):
        if entry.exists() or entry.is_symlink():
            if entry.is_symlink() or not entry.is_dir():
                raise PreparationError(f"invalid immutable cache entry: {entry}")
            state = load_state(state_path)
            assert_read_only(entry)
            source = entry / "source"
            mathlib_source = entry / "mathlib-source"
            if source.is_symlink() or not source.is_dir():
                raise PreparationError("immutable cache has no pristine source tree")
            if mathlib_source.is_symlink() or not mathlib_source.is_dir():
                raise PreparationError(
                    "immutable cache has no pristine Mathlib source tree"
                )
            assert_disjoint_trees(source, mathlib_source)
            assert_no_hardlinked_regular_files(
                source, label="NumStability pristine source"
            )
            assert_no_hardlinked_regular_files(
                mathlib_source, label="Mathlib pristine source"
            )
            assert_no_lake_directory(
                source, label="NumStability"
            )
            assert_no_lake_directory(mathlib_source, label="Mathlib")
            git_tree = assert_clean_detached_checkout(
                source,
                git_bin,
                commit,
                label="NumStability pristine source",
                include_ignored=True,
            )
            pins = inspect_upstream_pins(source)
            authorize_prefetch_sources(
                repository, pins, explicit_local_dependency_mirrors
            )
            mathlib_git_tree = assert_clean_detached_checkout(
                mathlib_source,
                git_bin,
                pins["mathlib"]["commit"],
                label="Mathlib pristine source",
                include_ignored=True,
            )
            pristine_records = state.get("pristine_sources")
            mathlib_record = (
                pristine_records.get("mathlib")
                if isinstance(pristine_records, Mapping)
                else None
            )
            if (
                state.get("git_tree") != git_tree
                or state.get("pins") != pins
                or not isinstance(mathlib_record, Mapping)
                or mathlib_record.get("git_tree") != mathlib_git_tree
            ):
                raise PreparationError("pristine source cache metadata was tampered")
            source_integrity = cache_integrity(source)
            mathlib_source_integrity = cache_integrity(mathlib_source)
            state_build = state.get("build")
            if not isinstance(state_build, Mapping):
                raise PreparationError("immutable cache has no derived build record")
            built = bool(state_build.get("performed"))
            if not no_build and not built:
                raise PreparationError(
                    "immutable cache was prepared with --no-build; use an empty external "
                    "cache root for a built snapshot"
                )
            build = entry / "build" if built else None
            if build is not None and (build.is_symlink() or not build.is_dir()):
                raise PreparationError("immutable cache has no derived build tree")
            if build is not None:
                assert_disjoint_trees(source, mathlib_source, build)
            build_integrity = cache_integrity(build) if build is not None else None
            mathlib_checkout: Path | None = None
            derived_mathlib_integrity: Mapping[str, Any] | None = None
            if build is None:
                state_matches(
                    state,
                    repository,
                    commit,
                    source_integrity,
                    mathlib_source_integrity,
                    build_integrity,
                    None,
                )
                recorded_tools = state.get("tools")
                if not isinstance(recorded_tools, Mapping):
                    raise PreparationError("immutable cache has no builder identity")
                verify_cached_builder_tools(
                    unshare_bin,
                    bwrap_bin,
                    curl_bin,
                    zstd_bin,
                    recorded_tools,
                )
                return source, mathlib_source, None, state, True
            build_tree = assert_clean_detached_checkout(
                build, git_bin, commit, label="NumStability derived build"
            )
            if build_tree != git_tree or inspect_upstream_pins(build) != pins:
                raise PreparationError("derived build sources differ from pristine source")
            mathlib_checkout = verify_mathlib_checkout(
                build, git_bin, pins, required=True
            )
            if mathlib_checkout is None:
                raise PreparationError("built cache has no pinned mathlib checkout")
            derived_mathlib_tree = assert_clean_detached_checkout(
                mathlib_checkout,
                git_bin,
                pins["mathlib"]["commit"],
                label="derived Mathlib package",
            )
            if derived_mathlib_tree != mathlib_git_tree:
                raise PreparationError(
                    "derived and pristine Mathlib trees do not match"
                )
            derived_mathlib_integrity = cache_integrity(mathlib_checkout)
            state_matches(
                state,
                repository,
                commit,
                source_integrity,
                mathlib_source_integrity,
                build_integrity,
                derived_mathlib_integrity,
            )
            verify_paper_required_library_modules(build)
            recorded_tools = state.get("tools")
            if not isinstance(recorded_tools, Mapping):
                raise PreparationError("immutable cache has no builder identity")
            verify_cached_builder_tools(
                unshare_bin,
                bwrap_bin,
                curl_bin,
                zstd_bin,
                recorded_tools,
            )
            prefetch_record = state.get("prefetch")
            if not isinstance(prefetch_record, Mapping) or not isinstance(
                prefetch_record.get("dependency_sources"), list
            ):
                raise PreparationError("immutable cache has no dependency prefetch record")
            verify_prefetched_dependency_sources(
                checkout=build,
                pins=pins,
                records=prefetch_record["dependency_sources"],
                git_bin=git_bin,
            )
            return source, mathlib_source, build, state, True

        staging = format_namespace / f".tmp-{commit}-{uuid.uuid4().hex}"
        source_staging = staging / "source"
        mathlib_source_staging = staging / "mathlib-source"
        build_staging = staging / "build"
        source_prefetch_root = staging / ".source-prefetch"
        numstability_prefetch = source_prefetch_root / "numstability"
        dependency_prefetch_root = source_prefetch_root / "packages"
        lean_toolchain_prefetch = source_prefetch_root / "lean-toolchain"
        build_commands: list[list[str]] = []
        try:
            staging.mkdir(mode=0o700)
            source_prefetch_root.mkdir(mode=0o700)
            # Download the locked root once into a private source store that is
            # never mounted into Lake. Both the disposable build and the later
            # pristine checkout are independent local clones of this store.
            clone_detached(
                numstability_prefetch, git_bin, repository, commit, recorder
            )
            assert_no_special_files(
                numstability_prefetch, label="prefetched NumStability source"
            )
            assert_no_hardlinked_regular_files(
                numstability_prefetch, label="prefetched NumStability source"
            )
            prefetched_numstability_tree = assert_clean_detached_checkout(
                numstability_prefetch,
                git_bin,
                commit,
                label="prefetched NumStability source",
                include_ignored=True,
            )
            numstability_prefetch_git_integrity = cache_integrity(
                numstability_prefetch / ".git"
            )
            clone_detached(
                build_staging,
                git_bin,
                os.fspath(numstability_prefetch),
                commit,
                recorder,
            )
            derived_git_tree = assert_clean_detached_checkout(
                build_staging, git_bin, commit, label="NumStability derived build"
            )
            if derived_git_tree != prefetched_numstability_tree:
                raise PreparationError(
                    "derived NumStability tree differs from its source prefetch"
                )
            derived_git_metadata_integrity = cache_integrity(
                build_staging / ".git"
            )
            pins = inspect_upstream_pins(build_staging)
            # This validates operator authorization for local mirrors. The
            # returned paths are deliberately not mounted into Lake.
            authorize_prefetch_sources(
                repository, pins, explicit_local_dependency_mirrors
            )
            dependency_source_records = prefetch_dependency_sources(
                source_store=dependency_prefetch_root,
                checkout=build_staging,
                pins=pins,
                git_bin=git_bin,
                recorder=recorder,
            )
            read_only_checkout_git_directories = (
                derived_git_administrative_directories(build_staging, pins)
            )
            prefetched_lake_bin, lean_toolchain_record = (
                prefetch_locked_lean_toolchain(
                    curl_bin=curl_bin,
                    zstd_bin=zstd_bin,
                    destination=lean_toolchain_prefetch,
                    pins=pins,
                    recorder=recorder,
                )
            )
            lake_sandbox = create_lake_sandbox_directory(build_staging)
            binary_cache_record: dict[str, Any] | None = None
            binary_cache_filenames: list[str] = []
            try:
                if not no_build:
                    binary_cache_record, binary_cache_filenames = prefetch_binary_cache(
                        checkout=build_staging,
                        sandbox=lake_sandbox,
                        pins=pins,
                        curl_bin=curl_bin,
                        recorder=recorder,
                    )
                tool_versions = verify_tool_versions(
                    build_staging,
                    prefetched_lake_bin,
                    unshare_bin,
                    bwrap_bin,
                    curl_bin,
                    zstd_bin,
                    lake_sandbox,
                    pins,
                    read_only_checkout_git_directories,
                    lean_toolchain_record,
                    recorder,
                )
                if not no_build:
                    build_commands = [
                        [
                            "private-prefetch/lean-toolchain/bin/lake",
                            "exe",
                            "cache",
                            "--skip-proofwidgets",
                            "get",
                        ],
                        [
                            "private-prefetch/lean-toolchain/bin/lake",
                            "build",
                            "NumStability",
                        ],
                        [
                            "private-prefetch/lean-toolchain/bin/lake",
                            "build",
                            *PAPER_REQUIRED_LIBRARY_MODULES,
                        ],
                        [
                            "private-prefetch/lean-toolchain/bin/lake",
                            "env",
                            "lean",
                            os.fspath(LIBRARY_LOOKUP_CHECK),
                        ],
                    ]
                    for build_command in build_commands:
                        run_offline_lake(
                            build_command[1:],
                            checkout=build_staging,
                            sandbox=lake_sandbox,
                            unshare_bin=unshare_bin,
                            bwrap_bin=bwrap_bin,
                            lake_bin=prefetched_lake_bin,
                            read_only_checkout_git_directories=(
                                read_only_checkout_git_directories
                            ),
                            timeout=build_timeout_seconds,
                            recorder=recorder,
                        )
                    verify_paper_required_library_modules(build_staging)
                    if binary_cache_record is None:
                        raise PreparationError("built runtime has no binary-cache prefetch")
                    binary_cache_record["post_lake_artifact_verification"] = (
                        verify_mathlib_cache_artifacts(
                            cache_directory=lake_sandbox / "cache" / "mathlib",
                            filenames=binary_cache_filenames,
                        )
                    )
            finally:
                remove_lake_sandbox_directory(lake_sandbox)
            if (
                cache_integrity(build_staging / ".git")
                != derived_git_metadata_integrity
            ):
                raise PreparationError(
                    "Lake changed derived NumStability Git administrative metadata"
                )
            post_build_tree = assert_clean_detached_checkout(
                build_staging,
                git_bin,
                commit,
                label="NumStability derived build",
            )
            if (
                post_build_tree != derived_git_tree
                or inspect_upstream_pins(build_staging) != pins
            ):
                raise PreparationError("Lake changed pinned NumStability sources")
            verify_prefetched_dependency_sources(
                checkout=build_staging,
                pins=pins,
                records=dependency_source_records,
                git_bin=git_bin,
            )
            if verify_locked_lean_toolchain(
                lean_toolchain_prefetch,
                label="private prefetched Lean toolchain after Lake",
            ) != {
                key: value
                for key, value in lean_toolchain_record.items()
                if key
                in {
                    "toolchain",
                    "archive_url",
                    "archive_size",
                    "archive_sha256",
                    "integrity",
                    "lake_sha256",
                    "lean_sha256",
                }
            }:
                raise PreparationError("offline Lake changed its Lean toolchain")
            derived_mathlib_checkout = verify_mathlib_checkout(
                build_staging, git_bin, pins, required=True
            )
            derived_mathlib_git_tree = (
                assert_clean_detached_checkout(
                    derived_mathlib_checkout,
                    git_bin,
                    pins["mathlib"]["commit"],
                    label="derived Mathlib package",
                )
                if derived_mathlib_checkout is not None
                else None
            )

            # There must be no Lake execution below this point. Create each
            # pristine source from the already-verified private prefetch stores;
            # no remote fetch is permitted after the first Lake process.
            if source_staging.exists() or source_staging.is_symlink():
                raise PreparationError(
                    "Lake activity created the planned pristine NumStability path"
                )
            if mathlib_source_staging.exists() or mathlib_source_staging.is_symlink():
                raise PreparationError(
                    "Lake activity created the planned pristine Mathlib path"
                )
            if cache_integrity(
                numstability_prefetch / ".git"
            ) != numstability_prefetch_git_integrity:
                raise PreparationError("NumStability source prefetch was changed")
            if assert_clean_detached_checkout(
                numstability_prefetch,
                git_bin,
                commit,
                label="prefetched NumStability source after Lake",
                include_ignored=True,
            ) != prefetched_numstability_tree:
                raise PreparationError("NumStability source prefetch tree changed")
            clone_detached(
                source_staging,
                git_bin,
                os.fspath(numstability_prefetch),
                commit,
                recorder,
            )
            assert_no_hardlinked_regular_files(
                source_staging, label="NumStability pristine source"
            )
            git_tree = assert_clean_detached_checkout(
                source_staging,
                git_bin,
                commit,
                label="NumStability pristine source",
                include_ignored=True,
            )
            if git_tree != derived_git_tree or inspect_upstream_pins(source_staging) != pins:
                raise PreparationError(
                    "independent pristine NumStability clone differs from derived source"
                )
            assert_no_lake_directory(source_staging, label="NumStability")
            mathlib_prefetch = dependency_prefetch_root / "mathlib"
            mathlib_prefetch_record = next(
                (
                    record
                    for record in dependency_source_records
                    if record.get("name") == "mathlib"
                ),
                None,
            )
            if mathlib_prefetch_record is None:
                raise PreparationError("Mathlib source prefetch record is missing")
            if cache_integrity(mathlib_prefetch / ".git") != mathlib_prefetch_record.get(
                "source_store_git_integrity"
            ):
                raise PreparationError("Mathlib source prefetch was changed")
            if assert_clean_detached_checkout(
                mathlib_prefetch,
                git_bin,
                pins["mathlib"]["commit"],
                label="prefetched Mathlib source after Lake",
                include_ignored=True,
            ) != mathlib_prefetch_record.get("git_tree"):
                raise PreparationError("Mathlib source prefetch tree changed")
            clone_detached(
                mathlib_source_staging,
                git_bin,
                os.fspath(mathlib_prefetch),
                str(pins["mathlib"]["commit"]),
                recorder,
            )
            assert_no_hardlinked_regular_files(
                mathlib_source_staging, label="Mathlib pristine source"
            )
            mathlib_git_tree = assert_clean_detached_checkout(
                mathlib_source_staging,
                git_bin,
                pins["mathlib"]["commit"],
                label="Mathlib pristine source",
                include_ignored=True,
            )
            assert_no_lake_directory(mathlib_source_staging, label="Mathlib")
            if (
                derived_mathlib_git_tree is not None
                and mathlib_git_tree != derived_mathlib_git_tree
            ):
                raise PreparationError(
                    "independent pristine Mathlib clone differs from derived package"
                )
            assert_disjoint_trees(
                source_staging, mathlib_source_staging, build_staging
            )
            first_lake_index = next(
                (
                    index
                    for index, record in enumerate(recorder)
                    if record.role == "lake-bwrap-offline-network"
                ),
                None,
            )
            if first_lake_index is None:
                raise PreparationError("preparation did not record an offline Lake process")
            for record in recorder[first_lake_index + 1 :]:
                if (
                    (record.argv and record.argv[0] == os.fspath(curl_bin))
                    or any(argument.startswith("https://") for argument in record.argv)
                    or (
                        "toolchain" in record.argv
                        and "install" in record.argv
                    )
                ):
                    raise PreparationError(
                        "remote-capable download was attempted after Lake began"
                    )
            prefetch_record = {
                "completed_before_first_lake_process": True,
                "remote_downloads_after_first_lake_process": False,
                "lake_network": "offline-private-unshare",
                "local_source_stores_visible_to_lake": False,
                "numstability_source": {
                    "repository": display_repository(repository),
                    "commit": commit,
                    "git_tree": prefetched_numstability_tree,
                    "source_store_git_integrity": (
                        numstability_prefetch_git_integrity
                    ),
                },
                "dependency_sources": dependency_source_records,
                "lean_toolchain": lean_toolchain_record,
                "binary_cache": binary_cache_record,
            }
            # The private download stores are only staging inputs. The two
            # pristine clones above are independent, verified descendants.
            make_owner_writable(source_prefetch_root)
            shutil.rmtree(source_prefetch_root)

            seal_read_only(source_staging)
            seal_read_only(mathlib_source_staging)
            assert_read_only(source_staging)
            assert_read_only(mathlib_source_staging)
            source_integrity = cache_integrity(source_staging)
            mathlib_source_integrity = cache_integrity(mathlib_source_staging)
            build_integrity: Mapping[str, Any] | None = None
            derived_mathlib_integrity: Mapping[str, Any] | None = None
            installed_build: Path | None = None
            if no_build:
                make_owner_writable(build_staging)
                shutil.rmtree(build_staging)
            else:
                seal_read_only(build_staging)
                assert_read_only(build_staging)
                build_integrity = cache_integrity(build_staging)
                if derived_mathlib_checkout is None:
                    raise PreparationError("built cache has no derived Mathlib package")
                derived_mathlib_integrity = cache_integrity(
                    derived_mathlib_checkout
                )
                installed_build = entry / "build"
            state = make_state(
                repository=repository,
                commit=commit,
                git_tree=git_tree,
                mathlib_git_tree=mathlib_git_tree,
                pins=pins,
                tool_versions=tool_versions,
                source_integrity=source_integrity,
                mathlib_source_integrity=mathlib_source_integrity,
                build_integrity=build_integrity,
                derived_mathlib_integrity=derived_mathlib_integrity,
                derived_mathlib_git_tree=derived_mathlib_git_tree,
                build_performed=not no_build,
                build_commands=build_commands,
                mathlib_materialized=(
                    not no_build and derived_mathlib_checkout is not None
                ),
                prefetch=prefetch_record,
            )
            write_json_atomic(staging / "state.json", state, mode=0o444)
            seal_read_only(staging)
            assert_read_only(staging)
            os.replace(staging, entry)
            return (
                entry / "source",
                entry / "mathlib-source",
                installed_build,
                state,
                False,
            )
        finally:
            if staging.exists():
                make_owner_writable(staging)
                shutil.rmtree(staging)


def read_text_if_present(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except (FileNotFoundError, PermissionError, UnicodeDecodeError, OSError):
        return None


def benchmark_git_inventory(repository: Path, git_bin: Path) -> dict[str, Any]:
    assert_nonexecuting_git_config(repository, label="benchmark repository")
    head = git_output(git_bin, repository, "rev-parse", "HEAD")
    tree = git_output(git_bin, repository, "rev-parse", "HEAD^{tree}")
    branch = git_output(git_bin, repository, "rev-parse", "--abbrev-ref", "HEAD")
    status = git_output(
        git_bin,
        repository,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=all",
    )
    index_status = git_output(
        git_bin,
        repository,
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
        "commit": head,
        "git_tree": tree,
        "branch": None if branch == "HEAD" else branch,
        "dirty": bool(status or index_status),
        "status_lines": status_lines,
    }


def runtime_inventory(
    *,
    repository_root_path: Path,
    benchmark_root: Path,
    cache_root: Path,
    output_dir: Path,
    git_bin: Path,
    unshare_bin: Path,
    bwrap_bin: Path,
    curl_bin: Path,
    zstd_bin: Path,
    commands: Sequence[CommandRecord],
) -> dict[str, Any]:
    affinity = (
        sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    )
    uname = platform.uname()
    cgroup_files = {}
    for relative in ["cpu.max", "cpuset.cpus.effective", "memory.max", "memory.high"]:
        value = read_text_if_present(Path("/sys/fs/cgroup") / relative)
        if value is not None:
            cgroup_files[relative] = value
    os_release = read_text_if_present(Path("/etc/os-release"))
    meminfo = read_text_if_present(Path("/proc/meminfo"))
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_at": utc_now(),
        "preparation": {
            "script": {
                "path": os.fspath(Path(__file__).resolve()),
                "sha256": sha256_file(Path(__file__).resolve()),
            },
            "repository_root": os.fspath(repository_root_path),
            "benchmark_root": os.fspath(benchmark_root),
            "external_cache_root": os.fspath(cache_root),
            "output_directory": os.fspath(output_dir),
            "process_id": os.getpid(),
            "commands": [record.as_json() for record in commands],
            "lake_filesystem_isolation": dict(PREPARATION_ISOLATION),
        },
        "benchmark_repository": benchmark_git_inventory(
            repository_root_path, git_bin
        ),
        "host": {
            "platform": platform.platform(),
            "system": uname.system,
            "release": uname.release,
            "version": uname.version,
            "machine": uname.machine,
            "processor": uname.processor,
            "hostname": uname.node,
            "logical_cpu_count": os.cpu_count(),
            "process_cpu_affinity": affinity,
            "os_release": os_release,
            "proc_meminfo": meminfo,
            "cgroup_v2": cgroup_files,
        },
        "python": {
            "executable": os.fspath(Path(sys.executable).resolve()),
            "version": platform.python_version(),
            "implementation": platform.python_implementation(),
        },
        "tools": {
            "git_executable": os.fspath(git_bin),
            "git_executable_sha256": sha256_file(git_bin),
            "git_version": run_command([os.fspath(git_bin), "--version"]).stdout.strip(),
            "bubblewrap_executable": os.fspath(bwrap_bin),
            "bubblewrap_executable_sha256": sha256_file(bwrap_bin),
            "unshare_executable": os.fspath(unshare_bin),
            "unshare_executable_sha256": sha256_file(unshare_bin),
            "curl_executable": os.fspath(curl_bin),
            "curl_executable_sha256": sha256_file(curl_bin),
            "zstd_executable": os.fspath(zstd_bin),
            "zstd_executable_sha256": sha256_file(zstd_bin),
            "lake_network": "offline-private-unshare",
        },
    }


def source_manifest(
    *,
    repository: str,
    commit: str,
    source_checkout: Path,
    mathlib_source_checkout: Path,
    build_checkout: Path | None,
    state: Mapping[str, Any],
    cache_reused: bool,
) -> dict[str, Any]:
    packages_root = (
        build_checkout / state["pins"]["lake"]["packages_directory"]
        if build_checkout is not None
        else None
    )
    derived_mathlib_checkout = (
        build_checkout / state["pins"]["lake"]["packages_directory"] / "mathlib"
        if build_checkout is not None
        else None
    )
    derived_mathlib_record = state["build"]["mathlib_package"]
    derived_mathlib_manifest = (
        {
            **derived_mathlib_record,
            "checkout": os.fspath(derived_mathlib_checkout),
            "packages_root": os.fspath(packages_root),
        }
        if isinstance(derived_mathlib_record, Mapping)
        and derived_mathlib_checkout is not None
        and packages_root is not None
        else None
    )
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_at": utc_now(),
        "policy": {
            "numstability_is_external": True,
            "numstability_sources_may_be_modified": False,
            "mathlib_sources_may_be_modified": False,
            "pristine_numstability_checkout_used_as_build_directory": False,
            "pristine_mathlib_checkout_used_as_build_directory": False,
            "pristine_mathlib_checkout_is_a_derived_package": False,
            "generated_artifacts_live_only_in_derived_build_checkout": True,
            "lake_preparation_host_root_was_not_mounted": True,
            "lake_preparation_only_writable_host_tree_was_derived_build": True,
            "lake_preparation_nested_user_namespaces_disabled": True,
            "lake_preparation_network_egress_was_none": True,
            "all_dependencies_prefetched_before_first_lake": True,
            "local_repository_mirrors_were_not_mounted_into_lake": True,
            "paper_commit_pinned": True,
            "lake_completed_before_pristine_checkouts_created": True,
            "lake_may_run_after_pristine_checkouts_created": False,
        },
        "numstability": {
            "repository": display_repository(repository),
            "ref": NUMSTABILITY_REF,
            "commit": commit,
            "git_tree": state["git_tree"],
            "checkout": os.fspath(source_checkout),
            "detached": True,
            "read_only": True,
            "cache_reused": cache_reused,
            "integrity": state["source_integrity"],
            "git_role": "pristine-source",
            "lake_directory_absent": True,
            "library_lookup": os.fspath(source_checkout / LIBRARY_LOOKUP),
            "files": state["pins"]["files"],
        },
        "lean": state["pins"]["lean"],
        "lake": state["pins"]["lake"],
        "mathlib": {
            **state["pins"]["mathlib"],
            "checkout": os.fspath(mathlib_source_checkout),
            "git_tree": state["pristine_sources"]["mathlib"]["git_tree"],
            "detached": True,
            "clean": True,
            "read_only": True,
            "git_role": "pristine-source",
            "lake_directory_absent": True,
            "integrity": state["pristine_sources"]["mathlib"]["integrity"],
        },
        "derived_mathlib_package": derived_mathlib_manifest,
        "dependencies": state["pins"]["dependencies"],
        "build": {
            **state["build"],
            "derived_checkout": (
                os.fspath(build_checkout) if build_checkout is not None else None
            ),
            "packages_root": (
                os.fspath(packages_root) if packages_root is not None else None
            ),
            "mathlib_package": derived_mathlib_manifest,
            "read_only": True if build_checkout is not None else None,
        },
        "tools_observed_at_cache_creation": state["tools"],
        "prefetch": state["prefetch"],
        "preparation_isolation": state["preparation_isolation"],
    }


def make_snapshot(
    *,
    source_checkout: Path,
    mathlib_source_checkout: Path,
    build_checkout: Path | None,
    state: Mapping[str, Any],
    source_manifest_path: Path,
    source_manifest_sha256: str,
    runtime_manifest_path: Path,
    runtime_manifest_sha256: str,
) -> dict[str, Any]:
    packages_root = (
        build_checkout / state["pins"]["lake"]["packages_directory"]
        if build_checkout is not None
        else None
    )
    derived_mathlib_checkout = (
        build_checkout / state["pins"]["lake"]["packages_directory"] / "mathlib"
        if build_checkout is not None
        else None
    )
    build_lib = (
        build_checkout
        / state["pins"]["lake"]["directory"]
        / "build"
        / "lib"
        / "lean"
        if build_checkout is not None
        else None
    )
    stable_identity = {
        "cache_format_version": CACHE_FORMAT_VERSION,
        "numstability_commit": state["commit"],
        "numstability_git_tree": state["git_tree"],
        "source_integrity": state["source_integrity"],
        "mathlib_source_integrity": state["pristine_sources"]["mathlib"][
            "integrity"
        ],
        "build_integrity": state["build"]["integrity"],
        "derived_mathlib_integrity": (
            state["build"]["mathlib_package"]["integrity"]
            if isinstance(state["build"]["mathlib_package"], Mapping)
            else None
        ),
        "lean_toolchain": state["pins"]["lean"]["toolchain"],
        "mathlib_commit": state["pins"]["mathlib"]["commit"],
        "tools": state["tools"],
        "build": state["build"]["performed"],
    }
    snapshot_id = sha256_bytes(canonical_json_bytes(stable_identity))
    source = {
        "numstability": {
            "repository": state["repository"],
            "ref": state["ref"],
            "commit": state["commit"],
            "checkout": os.fspath(source_checkout),
            "git_tree": state["git_tree"],
            "tree_digest": state["source_integrity"]["digest"],
            "read_only": True,
            "detached": True,
            "clean": True,
            "lake_directory_absent": True,
            "git_role": "pristine-source",
        },
        "derived_build": {
            "checkout": (
                os.fspath(build_checkout) if build_checkout is not None else None
            ),
            "tree_digest": (
                state["build"]["integrity"]["digest"]
                if state["build"]["integrity"] is not None
                else None
            ),
            "read_only": True if build_checkout is not None else None,
            "pristine_source_was_not_build_working_directory": True,
            "packages_root": (
                os.fspath(packages_root) if packages_root is not None else None
            ),
            "git_role": "derived-build",
            "lake_preparation_filesystem_isolated": True,
        },
        "mathlib": {
            "repository": state["pins"]["mathlib"]["repository"],
            "commit": state["pins"]["mathlib"]["commit"],
            "checkout": os.fspath(mathlib_source_checkout),
            "git_tree": state["pristine_sources"]["mathlib"]["git_tree"],
            "tree_digest": state["pristine_sources"]["mathlib"]["integrity"][
                "digest"
            ],
            "read_only": True,
            "detached": True,
            "clean": True,
            "lake_directory_absent": True,
            "git_role": "pristine-source",
        },
        "derived_mathlib_package": {
            "repository": state["pins"]["mathlib"]["repository"],
            "commit": state["pins"]["mathlib"]["commit"],
            "checkout": (
                os.fspath(derived_mathlib_checkout)
                if derived_mathlib_checkout is not None
                else None
            ),
            "tree_digest": (
                state["build"]["mathlib_package"]["integrity"]["digest"]
                if isinstance(state["build"]["mathlib_package"], Mapping)
                else None
            ),
            "git_tree": (
                state["build"]["mathlib_package"]["git_tree"]
                if isinstance(state["build"]["mathlib_package"], Mapping)
                else None
            ),
            "read_only": True if derived_mathlib_checkout is not None else None,
            "detached": True if derived_mathlib_checkout is not None else None,
            "clean": True if derived_mathlib_checkout is not None else None,
            "git_role": "derived-package",
        },
        "lean": state["pins"]["lean"],
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_at": utc_now(),
        "snapshot_id": snapshot_id,
        "prefetch": state["prefetch"],
        "source": source,
        "preparation_isolation": state["preparation_isolation"],
        "condition_l": {
            "numstability_source": os.fspath(source_checkout),
            "numstability_derived_build": (
                os.fspath(build_checkout) if build_checkout is not None else None
            ),
            "library_lookup": os.fspath(source_checkout / LIBRARY_LOOKUP),
            "lean_build_lib": (
                os.fspath(build_lib)
                if build_lib is not None and build_lib.is_dir()
                else None
            ),
            "mathlib_source": (
                os.fspath(mathlib_source_checkout)
            ),
            "mathlib_derived_package": (
                os.fspath(derived_mathlib_checkout)
                if derived_mathlib_checkout is not None
                else None
            ),
            "derived_packages_root": (
                os.fspath(packages_root) if packages_root is not None else None
            ),
            "mount_mode": "read-only",
        },
        "condition_n": {
            "forbidden_paths": [
                os.fspath(source_checkout),
                os.fspath(source_checkout / LIBRARY_LOOKUP),
                os.fspath(mathlib_source_checkout),
                os.fspath(build_checkout) if build_checkout is not None else None,
                (
                    os.fspath(derived_mathlib_checkout)
                    if derived_mathlib_checkout is not None
                    else None
                ),
            ]
        },
        "runtime": {
            "source_manifest": os.fspath(source_manifest_path),
            "source_manifest_sha256": source_manifest_sha256,
            "runtime_manifest": os.fspath(runtime_manifest_path),
            "runtime_manifest_sha256": runtime_manifest_sha256,
        },
    }


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    script_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=script_root,
        help="VSCLReuse root (default: parent of this scripts directory)",
    )
    parser.add_argument("--cache-root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--source-repository",
        default=NUMSTABILITY_REPOSITORY,
        help="NumStability Git repository; override only for an audited mirror/test fake",
    )
    parser.add_argument(
        "--local-dependency-mirror",
        action="append",
        type=Path,
        default=[],
        help=(
            "explicit local dependency repository allowed as a trusted host-side "
            "prefetch source; repeat for multiple audited mirrors"
        ),
    )
    parser.add_argument("--git-bin", default="git")
    parser.add_argument("--unshare-bin", default="unshare")
    parser.add_argument("--bwrap-bin", default="bwrap")
    parser.add_argument("--curl-bin", default="curl")
    parser.add_argument("--zstd-bin", default="zstd")
    parser.add_argument("--no-build", action="store_true")
    parser.add_argument("--build-timeout-seconds", type=float, default=7200.0)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = parse_args(argv)
    if arguments.build_timeout_seconds <= 0:
        raise PreparationError("--build-timeout-seconds must be positive")
    benchmark_root = arguments.benchmark_root.resolve(strict=True)
    if not benchmark_root.is_dir():
        raise PreparationError("--benchmark-root must be a directory")
    repository = display_repository(arguments.source_repository)
    validate_repository_transport(repository, label="NumStability source")
    git_bin = locate_executable(arguments.git_bin)
    unshare_bin = locate_executable(arguments.unshare_bin)
    bwrap_bin = locate_executable(arguments.bwrap_bin)
    curl_bin = locate_executable(arguments.curl_bin)
    zstd_bin = locate_executable(arguments.zstd_bin)
    repo_root = repository_root(benchmark_root, git_bin)
    assert_nonexecuting_git_config(repo_root, label="benchmark repository")
    local_mirror = require_external_local_mirror(repository, repo_root)
    if local_mirror is not None:
        assert_no_special_files(local_mirror, label="local NumStability mirror")
        assert_nonexecuting_git_config(
            local_mirror, label="local NumStability mirror"
        )
    explicit_local_dependency_mirrors: list[Path] = []
    for raw_mirror in arguments.local_dependency_mirror:
        lexical_mirror = absolute_without_resolving(raw_mirror)
        if ".." in raw_mirror.expanduser().parts:
            raise PreparationError(
                "--local-dependency-mirror must not contain '..' components"
            )
        if _secure_walk_directory(
            lexical_mirror, label="local dependency mirror", create=False
        ) != lexical_mirror:
            raise PreparationError("local dependency mirror is not a real directory")
        mirror = require_external_local_mirror(
            os.fspath(lexical_mirror), repo_root
        )
        if mirror is None:
            raise PreparationError("local dependency mirror must be a local path")
        assert_no_special_files(mirror, label="local dependency mirror")
        assert_nonexecuting_git_config(mirror, label="local dependency mirror")
        explicit_local_dependency_mirrors.append(mirror)
    if len(set(explicit_local_dependency_mirrors)) != len(
        explicit_local_dependency_mirrors
    ):
        raise PreparationError("duplicate --local-dependency-mirror")
    lexical_cache = absolute_without_resolving(arguments.cache_root)
    lexical_output = absolute_without_resolving(arguments.output_dir)
    lexical_repo_root = absolute_without_resolving(repo_root)
    if any(
        is_within(candidate, lexical_repo_root)
        or is_within(lexical_repo_root, candidate)
        for candidate in (lexical_cache, lexical_output)
    ):
        raise PreparationError(
            "external cache/output directories must not overlap the benchmark "
            "Git worktree"
        )
    if is_within(lexical_output, lexical_cache) or is_within(
        lexical_cache, lexical_output
    ):
        raise PreparationError("external cache and output directories must be disjoint")
    for mirror in [
        *([local_mirror] if local_mirror is not None else []),
        *explicit_local_dependency_mirrors,
    ]:
        if any(
            is_within(candidate, mirror) or is_within(mirror, candidate)
            for candidate in (lexical_cache, lexical_output)
        ):
            raise PreparationError(
                "external cache/output and local repository mirrors must be disjoint"
            )
    cache_root = require_external_private_directory(
        arguments.cache_root,
        label="external cache root",
        git_bin=git_bin,
        create=True,
    )
    output_dir = require_external_private_directory(
        arguments.output_dir,
        label="external output directory",
        git_bin=git_bin,
        create=True,
    )
    if is_within(output_dir, cache_root) or is_within(cache_root, output_dir):
        raise PreparationError("external cache and output directories must be disjoint")
    # Preserve the lexical child path until it has independently passed the
    # same no-symlink, no-worktree, private-ownership checks as the caller's
    # cache root.  Resolving first would hide a pre-existing
    # ``cache_root/numstability`` symlink and could redirect cache writes into an
    # unrelated checkout.
    cache_namespace = require_external_private_directory(
        cache_root / "numstability",
        label="external cache namespace",
        git_bin=git_bin,
        create=True,
    )
    if local_mirror is not None and (
        is_within(cache_namespace, local_mirror)
        or is_within(local_mirror, cache_namespace)
    ):
        raise PreparationError("external cache and local source mirror must be disjoint")
    commands: list[CommandRecord] = []
    commit = resolve_numstability_commit(git_bin, repository, commands)
    (
        source_checkout,
        mathlib_source_checkout,
        build_checkout,
        state,
        reused,
    ) = prepare_cache(
        namespace=cache_namespace,
        repository=repository,
        commit=commit,
        git_bin=git_bin,
        unshare_bin=unshare_bin,
        bwrap_bin=bwrap_bin,
        curl_bin=curl_bin,
        zstd_bin=zstd_bin,
        explicit_local_dependency_mirrors=explicit_local_dependency_mirrors,
        no_build=arguments.no_build,
        build_timeout_seconds=arguments.build_timeout_seconds,
        recorder=commands,
    )

    output_dir.mkdir(parents=True, exist_ok=True)
    source_path = output_dir / "source_manifest.json"
    runtime_path = output_dir / "runtime_manifest.json"
    snapshot_path = output_dir / "snapshot.json"
    source = source_manifest(
        repository=repository,
        commit=commit,
        source_checkout=source_checkout,
        mathlib_source_checkout=mathlib_source_checkout,
        build_checkout=build_checkout,
        state=state,
        cache_reused=reused,
    )
    source_sha = write_json_atomic(source_path, source)
    runtime = runtime_inventory(
        repository_root_path=repo_root,
        benchmark_root=benchmark_root,
        cache_root=cache_root,
        output_dir=output_dir,
        git_bin=git_bin,
        unshare_bin=unshare_bin,
        bwrap_bin=bwrap_bin,
        curl_bin=curl_bin,
        zstd_bin=zstd_bin,
        commands=commands,
    )
    runtime["source_manifest"] = {
        "path": os.fspath(source_path),
        "sha256": source_sha,
    }
    runtime_sha = write_json_atomic(runtime_path, runtime)
    snapshot = make_snapshot(
        source_checkout=source_checkout,
        mathlib_source_checkout=mathlib_source_checkout,
        build_checkout=build_checkout,
        state=state,
        source_manifest_path=source_path,
        source_manifest_sha256=source_sha,
        runtime_manifest_path=runtime_path,
        runtime_manifest_sha256=runtime_sha,
    )
    write_json_atomic(snapshot_path, snapshot)
    print(os.fspath(snapshot_path))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except PreparationError as error:
        print(f"prepare_runtime.py: error: {error}", file=sys.stderr)
        raise SystemExit(2) from error
