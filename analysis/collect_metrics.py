"""Collect time, tokens, full-file LOC, and DP from a verified campaign.

No task extraction or model execution occurs here. DP is computed afterward
from accepted proof bodies using the same frozen, offline Lean environment.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from metrics import lean_code_lines

HERE = Path(__file__).resolve().parent
FIELDS = ("run_id", "task_id", "category", "repetition", "condition", "time_seconds",
          "input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens",
          "total_tokens", "submitted_loc", "direct_proof_declarations", "accepted", "proof_sha256")
EXPECTED_LIBRARY_COMMIT = "38228c607d62e9485b4fa1fc668cc3cb2857857e"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def target_for(benchmark: Path, task_id: str) -> str:
    paper, slot = task_id.split("-", 1)
    metadata = read(benchmark / "tasks" / paper / slot / "task.json")
    return metadata["validation"]["required_declaration"]


def stage_compiled_cache(root: Path, packages: Path, library: Path, shared: Path,
                         runtime_id: str) -> tuple[Path, Path, Path, str]:
    """Optionally put byte-verified compiler inputs on a faster local disk."""
    root = root.resolve()
    sources = [(library.resolve(), Path("library")), (shared.resolve(), Path("shared"))]
    for package in sorted(packages.iterdir()):
        compiled = package / ".lake/build/lib/lean"
        if compiled.is_dir():
            sources.append((compiled.resolve(), Path("packages") / package.name / ".lake/build/lib/lean"))
    for source, _ in sources:
        if root.is_relative_to(source) or source.is_relative_to(root):
            raise ValueError("compiled cache and original compiler inputs must not overlap")
    root.mkdir(parents=True, exist_ok=True, mode=0o700)
    if root.stat().st_uid != os.getuid() or root.stat().st_mode & 0o077:
        raise ValueError("compiled cache must be a private, user-owned directory")
    manifest_path = root / "compiled-inputs.json"
    partial = root / "compiled-inputs.partial.json"
    if not manifest_path.exists():
        if partial.exists():
            if read(partial).get("runtime_snapshot_id") != runtime_id:
                raise ValueError("partial compiled cache belongs to another runtime")
        elif any(root.iterdir()):
            raise ValueError("use an empty directory for the optional compiled cache")
        else:
            partial.write_text(json.dumps({"runtime_snapshot_id": runtime_id}) + "\n")
    if manifest_path.exists():
        cached = read(manifest_path)
        if cached.get("runtime_snapshot_id") != runtime_id:
            raise ValueError("compiled cache belongs to a different runtime")
        for item in cached["files"]:
            path = root / item["path"]
            if path.resolve() != path or not path.is_relative_to(root):
                raise ValueError("compiled cache contains an unsafe path")
            if not path.is_file() or path.stat().st_size != item["bytes"] or sha256(path) != item["sha256"]:
                raise ValueError("compiled cache integrity check failed")
        print("Verified existing compiled-input cache", flush=True)
    else:
        files = []
        for source, dest in sources:
            for path in sorted(source.rglob("*")):
                if path.is_symlink():
                    raise ValueError("compiled inputs must not contain symlinks")
                if path.is_file():
                    files.append((path, dest / path.relative_to(source)))
        total = sum(p.stat().st_size for p, _ in files)
        if shutil.disk_usage(root).free < total + 512 * 1024**2:
            raise ValueError("insufficient space for the optional compiled cache")
        records = []
        for index, (source, relative) in enumerate(files, 1):
            dest = root / relative
            if dest.resolve(strict=False) != dest or not dest.is_relative_to(root):
                raise ValueError("compiled cache contains a symlink or unsafe path")
            dest.parent.mkdir(parents=True, exist_ok=True)
            if dest.exists():
                dest.chmod(0o600)
            digest = hashlib.sha256()
            with source.open("rb") as incoming, dest.open("wb") as outgoing:
                while chunk := incoming.read(1024 * 1024):
                    digest.update(chunk)
                    outgoing.write(chunk)
            if sha256(dest) != digest.hexdigest():
                raise ValueError("compiled-input copy verification failed")
            dest.chmod(0o444)
            records.append({"path": relative.as_posix(), "bytes": dest.stat().st_size, "sha256": digest.hexdigest()})
            if index % 5000 == 0:
                print(f"Verified compiler-input copies: {index}/{len(files)}", flush=True)
        temporary = manifest_path.with_suffix(".tmp")
        temporary.write_text(json.dumps({"runtime_snapshot_id": runtime_id, "files": records}, separators=(",", ":")) + "\n")
        temporary.replace(manifest_path)
        print(f"Verified {len(records)} copied compiler inputs ({total / 1024**3:.2f} GiB)", flush=True)
    return root / "packages", root / "library", root / "shared", sha256(manifest_path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--verification-summary", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path, default=HERE.parent / "benchmark")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache-dir", type=Path, required=True)
    parser.add_argument("--compiled-cache-root", type=Path,
                        help="Optional private fast-disk cache for byte-verified compiled inputs")
    parser.add_argument("--task-id", action="append", default=[], help="Optional task subset for inspection")
    parser.add_argument("--resource-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    for name in ("results_root", "verification_summary", "benchmark_root", "output", "cache_dir"):
        setattr(args, name, getattr(args, name).resolve())
    sys.path.insert(0, str(args.benchmark_root / "scripts"))
    import host_limits
    if not args.resource_worker and not host_limits.already_bounded():
        command = [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:], "--resource-worker"]
        with host_limits.command_scope(command, timeout=14400, cwd=HERE) as bounded:
            return subprocess.run(bounded, check=False).returncode
    if not host_limits.already_bounded():
        raise RuntimeError("authenticated CPU and memory controls are required")

    summary = read(args.verification_summary)
    attempts = summary["attempt_results"]
    if summary.get("complete") is not True or len(attempts) != 360:
        raise ValueError("expected a complete verifier summary for 360 attempts")
    if any(a.get("pass") is not True or a.get("token_usage_complete") is not True for a in attempts):
        raise ValueError("expected accepted attempts with complete token telemetry")
    lock = read(args.results_root / "campaign_lock.json")
    if lock["campaign_id"] != summary["campaign_id"]:
        raise ValueError("verifier and campaign identities differ")
    snapshot = read(args.results_root / lock["runtime_snapshot"]["path"])
    library = snapshot["source"]["numstability"]
    if library["commit"] != EXPECTED_LIBRARY_COMMIT:
        raise ValueError("DP must use the frozen Higham snapshot, not another VSCL version")
    source = Path(library["checkout"])
    build = Path(snapshot["source"]["derived_build"]["checkout"])
    toolchain = Path(lock["toolchain_root"])
    shared = Path(lock["shared_olean_root"])
    packages = build / ".lake/packages"
    library_olean = build / ".lake/build/lib/lean"
    compiled_cache_hash = None
    if args.compiled_cache_root is not None:
        packages, library_olean, shared, compiled_cache_hash = stage_compiled_cache(
            args.compiled_cache_root, packages, library_olean, shared, snapshot["snapshot_id"])
    helper = HERE / "direct_usage.lean"
    identity = {"campaign_lock": lock["record_sha256"], "runtime": snapshot["snapshot_id"],
                "direct_usage": sha256(helper), "metrics": sha256(HERE / "metrics.py"),
                "collector": sha256(Path(__file__)), "verification": sha256(args.verification_summary),
                "compiled_cache": compiled_cache_hash}
    args.cache_dir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    chosen = [a for a in attempts if not args.task_id or a["task_id"] in args.task_id]
    if not chosen:
        raise ValueError("no attempts selected")
    rows = []
    for index, attempt in enumerate(chosen, 1):
        run_id = attempt["run_id"]
        if any(c not in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" for c in run_id):
            raise ValueError("invalid run ID")
        pair_id, condition = run_id.rsplit("-", 1)
        directory = args.results_root / "pairs" / pair_id / ("condition-" + condition)
        proof = directory / "accepted_proof.lean"
        record = read(directory / "attempt.json")
        if not isinstance(attempt.get("numstability_declarations"), list):
            raise ValueError("verified transitive dependency evidence is required")
        proof_hash = sha256(proof)
        if record["run_id"] != run_id or record["pass"] is not True or record["validation"]["candidate_sha256"] != proof_hash:
            raise ValueError(f"accepted proof identity or hash differs: {run_id}")
        key = {**identity, "proof": proof_hash}
        cache = args.cache_dir / (run_id + ".json")
        cached = read(cache) if cache.exists() else {}
        if cached.get("identity") == key:
            row = cached["row"]
        else:
            # An empty verified transitive set proves that its direct subset
            # is empty as well. Other L proofs require the compiled-body audit.
            direct = {"count": 0, "declarations": [],
                      "source": "empty-verified-transitive-dependency-audit"}
            if condition == "N" and attempt.get("numstability_declarations"):
                raise ValueError("N has a forbidden library dependency")
            if condition == "L" and attempt.get("numstability_declarations"):
                paper = attempt["paper_id"]
                target = target_for(args.benchmark_root, attempt["task_id"])
                with tempfile.TemporaryDirectory(prefix="dp-", dir=args.cache_dir) as temp:
                    workspace = Path(temp)
                    shutil.copyfile(proof, workspace / "candidate.lean")
                    command = [sys.executable, str(args.benchmark_root / "tools/lean_isolated.py"),
                               "build-audit", "--condition", "L", "--workspace", str(workspace),
                               "--source", str(workspace / "candidate.lean"),
                               "--toolchain-root", str(toolchain), "--packages-root", str(packages),
                               "--shared-olean-root", str(shared / paper), "--library-source", str(source / "NumStability"),
                               "--library-root-file", str(source / "NumStability.lean"),
                               "--library-olean", str(library_olean),
                               "--audit-helper", str(helper), "--submission-module", "candidate", "--target-theorem", target]
                    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1800)
                    if result.returncode:
                        raise RuntimeError(f"DP audit failed for {run_id}:\n{result.stdout[-6000:]}")
                    matches = [json.loads(s) for s in result.stdout.splitlines() if s.startswith("{") and '"direct-proof-declarations-v1"' in s]
                    if len(matches) != 1:
                        raise ValueError(f"expected one compiled DP record: {run_id}")
                    direct = matches[0]
                    if direct["count"] != len(set(direct["declarations"])):
                        raise ValueError("DP count disagrees with its distinct declaration list")
            tokens = attempt["token_usage"]
            row = {"run_id": run_id, "task_id": attempt["task_id"], "category": attempt["category"],
                   "repetition": pair_id.rsplit("-", 1)[1], "condition": condition,
                   "time_seconds": f'{attempt["wall_time_seconds"]:.6f}',
                   **{k: tokens[k] for k in ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens", "total_tokens")},
                   "submitted_loc": lean_code_lines(proof.read_text(encoding="utf-8")),
                   "direct_proof_declarations": direct["count"], "accepted": "true", "proof_sha256": proof_hash}
            temporary = cache.with_suffix(".tmp")
            temporary.write_text(json.dumps({"identity": key, "row": row, "direct_usage": direct}, indent=2) + "\n")
            temporary.replace(cache)
        rows.append(row)
        print(f"[{index}/{len(chosen)}] {run_id}: LOC={row['submitted_loc']} DP={row['direct_proof_declarations']}", flush=True)
    temporary = args.output.with_suffix(".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda r: r["run_id"]))
    temporary.replace(args.output)
    print(f"wrote {len(rows)} numeric records: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
