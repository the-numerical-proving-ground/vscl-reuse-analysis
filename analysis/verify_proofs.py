"""Check the released final agent proofs against their index and measurements.

With no arguments, verify hashes, task statements, source policy, and LOC.
With --results-root, also recompile every proof and recompute DP using the
pinned runtime prepared by run_benchmark.py create. No model is invoked.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from benchmark.scripts import host_limits, run_attempt, run_benchmark
from benchmark.tools.validator import compare_target_signature, forbidden_source_findings
from metrics import lean_code_lines, load_attempts, task_means

LIBRARY_COMMIT = "38228c607d62e9485b4fa1fc668cc3cb2857857e"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_archive() -> list[dict]:
    bench = ROOT / "benchmark"
    run_benchmark._verify_task_corpus_lock(bench)
    attempts = load_attempts(ROOT / "results/attempts.csv")
    task_means(attempts)  # Check complete matched repetitions and categories.
    measured = {r["run_id"]:r for r in attempts}
    with (ROOT / "results/proofs/index.csv").open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != 360 or {r["run_id"] for r in rows} != set(measured):
        raise ValueError("proof index must match all 360 measured attempts")
    for row in rows:
        expected = measured[row["run_id"]]
        for field in ("task_id", "repetition", "condition"):
            if row[field] != expected[field]:
                raise ValueError(f"proof index disagrees with measurements: {row['run_id']}")
        relative = f"results/proofs/{row['task_id']}/rep-{row['repetition']}/{row['condition']}/candidate.lean"
        proof = ROOT / relative
        if row["path"] != relative or proof.is_symlink() or not proof.resolve().is_relative_to(ROOT):
            raise ValueError("proof index contains an invalid file path")
        if row["original_submitted_sha256"] != expected["proof_sha256"] or sha(proof) != row["published_sha256"]:
            raise ValueError(f"proof hash differs: {row['run_id']}")
        info = run_attempt._task_metadata(bench, row["task_id"])
        if not compare_target_signature(proof, bench / info["target_relative"], info["target_theorem"])["ok"]:
            raise ValueError(f"fixed statement differs: {row['run_id']}")
        if forbidden_source_findings(proof, ["NumStability"] if row["condition"] == "N" else []):
            raise ValueError(f"proof violates its source policy: {row['run_id']}")
        loc = lean_code_lines(proof.read_text(encoding="utf-8"))
        if loc != expected["submitted_loc"]:
            raise ValueError(f"LOC differs: {row['run_id']}")
        row.update(expected_dp=expected["direct_proof_declarations"], submitted_loc=loc)
    return rows


@dataclass(frozen=True)
class LeanInputs:
    toolchain: Path
    packages: Path
    shared: Path
    library_source: Path
    library_olean: Path
    identity: str


def inputs_from_campaign(results: Path) -> LeanInputs:
    lock = read(results / "campaign_lock.json")
    snapshot = read(results / lock["runtime_snapshot"]["path"])
    if snapshot["source"]["numstability"]["commit"] != LIBRARY_COMMIT:
        raise ValueError("proof verification requires the paper's pinned Higham snapshot")
    build = Path(snapshot["source"]["derived_build"]["checkout"])
    return LeanInputs(Path(lock["toolchain_root"]), build / ".lake/packages",
                      Path(lock["shared_olean_root"]), Path(snapshot["source"]["numstability"]["checkout"]),
                      build / ".lake/build/lib/lean", snapshot["snapshot_id"])


def audit_one(row: dict, inputs: LeanInputs, cache: Path) -> dict:
    if not host_limits.already_bounded():
        raise RuntimeError("offline proof compilation needs authenticated CPU and memory controls")
    identity = {"proof": row["published_sha256"], "runtime": inputs.identity,
                "helper": sha(HERE / "direct_usage.lean"), "verifier": sha(Path(__file__)),
                "task_corpus_lock": sha(ROOT / "benchmark/metadata/task_corpus_lock.json")}
    saved = cache / (row["run_id"] + ".json")
    cached = read(saved) if saved.exists() else {}
    if cached.get("identity") == identity:
        result = cached["result"]
    else:
        bench = ROOT / "benchmark"
        info = run_attempt._task_metadata(bench, row["task_id"])
        with tempfile.TemporaryDirectory(prefix="proof-", dir=cache) as temporary:
            workspace = Path(temporary) / "workspace"
            _, candidate = run_attempt._stage_workspace(bench, info, workspace)
            shutil.copyfile(ROOT / row["path"], candidate)
            command = [sys.executable, str(bench / "tools/lean_isolated.py"), "build-audit",
                       "--condition", row["condition"], "--workspace", str(workspace), "--source", str(candidate),
                       "--toolchain-root", str(inputs.toolchain), "--packages-root", str(inputs.packages),
                       "--shared-olean-root", str(inputs.shared / info["paper_id"]),
                       "--audit-helper", str(HERE / "direct_usage.lean"), "--submission-module", "candidate",
                       "--target-theorem", info["target_theorem"]]
            if row["condition"] == "L":
                command.extend(["--library-source", str(inputs.library_source / "NumStability"),
                                "--library-root-file", str(inputs.library_source / "NumStability.lean"),
                                "--library-olean", str(inputs.library_olean)])
            completed = subprocess.run(command, capture_output=True, text=True, timeout=1800)
            if completed.returncode:
                raise RuntimeError(f"proof compilation failed: {row['run_id']}\n{completed.stdout[-5000:]}{completed.stderr[-2000:]}")
            outputs = [json.loads(line) for line in completed.stdout.splitlines()
                       if line.startswith("{") and '"direct-proof-declarations-v1"' in line]
            if len(outputs) != 1:
                raise ValueError("expected one compiled DP report")
            direct = outputs[0]
            if direct["count"] != len(set(direct["declarations"])):
                raise ValueError("DP count and distinct declarations disagree")
            result = {"run_id": row["run_id"], "compiled": True, "submitted_loc": row["submitted_loc"],
                      "direct_proof_declarations": direct["count"], "declarations": direct["declarations"]}
        saved.write_text(json.dumps({"identity":identity, "result":result}, indent=2) + "\n")
    if result["direct_proof_declarations"] != row["expected_dp"] or result["submitted_loc"] != row["submitted_loc"]:
        raise ValueError(f"recomputed measurements differ: {row['run_id']}")
    return result


def audit_archive(rows: list[dict], inputs: LeanInputs, cache: Path, jobs: int = 1) -> list[dict]:
    if cache.resolve().is_relative_to(ROOT):
        raise ValueError("put proof-check output outside this repository")
    cache.mkdir(parents=True, exist_ok=True, mode=0o700)
    if cache.stat().st_uid != os.getuid() or cache.stat().st_mode & 0o077:
        raise ValueError("proof-check output must be a private, user-owned directory")
    results = []
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [executor.submit(audit_one, row, inputs, cache) for row in rows]
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            print(f"[{len(results)}/{len(rows)}] {result['run_id']}: compiled, LOC and DP match", flush=True)
    results.sort(key=lambda r:r["run_id"])
    (cache / "summary.json").write_text(json.dumps({"proofs":len(results), "all_compiled":True,
                                                   "recorded_LOC_and_DP_match":True}, indent=2) + "\n")
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-root", type=Path, help="runtime from run_benchmark.py create; no model attempts needed")
    parser.add_argument("--cache-dir", type=Path, help="private output directory outside this checkout")
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1, help="offline compiler jobs within aggregate build limits")
    parser.add_argument("--resource-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    rows = load_archive()
    print("All 360 published proofs: hashes, statements, source policy and recorded LOC match", flush=True)
    if args.results_root is None:
        return 0
    if args.cache_dir is None:
        parser.error("compiled verification requires --cache-dir outside this checkout")
    if not args.resource_worker and not host_limits.already_bounded():
        command = [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:], "--resource-worker"]
        with host_limits.command_scope(command, timeout=14400, cwd=ROOT) as bounded:
            return subprocess.run(bounded, check=False).returncode
    audit_archive(rows, inputs_from_campaign(args.results_root.resolve()), args.cache_dir.resolve(), args.jobs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
