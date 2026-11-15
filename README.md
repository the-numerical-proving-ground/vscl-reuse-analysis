# VSCL reuse analysis

This package contains the 60 active proof tasks and the numerical records needed
to reproduce Figures 9 and 10. Categories C1, C2, and C3 contain 30, 20, and 10
tasks. The 54 retained source papers are indexed consecutively as P01–P54 in
[`benchmark/metadata/papers.csv`](benchmark/metadata/papers.csv). Each entry
lists its citation and task IDs; source papers themselves are not included.

The categories are based on the applicable results from the library that satisfy the following three conditions:
(i) reconstructing the result without access to VSCL would require significant mathematical effort, as judged by the LLM that extracted the task (OpenAI Codex with GPT-6 Sol); (ii) the result goes beyond basic algebraic manipulations; and (iii) Mathlib does not already provide a readily usable equivalent.

| Category | Tasks | Applicable qualifying results |
| --- | ---: | --- |
| C1 | 30 | None |
| C2 | 20 | Exactly one |
| C3 | 10 | At least two |

This classification describes expected support; it is separate from the observed DP count.

For example, task `P01-C3` has the following fixed inputs:

| File | Purpose |
| --- | --- |
| `benchmark/tasks/P01/C3/target.lean` | Fixed theorem statement. |
| `benchmark/tasks/P01/C3/context.md` | Source statement and proof context. |
| `benchmark/shared/VSCLReuse/P01/Definitions.lean` | Definitions from that paper, shared by its tasks. |
| `benchmark/tasks/P01/C3/task.json` | Category, source labels/locations, and validation declaration. |

Both conditions receive these inputs unchanged and read-only. A submission is
written to `candidate.lean`. Task IDs combine the paper index and category;
a source-label suffix distinguishes two tasks in the same category from one
paper, such as `P53-C3-Lemma1`.

The source annotations retain the original theorem, lemma, proposition, and
equation numbers. There are 43 tasks from explicitly named results: 21
theorems (`THM`), 19 lemmas (`LEM`), and 3 propositions (`PROP`). The remaining
17 come from equations (`EQN`), prose (`TXT`), or unnumbered displays (`UNL`);
these source tags can overlap within a task. The index covers only the 54
retained papers from the 78 screened candidates. Citation dates refer to the
source version where the task used an author manuscript.

You can regenerate the paper figures from the bundled numerical records, or run
fresh N/L measurements on your own machine. Fresh runs use the same fixed
statements, prompts, library snapshot, Lean version, and Mathlib revision.
Elapsed times and model-generated proofs can vary between runs and machines.
The bundled measurements retain their recorded numeric values. Release paper
indices, category labels, file/module names, and corresponding local Lean
identifiers have been normalized to this paper's notation; mathematical
statements, definitions, and source result labels are preserved. Historical
proof hashes in `results/attempts.csv` identify the original accepted files.
The frozen counterbalanced N/L order is preserved in `metadata/run_order.json`
under `benchmark/`. Fresh campaign locks authenticate the release inputs.

## Regenerate Figures 9 and 10

From the repository root, with Python 3.11 or later:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python analysis/plot_figures.py --check-paper
```

This writes `generated/figure9.pdf`, `generated/figure10.pdf`, SVG versions, and
the values used to draw them. It requires neither an agent account nor the Lean
library. To recompute the numerical tables with Python's standard library:

```sh
python3 analysis/plot_figures.py --tables-only --check-paper
```

## Access the exact library snapshot

The measurements used the Higham component of VSCL at commit
`38228c607d62e9485b4fa1fc668cc3cb2857857e` of
[`AlexGeorgantzas/lean-numerical-stability`](https://github.com/AlexGeorgantzas/lean-numerical-stability/tree/38228c607d62e9485b4fa1fc668cc3cb2857857e).
Its Lean modules use the `NumStability` namespace. The pinned dependencies are:

| Dependency | Version |
| --- | --- |
| Higham snapshot | `38228c607d62e9485b4fa1fc668cc3cb2857857e` |
| Lean | `leanprover/lean4:v4.29.0-rc3` |
| Mathlib | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |

The same pins are recorded in `benchmark/metadata/dependencies.json` and checked
by runtime preparation. Preparation fetches that exact commit and builds the
required compiled modules in an external cache. Condition L receives read-only
access to it; condition N receives no library source, compiled modules, guide,
or index. Preparation uses the snapshot's locked dependency manifest.

To inspect the source separately, create a workspace outside this Git checkout
and check out the exact commit:

```sh
export REUSE_WORK_ROOT="$(mktemp -d "$HOME/vscl-reuse-work.XXXXXX")"
git clone --no-checkout \
  https://github.com/AlexGeorgantzas/lean-numerical-stability.git \
  "$REUSE_WORK_ROOT/higham-snapshot"
git -C "$REUSE_WORK_ROOT/higham-snapshot" checkout --detach \
  38228c607d62e9485b4fa1fc668cc3cb2857857e
git -C "$REUSE_WORK_ROOT/higham-snapshot" rev-parse HEAD
```

The last command must print the full snapshot commit above. This inspection
checkout is separate from the runner's authenticated cache. The runner selects
the commit directly, so subsequent branch updates do not change the experiment.

## Host requirements for fresh measurements

The measured runner currently supports Linux x86-64 with systemd, a unified
cgroup-v2 hierarchy with CPU partition and memory controls, and unprivileged
user namespaces. Install `git`, `curl`, `zstd`, ripgrep (`rg`), Bubblewrap (`bwrap`), `unshare`,
a C compiler, Python 3.11 or later, and the pinned Lean toolchain through Elan.
Figure generation runs independently of these Linux measurement facilities.

The paper's per-attempt budget is four homogeneous physical cores, including
their online SMT siblings, and 16 GiB of memory with zero swap. The manager has
a separate 1 GiB allowance. The runner checks available memory and requires
CPUs outside the leased set for host management. These are experiment settings;
no processor brand, model, hostname, CPU IDs, disk mount, username, or UID from
the authors' machine is required.

Setup discovers the reader's online CPU topology, allowed affinity, eligible
core classes, current user, paths, and supported kernel controls. It selects
actual CPU IDs from that host and records the resulting allocation in the
local campaign. N and L use matching budgets and run serially. A host that
cannot provide the paper's budget receives an explicit prerequisite failure;
the runner does not silently change the experiment. Different resource budgets
would define a separately recorded experimental configuration.

You also need access to the measured model (`gpt-6-sol`, reasoning `xhigh`) and
a compatible agent executable with its sibling `codex-code-mode-host` binary.
The measured executable reported `codex-cli 0.162.0-alpha.17.2`. Supply paths to
your own installation and authentication file. Agent availability and protocol
compatibility must be checked before starting fresh measurements.

## Prepare and run on your host

Keep the repository's controlled files committed and clean before creating a
campaign. From the repository root:

```sh
elan toolchain install "$(cat lean-toolchain)"
export REUSE_CODEX_BIN="$(command -v codex)"
export REUSE_AUTH_FILE="${CODEX_HOME:-$HOME/.codex}/auth.json"
export REUSE_LEAN_BIN="$(elan which lean)"
export REUSE_LEAN_ROOT="$(dirname "$(dirname "$REUSE_LEAN_BIN")")"
```

Set `REUSE_CODEX_BIN` and `REUSE_AUTH_FILE` to the paths for your installation
if these discovery defaults do not identify them. If you did not create the
external inspection workspace above, create one now:

```sh
export REUSE_WORK_ROOT="$(mktemp -d "$HOME/vscl-reuse-work.XXXXXX")"
```

Install the local CPU guard and inspect the automatically discovered host:

```sh
sudo sh benchmark/admin/install_cpu_guard.sh --operator "$(id -un)"
.venv/bin/python benchmark/scripts/run_benchmark.py inventory
mkdir -m 700 "$REUSE_WORK_ROOT/cache" "$REUSE_WORK_ROOT/metrics-cache"
```

The installer generates its configuration from this host and user. No
pre-generated author machine configuration is supplied in this package.

Create the frozen campaign. This prepares the pinned offline Lean runtime and
records your host environment; it does not start a model attempt:

```sh
.venv/bin/python benchmark/scripts/run_benchmark.py create \
  --results-root "$REUSE_WORK_ROOT/results" \
  --runtime-cache-root "$REUSE_WORK_ROOT/cache" \
  --codex "$REUSE_CODEX_BIN" \
  --auth-file "$REUSE_AUTH_FILE" \
  --toolchain-root "$REUSE_LEAN_ROOT" \
  --jobs 1 --acknowledge-environment-lock
```

Start the model-backed measurements and verify the complete campaign:

```sh
.venv/bin/python benchmark/scripts/run_benchmark.py campaign \
  --results-root "$REUSE_WORK_ROOT/results" --acknowledge-provider-use
.venv/bin/python benchmark/scripts/verify_results.py \
  --results-root "$REUSE_WORK_ROOT/results" --require-complete \
  > "$REUSE_WORK_ROOT/verification-summary.json"
```

Repeating the campaign command resumes unfinished assignments with fresh agent
state. The protocol allows 7,200 seconds per condition and runs three matched
N/L repetitions per task, yielding 180 pairs and 360 attempts. Agent tools are
offline and subagents are disabled. Submission stops the scored clock; hidden
validation and later metric collection have separate timing.

## Compute DP and plot a fresh campaign

DP counts distinct declarations from the frozen Higham snapshot referenced by
the compiled target proof or the bodies of reachable helpers in the submitted
file. The analysis resolves Lean names, follows submitted helpers, and stops
at imported declarations. It counts definitions and other constants as well as
theorems. Repeated references count once; unused imports and unreachable helpers
add nothing. Imported library proof bodies are outside the traversal.

```sh
.venv/bin/python analysis/collect_metrics.py \
  --results-root "$REUSE_WORK_ROOT/results" \
  --verification-summary "$REUSE_WORK_ROOT/verification-summary.json" \
  --output "$REUSE_WORK_ROOT/attempts.csv" \
  --cache-dir "$REUSE_WORK_ROOT/metrics-cache"
.venv/bin/python analysis/plot_figures.py \
  --data "$REUSE_WORK_ROOT/attempts.csv" \
  --output "$REUSE_WORK_ROOT/figures"
```

The collector uses the paths recorded by your campaign on your machine. It
checks the snapshot commit and accepted proof hashes. DP compilation is offline
and bounded by the local build controls; it does not alter measured costs.

For a campaign whose compiled libraries are on a slow disk, the collector also
accepts `--compiled-cache-root` pointing to an empty private directory on a
faster local disk. It copies and verifies the compiled inputs byte for byte
before using them and verifies cached copies on reuse. This optional cache
needs several GiB of local storage and is excluded from the repository. An
empty verified transitive dependency set establishes DP=0 directly; the other
L proofs are analyzed through their compiled target and helper bodies.

LOC counts nonblank, noncomment lines across the complete submitted file,
including imports and local helpers. Total tokens equal input plus output;
cached input and reasoning are already included in those totals. Figure 9 uses
category mean costs. Figure 10 averages DP across each task's three L attempts,
groups tasks into `0`, `(0,5]`, `(5,10]`, `(10,15]`, and `(15,+∞)`, and averages
the task-level signed gains within each group. Gain is `100 * (1 - L/N)`.

The repository includes compact numerical records and provenance. Full agent
logs, credentials, generated proofs, runtime caches, extraction tools, skills,
and papers are excluded. Fresh runs retain their detailed evidence locally.

## Citation

```bibtex
@misc{qharabagh2026vsclreuse,
  author       = {Fetrat Qharabagh, Muhammad and Georgantzas, Georgios Alexandros},
  title        = {{VSCL} Reuse Analysis: Tasks and Reproducibility Scripts},
  year         = {2026},
  howpublished = {GitHub repository, \url{https://github.com/VSCL-x-VERITAS/vscl-reuse-analysis}},
  note         = {Accessed November 12, 2026}
}
```
