"""Recompute paper tables and render Figures 9 and 10 as PDF and SVG."""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from metrics import DP_LABELS, METRICS, figure_values, load_attempts, task_means

HERE = Path(__file__).resolve().parent


def check_paper(values: dict) -> None:
    reference = {
        "C1": ((364.6, 374.0), (280.3, 285.4), (-2.6, -10.5, -1.8), 0.34),
        "C2": ((355.1, 153.4), (290.5, 169.5), (56.8, 38.8, 41.7), 9.48),
        "C3": ((640.5, 244.5), (639.1, 261.4), (61.8, 56.7, 59.1), 17.73),
    }
    failures = []
    def equal(label, actual, expected, digits=1):
        if actual is None or f"{actual:.{digits}f}" != f"{expected:.{digits}f}":
            failures.append(f"{label}: computed {actual}; paper {expected}")
    for row in values["figure9"]:
        times, locs, gains, dp = reference[row["category"]]
        for condition, time, loc in zip(("N", "L"), times, locs):
            equal(f"{row['category']} {condition} time", row[f"{condition}_time_seconds"], time)
            equal(f"{row['category']} {condition} LOC", row[f"{condition}_submitted_loc"], loc)
        for metric, gain in zip(METRICS, gains):
            equal(f"{row['category']} {metric} gain", row[f"gain_{metric}"], gain)
        equal(f"{row['category']} mean DP", row["mean_dp"], dp, 2)
    for group, gains in ((0, (-4.3, -23.4, -3.9)), (4, (65.7, 51.5, 54.2))):
        for metric, gain in zip(METRICS, gains):
            equal(f"DP {DP_LABELS[group]} {metric}", values["figure10"][group][f"mean_gain_{metric}"], gain)
    if values["tasks_with_library_use"] != 33:
        failures.append("the paper reports 33 tasks with DP > 0")
    if failures:
        raise ValueError("published-value check failed:\n" + "\n".join(failures))
    print("published rounded values match")


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def render(tasks: list[dict], values: dict, output: Path) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D

    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                         "svg.hashsalt": "vscl-reuse-analysis", "pdf.fonttype": 42})
    colors = {"N": "#4c78a8", "L": "#f28e2b"}
    titles = ("(a) Time", "(b) Total tokens", "(c) Complete submitted Lean code")
    ylabels = ("Mean time (seconds)", "Mean total tokens (millions)", "Mean lines of Lean code")
    def save(fig, name):
        fig.savefig(output / (name + ".pdf"), metadata={"Creator": "VSCL reuse analysis", "CreationDate": None, "ModDate": None})
        fig.savefig(output / (name + ".svg"), metadata={"Creator": "VSCL reuse analysis", "Date": None})
        plt.close(fig)
    fig, axes = plt.subplots(3, 1, figsize=(7.8, 9))
    for ax, metric, title, ylabel in zip(axes, METRICS, titles, ylabels):
        scale = 1e6 if metric == "total_tokens" else 1
        for index, row in enumerate(values["figure9"]):
            n, l = (row[f"{c}_{metric}"] / scale for c in ("N", "L"))
            for offset, value, condition in ((-0.14, n, "N"), (0.14, l, "L")):
                ax.bar(index + offset, value, 0.28, color=colors[condition])
                label = f"{value:.2f}" if scale != 1 else f"{value:.1f}"
                ax.annotate(label, (index + offset, value), xytext=(0, 4), textcoords="offset points", ha="center", fontsize=9)
            gain = row[f"gain_{metric}"]
            ax.annotate(f"{'Gain' if gain >= 0 else 'Loss'}: {abs(gain):.1f}%", (index, max(n, l)), xytext=(0, 25), textcoords="offset points", ha="center", fontsize=10)
        maximum = max(r[f"{c}_{metric}"] / scale for r in values["figure9"] for c in ("N", "L"))
        ax.set_ylim(0, 1.55 * maximum)
        ax.set_xticks(range(3), ("C1", "C2", "C3"))
        ax.set_ylabel(ylabel)
        ax.set_title(title, y=-0.32, fontsize=11)
        ax.spines[["top", "right"]].set_visible(False)
    fig.legend(handles=[Line2D([0], [0], color=colors[c], lw=8, label=label) for c, label in (("N", "N: Mathlib"), ("L", "L: Mathlib + library"))], loc="upper right", ncols=2, frameon=False)
    fig.subplots_adjust(left=0.15, right=0.97, top=0.93, bottom=0.07, hspace=0.65)
    save(fig, "figure9")

    fig, axes = plt.subplots(3, 1, figsize=(7.8, 9))
    for ax, metric, title, ylabel in zip(axes, METRICS, titles, ("Time gain (%)", "Total-token gain (%)", "Code-line gain (%)")):
        for group in range(5):
            selected = sorted((t for t in tasks if t["dp_group"] == group), key=lambda t: t["task_id"])
            offsets = [0] if len(selected) <= 1 else [-0.17 + 0.34 * i / (len(selected) - 1) for i in range(len(selected))]
            ax.scatter([group + x for x in offsets], [t[f"gain_{metric}"] for t in selected], s=22, color=colors["N"], alpha=0.65, edgecolors="none")
        means = [r[f"mean_gain_{metric}"] for r in values["figure10"]]
        ax.plot(range(5), [float("nan") if m is None else m for m in means], "D--", color="#c85141", markersize=6, linewidth=1.1)
        ax.axhline(0, color="#777777", linewidth=0.7)
        ax.set_xticks(range(5), DP_LABELS)
        ax.set_xlabel("Library usage (mean DP)")
        ax.set_ylabel(ylabel)
        ax.set_title(title, y=-0.42, fontsize=11)
        ax.spines[["top", "right"]].set_visible(False)
        ax.margins(x=0.08, y=0.15)
    fig.legend(handles=[Line2D([0], [0], marker="o", linestyle="none", color=colors["N"], label="Task"), Line2D([0], [0], marker="D", linestyle="--", color="#c85141", label="Group mean")], loc="upper right", ncols=2, frameon=False)
    fig.subplots_adjust(left=0.15, right=0.97, top=0.93, bottom=0.11, hspace=0.85)
    save(fig, "figure10")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=HERE.parent / "results/attempts.csv")
    parser.add_argument("--output", type=Path, default=HERE.parent / "generated")
    parser.add_argument("--tables-only", action="store_true", help="No plotting dependency required")
    parser.add_argument("--check-paper", action="store_true", help="Compare against the published rounded values")
    args = parser.parse_args()
    tasks = task_means(load_attempts(args.data))
    values = figure_values(tasks)
    if args.check_paper:
        check_paper(values)
    args.output.mkdir(parents=True, exist_ok=True)
    write_csv(args.output / "task_means.csv", tasks)
    write_csv(args.output / "figure9_values.csv", values["figure9"])
    write_csv(args.output / "figure10_values.csv", values["figure10"])
    (args.output / "figure_values.json").write_text(json.dumps(values, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    if not args.tables_only:
        render(tasks, values, args.output)
    print(f"wrote figure data{' and PDF/SVG plots' if not args.tables_only else ''} to {args.output}")


if __name__ == "__main__":
    main()
