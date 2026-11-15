"""LOC, per-task means, category means, and DP groups for Figures 9 and 10."""

from __future__ import annotations

from collections import Counter, defaultdict
import csv
from pathlib import Path
from statistics import mean

METRICS = ("time_seconds", "total_tokens", "submitted_loc")
DP_LABELS = ("0", "(0, 5]", "(5, 10]", "(10, 15]", "(15, +∞)")


def lean_code_lines(source: str) -> int:
    """Count full-file nonblank, noncomment lines, including local helpers.

    Handle nested block comments, line comments, strings, raw strings, and
    character literals. Keep comment delimiters inside literals unchanged.
    """
    result = []
    depth = 0
    string = False
    raw_end = ""
    i = 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
                result.append(" ")
            else:
                if source[i] == "\n":
                    result.append("\n")
                i += 1
        elif raw_end:
            if source.startswith(raw_end, i):
                result.append(raw_end)
                i += len(raw_end)
                raw_end = ""
            else:
                result.append(source[i])
                i += 1
        elif string:
            result.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
            else:
                if source[i] == '"':
                    string = False
                i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = len(source) if j < 0 else j
        elif source.startswith("/-", i):
            depth = 1
            result.append(" ")
            i += 2
        elif source[i] == "'" and i + 2 < len(source):
            # Distinguish a quoted character from apostrophes in Lean names.
            j = i + 2 if source[i + 1] != "\\" else i + 3
            if j < len(source) and source[j] == "'":
                result.append(source[i:j + 1])
                i = j + 1
            else:
                result.append(source[i])
                i += 1
        elif source[i] == "r" and i + 1 < len(source) and source[i + 1] in '#"':
            j = i + 1
            while j < len(source) and source[j] == "#":
                j += 1
            if j < len(source) and source[j] == '"':
                raw_end = '"' + source[i + 1:j]
                result.append(source[i:j + 1])
                i = j + 1
            else:
                result.append(source[i])
                i += 1
        else:
            result.append(source[i])
            if source[i] == '"':
                string = True
            i += 1
    if depth or string or raw_end:
        raise ValueError("unterminated Lean comment or literal")
    return sum(bool(line.strip()) for line in "".join(result).splitlines())


def load_attempts(path: Path) -> list[dict]:
    with path.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != 360 or len({r["run_id"] for r in rows}) != 360:
        raise ValueError("expected 360 unique attempts")
    for r in rows:
        if r["accepted"] != "true" or r["condition"] not in ("N", "L"):
            raise ValueError("expected accepted N/L attempts")
        for field in METRICS:
            r[field] = float(r[field])
            if r[field] <= 0:
                raise ValueError("resource costs must be positive")
        r["direct_proof_declarations"] = int(r["direct_proof_declarations"])
        if r["direct_proof_declarations"] < 0 or (r["condition"] == "N" and r["direct_proof_declarations"]):
            raise ValueError("invalid DP count")
        for field in ("input_tokens", "cached_input_tokens", "output_tokens", "reasoning_output_tokens"):
            r[field] = int(r[field])
        if r["total_tokens"] != r["input_tokens"] + r["output_tokens"]:
            raise ValueError("cached input and reasoning must not be counted twice")
        if not (0 <= r["cached_input_tokens"] <= r["input_tokens"] and
                0 <= r["reasoning_output_tokens"] <= r["output_tokens"]):
            raise ValueError("invalid token breakdown")
    return rows


def task_means(rows: list[dict]) -> list[dict]:
    groups = defaultdict(list)
    for row in rows:
        groups[row["task_id"]].append(row)
    if len(groups) != 60:
        raise ValueError("expected 60 tasks")
    tasks = []
    for task_id, attempts in sorted(groups.items()):
        if Counter(r["condition"] for r in attempts) != {"N": 3, "L": 3}:
            raise ValueError(f"expected three N/L repetitions: {task_id}")
        if len({r["category"] for r in attempts}) != 1:
            raise ValueError(f"category differs across repetitions: {task_id}")
        item = {"task_id": task_id, "category": attempts[0]["category"]}
        for condition in ("N", "L"):
            selected = [r for r in attempts if r["condition"] == condition]
            if {r["repetition"] for r in selected} != {"01", "02", "03"}:
                raise ValueError(f"unmatched repetitions: {task_id}")
            for field in METRICS:
                item[f"{condition}_{field}"] = mean(r[field] for r in selected)
        item["mean_dp"] = mean(r["direct_proof_declarations"] for r in attempts if r["condition"] == "L")
        item["dp_group"] = next((i for i, boundary in enumerate((0, 5, 10, 15)) if item["mean_dp"] <= boundary), 4)
        for field in METRICS:
            item[f"gain_{field}"] = 100 * (1 - item[f"L_{field}"] / item[f"N_{field}"])
        tasks.append(item)
    if Counter(r["category"] for r in tasks) != {"C1": 30, "C2": 20, "C3": 10}:
        raise ValueError("expected C1=30, C2=20, C3=10")
    return tasks


def figure_values(tasks: list[dict]) -> dict:
    categories, groups = [], []
    for category in ("C1", "C2", "C3"):
        selected = [t for t in tasks if t["category"] == category]
        row = {"category": category, "tasks": len(selected), "mean_dp": mean(t["mean_dp"] for t in selected)}
        for field in METRICS:
            for condition in ("N", "L"):
                row[f"{condition}_{field}"] = mean(t[f"{condition}_{field}"] for t in selected)
            row[f"gain_{field}"] = 100 * (1 - row[f"L_{field}"] / row[f"N_{field}"])
        categories.append(row)
    for index, label in enumerate(DP_LABELS):
        selected = [t for t in tasks if t["dp_group"] == index]
        row = {"dp_group": label, "tasks": len(selected)}
        for field in METRICS:
            row[f"mean_gain_{field}"] = mean(t[f"gain_{field}"] for t in selected) if selected else None
        groups.append(row)
    return {"figure9": categories, "figure10": groups, "tasks_with_library_use": sum(t["mean_dp"] > 0 for t in tasks)}
