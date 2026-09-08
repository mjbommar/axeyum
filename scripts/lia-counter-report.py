#!/usr/bin/env python3
"""Summarise a `scripts/lia-counter-sweep.sh` output directory.

The one rule this script enforces on itself: **a group that did not run is
never averaged in.** The `; lia …` line prints `measured` / `not-reached` /
`off` in front of each group precisely so a reader can tell a measured zero
from a structural one, and a summary that means anything has to honour that.
So every aggregate below states its own denominator -- the number of files in
which the group was `measured` -- rather than dividing by the file count.

Usage:
  scripts/lia-counter-report.py <sweep-dir> [<sweep-dir> ...]
"""

from __future__ import annotations

import csv
import os

import sys

GROUPS = ("offline", "theory", "propagation")


def parse_lia_line(line: str) -> dict[str, str] | None:
    if not line.startswith("; lia "):
        return None
    out: dict[str, str] = {}
    for token in line[len("; lia "):].strip().split():
        if "=" not in token:
            continue
        key, value = token.split("=", 1)
        out[key] = value
    return out


def parse_route_line(line: str) -> dict[str, str] | None:
    if not line.startswith("; route "):
        return None
    out: dict[str, str] = {}
    for token in line[len("; route "):].strip().split():
        if "=" in token:
            key, value = token.split("=", 1)
            out[key] = value
    return out


def load(sweep_dir: str) -> list[dict]:
    index_path = os.path.join(sweep_dir, "index.tsv")
    rows: list[dict] = []
    with open(index_path, newline="") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            log = os.path.join(sweep_dir, f"{row['index']}.log")
            record = {
                "file": row["file"],
                "verdict": row["verdict"],
                "wall_ms": int(row["wall_ms"]),
                "lia": None,
                "route": None,
            }
            if os.path.exists(log):
                with open(log, errors="replace") as fh:
                    for line in fh:
                        lia = parse_lia_line(line)
                        if lia is not None:
                            record["lia"] = lia
                        route = parse_route_line(line)
                        if route is not None:
                            record["route"] = route
            rows.append(record)
    return rows


def as_int(counters: dict[str, str], key: str) -> int:
    try:
        return int(counters.get(key, "0"))
    except ValueError:
        return 0


def report(sweep_dir: str) -> None:
    rows = load(sweep_dir)
    print(f"=== {sweep_dir}  ({len(rows)} files)")

    verdicts: dict[str, int] = {}
    for row in rows:
        verdicts[row["verdict"]] = verdicts.get(row["verdict"], 0) + 1
    print("  verdicts: " + ", ".join(f"{k}={v}" for k, v in sorted(verdicts.items())))

    no_trace = [r for r in rows if r["lia"] is None]
    if no_trace:
        print(f"  no `; lia` line at all (aborted before the trace printed): {len(no_trace)}")

    # Binding route, from the route trail. This is the field the 2026-09-07
    # attribution lane established as the one to classify by: the route that
    # SPENT the budget, not the route that printed last.
    binders: dict[str, int] = {}
    for row in rows:
        route = row["route"] or {}
        key = route.get("bound_by", "NA") if row["verdict"] == "unknown" else None
        if key is not None:
            binders[key] = binders.get(key, 0) + 1
    if binders:
        print("  bound_by on undecided files: "
              + ", ".join(f"{k}={v}" for k, v in sorted(binders.items(), key=lambda kv: -kv[1])))

    for group in GROUPS:
        readings: dict[str, int] = {}
        for row in rows:
            lia = row["lia"]
            reading = lia.get(group, "unavailable") if lia else "absent"
            readings[reading] = readings.get(reading, 0) + 1
        print(f"  group {group}: "
              + ", ".join(f"{k}={v}" for k, v in sorted(readings.items())))

    def totals(group: str, keys: list[str]) -> None:
        live = [r for r in rows if r["lia"] and r["lia"].get(group) == "measured"]
        print(f"  --- {group}: totals over the {len(live)} files where it was MEASURED")
        if not live:
            return
        for key in keys:
            values = [as_int(r["lia"], key) for r in live]
            values.sort()
            total = sum(values)
            median = values[len(values) // 2]
            print(f"      {key:<26} total={total:<14} median={median:<12} max={values[-1]}")

    totals("offline", [
        "offline_calls", "offline_constraints", "offline_early_exits",
        "gomory_calls", "gomory_decided", "gomory_rounds", "gomory_cuts",
        "gomory_pivots", "gomory_rows", "gomory_columns",
        "bnb_roots", "bnb_nodes", "bnb_budget_exhausted",
        "simplex_solves", "simplex_pivots", "simplex_rows", "simplex_columns",
        "simplex_declines", "lp_relaxations",
    ])
    totals("theory", [
        "theory_asserts", "feasibility_checks", "arena_clones", "arena_clone_nodes",
        "live_literals", "filter_refuted", "filter_integral", "filter_inconclusive",
        "core_minimizations", "core_minimization_probes",
    ])
    totals("propagation", [
        "propagate_calls", "propagate_atoms", "propagate_probes", "propagations_offered",
    ])

    # The two questions part B was scoped against.
    live = [r for r in rows if r["lia"] and r["lia"].get("theory") == "measured"]
    if live:
        clones = sum(as_int(r["lia"], "arena_clones") for r in live)
        nodes = sum(as_int(r["lia"], "arena_clone_nodes") for r in live)
        asserts = sum(as_int(r["lia"], "theory_asserts") for r in live)
        print(f"  ARENA CLONING: {clones} clones, {nodes} nodes copied, "
              f"over {asserts} asserts "
              f"({nodes / max(asserts, 1):.1f} nodes/assert)")
    live = [r for r in rows if r["lia"] and r["lia"].get("offline") == "measured"]
    if live:
        calls = sum(as_int(r["lia"], "offline_calls") for r in live)
        probes = sum(as_int(r["lia"], "core_minimization_probes") for r in live)
        print(f"  CORE MINIMISATION: {probes} offline re-decisions of {calls} "
              f"offline calls ({100 * probes / max(calls, 1):.1f}%)")

    # Per-file leaders, so a total is never mistaken for a population effect.
    print("  --- heaviest single files")
    def top(key: str, n: int = 5) -> None:
        have = [r for r in rows if r["lia"] and key in r["lia"]]
        have.sort(key=lambda r: -as_int(r["lia"], key))
        for row in have[:n]:
            if as_int(row["lia"], key) == 0:
                break
            print(f"      {key}={as_int(row['lia'], key):<12} "
                  f"{row['verdict']:<8} {os.path.basename(row['file'])}")
    top("simplex_pivots")
    top("gomory_pivots")
    top("bnb_nodes")
    top("arena_clone_nodes")
    top("propagate_probes")
    print()


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    for sweep_dir in sys.argv[1:]:
        report(sweep_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
