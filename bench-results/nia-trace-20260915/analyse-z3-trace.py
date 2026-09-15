#!/usr/bin/env python3
"""Summarise ADR-2112's z3 three-arm reference trace.

The question the table has to answer is not "does z3 beat us" -- the board
already says that -- but **which machinery decides each file**, so that the
next lever is aimed at the machinery that decides rather than the one that
refuses.

Reads the trace TSV (or several, one per shard) and reports, per arm: how many
files it decides, and for the deciding runs which nonlinear engines were
nonzero. A row whose `engine` is `none` on a TIMEOUT says nothing -- z3 prints
a five-key statistic block when it runs out of clock -- so timeouts are
excluded from the engine tally rather than counted as `none`, and the count of
what was excluded is printed.

usage: analyse-z3-trace.py <trace.tsv>...
"""

import collections
import csv
import sys

DECIDED = {"sat", "unsat"}


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2

    rows: list[dict[str, str]] = []
    for path in argv[1:]:
        with open(path, newline="") as handle:
            rows.extend(csv.DictReader(handle, delimiter="\t"))
    rows = [r for r in rows if r.get("arm") and r.get("arm") != "arm"]
    if not rows:
        print("no rows: the trace is empty, which is not a result", file=sys.stderr)
        return 1

    files = {r["path"] for r in rows}
    print(f"rows {len(rows)}   distinct files {len(files)}")

    arms = sorted({r["arm"] for r in rows})
    # An arm that did not see every file cannot be compared to one that did.
    print("\n=== coverage: an arm missing files is not comparable ===")
    for arm in arms:
        seen = {r["path"] for r in rows if r["arm"] == arm}
        print(f"  {arm:<8} {len(seen):>4} of {len(files)} files")

    print("\n=== decided, by arm ===")
    for arm in arms:
        arm_rows = [r for r in rows if r["arm"] == arm]
        decided = [r for r in arm_rows if r["verdict"] in DECIDED]
        sat = sum(1 for r in decided if r["verdict"] == "sat")
        unsat = len(decided) - sat
        pct = 100.0 * len(decided) / len(arm_rows) if arm_rows else 0.0
        print(
            f"  {arm:<8} decided {len(decided):>4} of {len(arm_rows):<4} "
            f"({pct:5.1f} %)   sat {sat:<4} unsat {unsat}"
        )

    print("\n=== engines on the runs that DECIDED (timeouts excluded) ===")
    for arm in arms:
        decided = [r for r in rows if r["arm"] == arm and r["verdict"] in DECIDED]
        if not decided:
            print(f"  {arm:<8} nothing decided, so nothing to attribute")
            continue
        tally = collections.Counter(r["engine"] for r in decided)
        print(f"  {arm}:")
        for engine, count in tally.most_common():
            print(f"      {count:>4}  {engine}")

    # Per-engine participation, which is what "does the bit-blast decide
    # anything" actually asks: a file may light several counters.
    print("\n=== how many DECIDED runs had each engine nonzero ===")
    for arm in arms:
        decided = [r for r in rows if r["arm"] == arm and r["verdict"] in DECIDED]
        if not decided:
            continue
        parts: collections.Counter[str] = collections.Counter()
        for row in decided:
            for engine in row["engine"].split("+"):
                if engine and engine != "none":
                    parts[engine] += 1
        summary = "  ".join(f"{e} {c}" for e, c in sorted(parts.items()))
        print(f"  {arm:<8} of {len(decided):>3} decided: {summary or '(none)'}")

    print("\n=== union: files ANY arm decides ===")
    any_decided = {r["path"] for r in rows if r["verdict"] in DECIDED}
    blast_decided = {
        r["path"] for r in rows if r["arm"] == "nla2bv" and r["verdict"] in DECIDED
    }
    only_blast = blast_decided - {
        r["path"]
        for r in rows
        if r["arm"] in {"default", "qfnia"} and r["verdict"] in DECIDED
    }
    print(f"  any arm          {len(any_decided):>4} of {len(files)}")
    print(f"  the nla2bv arm   {len(blast_decided):>4} of {len(files)}")
    print(f"  ONLY nla2bv      {len(only_blast):>4}")

    print("\n=== wall-clock on the runs that decided (ms) ===")
    for arm in arms:
        times = sorted(
            int(r["wall_ms"])
            for r in rows
            if r["arm"] == arm and r["verdict"] in DECIDED and r["wall_ms"].isdigit()
        )
        if not times:
            continue
        median = times[len(times) // 2]
        print(
            f"  {arm:<8} n {len(times):>4}  min {times[0]:>6}  "
            f"median {median:>6}  max {times[-1]:>6}"
        )

    excluded = sum(1 for r in rows if r["verdict"] not in DECIDED)
    print(
        f"\nexcluded from the engine tally: {excluded} rows that did not decide "
        f"(z3 prints only a five-key statistic block on a timeout, so `engine` "
        f"is uninformative there and is not counted as evidence of `none`)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
