#!/usr/bin/env python3
"""Select the boundary population for the variance test, from the arm sweeps.

Usage:
    python3 scripts/inprocess-cost-boundary.py <out.txt> <arm.jsonl> [<arm.jsonl> ...]

A variance test run over the whole corpus would spend almost all of its budget
on files that decide in 90 ms and cannot move. The files where run-to-run spread
can change an ANSWER are the ones near the cutoff, and they are selected by a
rule fixed here rather than by looking at which files happened to look
interesting:

* the arms disagree on whether the file was decided at all, or
* some arm decided it later than 60% of the budget, or
* a pass was cut off by its deadline on that file.

The third is the one a naive "near the budget" rule misses: a file that spends
its whole inprocessing slice and then decides in 90 ms of search is nowhere near
the budget in wall time, and is exactly where a wall-clock cutoff is deciding
how much of the pass runs.
"""

import json
import sys


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    out_path = sys.argv[1]
    arms = {}
    for path in sys.argv[2:]:
        rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
        if not rows:
            print(f"FAIL: {path} has no rows", file=sys.stderr)
            return 1
        arms[rows[0]["arm"]] = {r["file"]: r for r in rows}

    populations = {frozenset(v) for v in arms.values()}
    if len(populations) != 1:
        print("FAIL: arms cover different files", file=sys.stderr)
        return 1
    files = sorted(next(iter(populations)))

    def decided(row):
        return row["verdict"] in ("sat", "unsat")

    selected = []
    for f in files:
        rows = [arms[a][f] for a in arms]
        budget = rows[0]["budget_ms"]
        flip = len({decided(r) for r in rows}) > 1
        near = any(decided(r) and r["wall_ms"] > 0.6 * budget for r in rows)
        truncated = any(
            r.get("counters", {}).get(k) == 1.0
            for r in rows
            for k in ("bve_deadline_expired", "subsume_deadline_expired", "vivify_deadline_expired")
        )
        if flip or near or truncated:
            selected.append(f)
            tags = "".join(t for t, on in (("F", flip), ("N", near), ("T", truncated)) if on)
            cells = " ".join(f"{a}={arms[a][f]['verdict']}/{arms[a][f]['wall_ms']}" for a in arms)
            print(f"  [{tags:3s}] {cells}  {f.split('/')[-1]}")

    if not selected:
        # No boundary files is a real possible answer and a suspicious one: it
        # would mean nothing in the corpus is close enough to the cutoff for
        # variance to matter. Say so rather than writing an empty file that a
        # later run would silently measure nothing from.
        print("FAIL: no boundary files selected — nothing to vary", file=sys.stderr)
        return 1
    with open(out_path, "w", encoding="utf-8") as handle:
        handle.write("\n".join(selected) + "\n")
    print(f"\nselected {len(selected)} of {len(files)} files -> {out_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
