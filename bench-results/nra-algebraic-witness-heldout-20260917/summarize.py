#!/usr/bin/env python3
"""Summarise ADR-2134 A/B rows (`ab-cad-env.sh` output): decided per arm,
movers, flips, `:status` disagreements, exit statuses.

Exit status depends on the finding: 1 if any `:status` disagreement or any
sat/unsat flip, 2 if a row's timing column fails the unit sanity check (a 24 s
budget cannot produce a 24,000,000 ms row -- the uutils `date` trap), or if
there are no rows.

Usage: summarize.py [--movers FILE] shard0.tsv shard1.tsv ... > summary.md
  --movers FILE  write the absolute corpus paths of every raw mover (gain or
                 loss) to FILE, one per line, for the recheck script.
"""

from __future__ import annotations

import csv
import sys

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
BUDGET_MS = 24_000
HEADROOM_MS = 16_000

args = sys.argv[1:]
movers_out = None
if args and args[0] == "--movers":
    movers_out = args[1]
    args = args[2:]

rows = []
for path in args:
    with open(path, newline="") as fh:
        rows.extend(csv.DictReader(fh, delimiter="\t"))

if not rows:
    print("no rows", file=sys.stderr)
    sys.exit(2)


def decided(v: str) -> bool:
    return v in ("sat", "unsat")


bad_clock = [
    r
    for r in rows
    if int(r["A_ms"]) > BUDGET_MS + HEADROOM_MS + 5_000
    or int(r["B_ms"]) > BUDGET_MS + HEADROOM_MS + 5_000
]
dec_a = sum(decided(r["A"]) for r in rows)
dec_b = sum(decided(r["B"]) for r in rows)
sat_a = sum(r["A"] == "sat" for r in rows)
sat_b = sum(r["B"] == "sat" for r in rows)
unsat_a = sum(r["A"] == "unsat" for r in rows)
unsat_b = sum(r["B"] == "unsat" for r in rows)
none_rows = [r for r in rows if r["A"] == "none" or r["B"] == "none"]
gains = [r for r in rows if not decided(r["A"]) and decided(r["B"])]
losses = [r for r in rows if decided(r["A"]) and not decided(r["B"])]
flips = [r for r in rows if decided(r["A"]) and decided(r["B"]) and r["A"] != r["B"]]
disagree = [
    (arm, r)
    for r in rows
    for arm in ("A", "B")
    if r["status"] in ("sat", "unsat") and decided(r[arm]) and r[arm] != r["status"]
]
comparable = sum(
    1 for r in rows for arm in ("A", "B") if r["status"] in ("sat", "unsat") and decided(r[arm])
)
aborts = [r for r in rows if r["A_rc"] != "0" or r["B_rc"] != "0"]
both = [r for r in rows if decided(r["A"]) and decided(r["B"])]
sum_a = sum(int(r["A_ms"]) for r in both)
sum_b = sum(int(r["B_ms"]) for r in both)
par2_a = sum(int(r["A_ms"]) if decided(r["A"]) else 2 * BUDGET_MS for r in rows) / len(rows)
par2_b = sum(int(r["B_ms"]) if decided(r["B"]) else 2 * BUDGET_MS for r in rows) / len(rows)

print("| measure | A = `single-cell` (shipped) | B = `algebraic-witness` |")
print("| --- | ---: | ---: |")
print(f"| files | {len(rows)} | {len(rows)} |")
print(f"| decided | {dec_a} | {dec_b} |")
print(f"| sat / unsat | {sat_a} / {unsat_a} | {sat_b} / {unsat_b} |")
print(f"| PAR-2 (ms, 24 s budget) | {par2_a:.0f} | {par2_b:.0f} |")
print(f"| wall on the {len(both)} both-decided files (ms) | {sum_a} | {sum_b} |")
print()
print(f"- delta (B - A decided): {dec_b - dec_a:+d}")
print(f"- raw gains (A undecided, B decided): {len(gains)}")
for r in gains:
    print(f"    - {r['file']}  A={r['A']}@{r['A_ms']}ms  B={r['B']}@{r['B_ms']}ms")
print(f"- raw losses (A decided, B undecided): {len(losses)}")
for r in losses:
    print(f"    - {r['file']}  A={r['A']}@{r['A_ms']}ms  B={r['B']}@{r['B_ms']}ms")
print(f"- sat/unsat flips between arms: {len(flips)}")
for r in flips:
    print(f"    - {r['file']}  A={r['A']}  B={r['B']}")
print(
    f"- `:status` disagreements (either arm, decided, against a declared sat/unsat): "
    f"{len(disagree)} over {comparable} comparable verdicts"
)
for arm, r in disagree:
    print(f"    - {r['file']}  arm {arm}={r[arm]}  :status={r['status']}")
print(f"- arm runs without a verdict token: {len(none_rows)}")
print(f"- nonzero exit status rows: {len(aborts)}")
for r in aborts:
    print(f"    - {r['file']}  A_rc={r['A_rc']}  B_rc={r['B_rc']}")
print(f"- rows failing the timing unit sanity check: {len(bad_clock)}")

if movers_out is not None:
    with open(movers_out, "w") as fh:
        for r in gains + losses:
            fh.write(CORPUS + r["file"] + "\n")

if bad_clock:
    sys.exit(2)
if disagree or flips:
    sys.exit(1)
