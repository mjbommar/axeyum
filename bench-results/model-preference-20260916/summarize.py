#!/usr/bin/env python3
"""Summarise the ADR-2140 A/B rows: decided per arm, movers, disagreements, time.

Exit status depends on the finding: 1 if any `:status` disagreement, 2 if a
row's timing column fails the unit sanity check (a 24 s budget cannot produce
a 24,000,000 ms row -- the uutils `date` trap this harness replaced).

Usage: summarize.py half1.tsv half2.tsv ... > summary.md
"""

from __future__ import annotations

import csv
import sys

rows = []
for path in sys.argv[1:]:
    with open(path, newline="") as fh:
        rows.extend(csv.DictReader(fh, delimiter="\t"))

if not rows:
    print("no rows", file=sys.stderr)
    sys.exit(2)

BUDGET_MS = 24_000
HEADROOM_MS = 16_000


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
gains = [r for r in rows if not decided(r["A"]) and decided(r["B"])]
losses = [r for r in rows if decided(r["A"]) and not decided(r["B"])]
flips = [r for r in rows if decided(r["A"]) and decided(r["B"]) and r["A"] != r["B"]]
disagree = [
    (arm, r)
    for r in rows
    for arm in ("A", "B")
    if r["status"] in ("sat", "unsat") and decided(r[arm]) and r[arm] != r["status"]
]
aborts = [r for r in rows if r["A_rc"] not in ("0",) or r["B_rc"] not in ("0",)]
both = [r for r in rows if decided(r["A"]) and decided(r["B"])]
sum_a = sum(int(r["A_ms"]) for r in both)
sum_b = sum(int(r["B_ms"]) for r in both)
slower = sum(int(r["B_ms"]) > int(r["A_ms"]) * 1.1 + 50 for r in both)
faster = sum(int(r["A_ms"]) > int(r["B_ms"]) * 1.1 + 50 for r in both)
par2_a = sum(int(r["A_ms"]) if decided(r["A"]) else 2 * BUDGET_MS for r in rows) / len(rows)
par2_b = sum(int(r["B_ms"]) if decided(r["B"]) else 2 * BUDGET_MS for r in rows) / len(rows)

print("| measure | A = `Any` (unset) | B = `AXEYUM_MODEL_PREFERENCE=zero` |")
print("| --- | ---: | ---: |")
print(f"| files | {len(rows)} | {len(rows)} |")
print(f"| decided | {dec_a} | {dec_b} |")
print(f"| sat / unsat | {sat_a} / {unsat_a} | {sat_b} / {unsat_b} |")
print(f"| PAR-2 (ms, 24 s budget) | {par2_a:.0f} | {par2_b:.0f} |")
print(f"| wall on the {len(both)} both-decided files (ms) | {sum_a} | {sum_b} |")
print(
    f"| both-decided files where the other arm is >10 % + 50 ms slower | B slower on {slower} | A slower on {faster} |"
)
print()
print(f"- raw gains (A undecided, B decided): {len(gains)}")
print(f"- raw losses (A decided, B undecided): {len(losses)}")
print(f"- sat/unsat flips between arms: {len(flips)}")
print(
    f"- `:status` disagreements (either arm, decided, against a declared sat/unsat): {len(disagree)}"
)
print(f"- nonzero exit status rows: {len(aborts)}")
print(f"- rows failing the timing-unit sanity check: {len(bad_clock)}")
for r in gains:
    print(f"  - GAIN {r['file']}: A={r['A']}/{r['A_ms']}ms B={r['B']}/{r['B_ms']}ms")
for r in losses:
    print(f"  - LOSS {r['file']}: A={r['A']}/{r['A_ms']}ms B={r['B']}/{r['B_ms']}ms")
for r in flips:
    print(f"  - FLIP {r['file']}: A={r['A']} B={r['B']} status={r['status']}")
for arm, r in disagree:
    print(f"  - DISAGREE {arm} {r['file']}: {r[arm]} vs :status {r['status']}")

# Movers list for the three-pass recheck: every gain, loss and flip. Written
# only when there is one, so a clean run leaves no empty list behind.
if gains or losses or flips:
    with open("movers.txt", "w") as fh:
        corpus = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
        for r in gains + losses + flips:
            fh.write(corpus + r["file"] + "\n")

if disagree:
    sys.exit(1)
if bad_clock:
    sys.exit(2)
