#!/usr/bin/env python3
"""LEMMA-INPUT -- read an A/B TSV and report gains, losses, flips, exit-status
moves and the wall-ratio band.

POLARITY (the runner's header says the same thing): BASE is the lever unset --
the shipped full-rebuild refresh; ARM is `AXEYUM_LIA_INITIAL_BOUND_INDEX=1`.
A GAIN is `unknown` under BASE and decided under ARM.

R5: exit status is its own channel and is reported whether or not a verdict
moved.  R7: with more than one pass, a row whose verdict disagrees ACROSS
passes within one arm is UNSTABLE and is reported separately -- it is not
evidence either way.

The exit status depends on the finding: losses or flips exit non-zero.
"""

import collections
import pathlib
import statistics
import sys

SRC = pathlib.Path(sys.argv[1])

# pass, file, arm, verdict, status, wall_ms, rss
runs = []
for line in SRC.read_text().splitlines():
    if not line.strip():
        continue
    p = line.split("\t")
    if len(p) != 7:
        print(f"MALFORMED: {line!r}")
        sys.exit(4)
    runs.append((p[0], p[1], p[2], p[3], int(p[4]), int(p[5]), p[6]))

files = sorted({r[1] for r in runs})
passes = sorted({r[0] for r in runs})
print(f"arm-runs: {len(runs)}   files: {len(files)}   passes: {len(passes)} ({', '.join(passes)})")

by = collections.defaultdict(dict)  # file -> (pass, arm) -> row
for r in runs:
    by[r[1]][(r[0], r[2])] = r

DECIDED = {"sat", "unsat"}
gains, losses, flips, status_moves, unstable = [], [], [], [], []
ratios = []
for f in files:
    base_v = {by[f][(p, "base")][3] for p in passes if (p, "base") in by[f]}
    arm_v = {by[f][(p, "arm")][3] for p in passes if (p, "arm") in by[f]}
    base_s = {by[f][(p, "base")][4] for p in passes if (p, "base") in by[f]}
    arm_s = {by[f][(p, "arm")][4] for p in passes if (p, "arm") in by[f]}
    if len(base_v) > 1 or len(arm_v) > 1:
        unstable.append((f, sorted(base_v), sorted(arm_v)))
        continue
    if not base_v or not arm_v:
        continue
    b = next(iter(base_v))
    a = next(iter(arm_v))
    if b not in DECIDED and a in DECIDED:
        gains.append((f, b, a))
    if b in DECIDED and a not in DECIDED:
        losses.append((f, b, a))
    if b in DECIDED and a in DECIDED and a != b:
        flips.append((f, b, a))
    if base_s != arm_s:
        status_moves.append((f, sorted(base_s), sorted(arm_s)))
    bw = statistics.median(by[f][(p, "base")][5] for p in passes if (p, "base") in by[f])
    aw = statistics.median(by[f][(p, "arm")][5] for p in passes if (p, "arm") in by[f])
    if bw > 0:
        ratios.append((aw / bw, f, bw, aw))

print()
print(f"GAINS   (unknown -> decided): {len(gains)}")
for f, b, a in gains:
    print(f"  {b} -> {a}\t{f}")
print(f"LOSSES  (decided -> unknown): {len(losses)}")
for f, b, a in losses:
    print(f"  {b} -> {a}\t{f}")
print(f"FLIPS   (sat <-> unsat):      {len(flips)}")
for f, b, a in flips:
    print(f"  {b} -> {a}\t{f}")
print(f"EXIT-STATUS MOVES (R5):       {len(status_moves)}")
for f, b, a in status_moves:
    print(f"  {b} -> {a}\t{f}")
print(f"UNSTABLE across passes:       {len(unstable)}")
for f, b, a in unstable:
    print(f"  base={b} arm={a}\t{f}")

if ratios:
    ratios.sort()
    vals = [r[0] for r in ratios]
    print()
    print(f"arm/base wall ratio over {len(vals)} files: "
          f"min {vals[0]:.3f}  p10 {vals[len(vals)//10]:.3f}  "
          f"median {statistics.median(vals):.3f}  "
          f"p90 {vals[min(len(vals)-1, 9*len(vals)//10)]:.3f}  max {vals[-1]:.3f}")
    print("  ten largest speedups (arm faster):")
    for ratio, f, bw, aw in ratios[:10]:
        print(f"    {ratio:.3f}\tbase={bw} ms arm={aw} ms\t{f}")

print()
print("exit status by arm (its own channel):")
for arm in ("base", "arm"):
    counts = collections.Counter(r[4] for r in runs if r[2] == arm)
    print(f"  {arm}: {dict(sorted(counts.items()))}")
print("verdicts by arm:")
for arm in ("base", "arm"):
    counts = collections.Counter(r[3] for r in runs if r[2] == arm)
    print(f"  {arm}: {dict(sorted(counts.items()))}")

if losses or flips:
    print()
    print("FINDING: the arm lost or flipped a verdict.")
    sys.exit(1)
