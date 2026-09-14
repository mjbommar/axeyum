#!/usr/bin/env python3
"""SKELETON-REACH -- summarize one A/B phase.

    ab-summarize.py <phase.tsv> [label]

Reports GAIN / LOSS / FLIP against a shipped-arm baseline, and -- because a
gain attributable to timing is not attributable to the lever -- labels every
gain by whether the arm's ingest refusal actually went away:

  EXPLAINED    base stopped at `fd:parse` (a give-up) and the arm did not
  UNEXPLAINED  the base did NOT stop at ingest, so this lever did not cause it

An UNEXPLAINED gain is NAMED, never folded into the total.  A FLIP
(sat<->unsat) is a P0 and is printed on its own line with the file.
"""
import collections
import csv
import math
import sys

F = ["file", "base_v", "base_rung", "base_ms", "base_giveup",
     "arm_v", "arm_rung", "arm_ms", "arm_giveup", "order"]
DEC = {"sat", "unsat"}


def wilson(k, n):
    if n == 0:
        return "n/a"
    z = 1.959963985
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return f"[{100 * max(0, c - h):.1f}%, {100 * min(1, c + h):.1f}%]"


rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t", fieldnames=F))
rows = [r for r in rows if r["file"] != "file"]
label = sys.argv[2] if len(sys.argv) > 2 else sys.argv[1]

nb = sum(1 for r in rows if r["base_v"] in DEC)
na = sum(1 for r in rows if r["arm_v"] in DEC)
gains = [r for r in rows if r["base_v"] not in DEC and r["arm_v"] in DEC]
losses = [r for r in rows if r["base_v"] in DEC and r["arm_v"] not in DEC]
flips = [r for r in rows if r["base_v"] in DEC and r["arm_v"] in DEC and r["base_v"] != r["arm_v"]]

print(f"{label}: {len(rows)} rows   base decided {nb}   arm decided {na}   "
      f"net {na - nb:+d}   GAIN {len(gains)}  LOSS {len(losses)}  FLIP {len(flips)}")
print(f"  gain rate {len(gains)}/{len(rows)} Wilson95 {wilson(len(gains), len(rows))}")

tb = sum(int(r["base_ms"] or 0) for r in rows)
ta = sum(int(r["arm_ms"] or 0) for r in rows)
print(f"  attributed wall: base {tb / 1000:.1f}s  arm {ta / 1000:.1f}s  "
      f"ratio {ta / tb if tb else float('nan'):.2f}x")

expl = collections.Counter()
for r in gains:
    kind = "EXPLAINED" if r["base_giveup"] != "none" and r["arm_giveup"] == "none" else "UNEXPLAINED"
    expl[kind] += 1
    print(f"  GAIN {kind:<11} {r['base_v']}->{r['arm_v']} rung={r['arm_rung']:<8} "
          f"{r['arm_ms']:>6}ms base_giveup={r['base_giveup']:<14} {r['file'].split('/', 1)[1][:62]}")
for r in losses:
    print(f"  LOSS             {r['base_v']}->{r['arm_v']} {r['file'].split('/', 1)[1][:62]}")
for r in flips:
    print(f"  *** FLIP (P0) *** {r['base_v']}->{r['arm_v']} {r['file']}")
print("  gains by attribution:", dict(expl))

# LEVER LIVENESS: rows where the base's ingest refusal disappeared in the arm,
# whether or not the verdict changed. A phase where this is 0 has not exercised
# the lever at all, and its zero is a WEAK control -- say so rather than
# reporting it as a measured null.
live = [r for r in rows if r["base_giveup"] != "none" and r["arm_giveup"] == "none"]
print(f"  LEVER LIVENESS: {len(live)} rows lost their base give-up in the arm "
      f"({'non-vacuous' if live else 'VACUOUS -- the lever never fired here'})")
