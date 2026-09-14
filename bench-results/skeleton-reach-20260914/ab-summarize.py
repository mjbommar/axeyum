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

# WHAT COUNTS AS EXPLAINED.  This lever can only act by removing an INGEST
# refusal, so a gain is attributable to it only if the base row carried one.
# The first spelling here was `base_giveup != "none"`, which also matched a
# base row that simply TIMED OUT -- and the control division promptly produced
# such a row, `unknown -> sat` at 23,962 ms with the rung ABSENT, labelled
# EXPLAINED. That is a timing gain wearing the lever's name. A gain the lever
# cannot have caused must read UNEXPLAINED and be named.
INGEST_GIVEUP = {"ResourceLimit", "Error"}
expl = collections.Counter()
for r in gains:
    kind = "EXPLAINED" if r["base_giveup"] in INGEST_GIVEUP and r["arm_giveup"] == "none" else "UNEXPLAINED"
    expl[kind] += 1
    print(f"  GAIN {kind:<11} {r['base_v']}->{r['arm_v']} rung={r['arm_rung']:<8} "
          f"{r['arm_ms']:>6}ms base_giveup={r['base_giveup']:<14} {r['file'].split('/', 1)[1][:62]}")
for r in losses:
    print(f"  LOSS             {r['base_v']}->{r['arm_v']} {r['file'].split('/', 1)[1][:62]}")
for r in flips:
    print(f"  *** FLIP (P0) *** {r['base_v']}->{r['arm_v']} {r['file']}")
print("  gains by attribution:", dict(expl))

# LEVER LIVENESS, in TWO columns, because the strict one under-reports.
#
# A row whose ingest refusal the arm removes usually does NOT end with no
# give-up at all: it now reaches the ladder and spends the budget there, so it
# ends at `Watchdog`. Counting only `arm_giveup == none` therefore misses every
# row where the lever fired and the file still went undecided -- which on the
# control division is exactly the population that proves the control is not
# vacuous. So `FIRED` is the honest liveness column and `RESOLVED` is the
# subset that also finished.
#
# A phase where FIRED is 0 has not exercised the lever at all, and its zero is
# a WEAK control. Say so rather than reporting it as a measured null.
INGEST = INGEST_GIVEUP
fired = [r for r in rows if r["base_giveup"] in INGEST and r["arm_giveup"] != r["base_giveup"]]
resolved = [r for r in fired if r["arm_giveup"] == "none"]
print(f"  LEVER LIVENESS: FIRED on {len(fired)} rows (base give-up was an ingest refusal and "
      f"the arm's is not), of which RESOLVED {len(resolved)} "
      f"({'non-vacuous' if fired else 'VACUOUS -- the lever never fired here'})")
for r in fired:
    print(f"    fired {r['base_giveup']:<14}-> {r['arm_giveup']:<12} {r['base_v']}->{r['arm_v']} "
          f"{r['file'].split('/', 1)[1][:60]}")
