#!/usr/bin/env python3
"""SILENT-HANG -- summarise the interleaved A/B.

POLARITY (restated here so a reader of this file alone cannot get it backwards):
  base = AXEYUM_EQ_ATOM_DAG_WALK unset  = the shipped tree walk
  arm  = AXEYUM_EQ_ATOM_DAG_WALK=1      = the DAG walk
  GAIN = base undecided, arm decided.  LOSS = the reverse.
  FLIP = sat<->unsat, which for a change claiming identical atom collection
         would be a SOUNDNESS finding, not a performance one.

Exit status depends on the finding: any FLIP, or any row whose exit status
changes, is a non-zero exit.
"""

import csv
import statistics
import sys
from pathlib import Path

W = Path(__file__).resolve().parent


def load(p):
    f = W / "ref" / p
    if not f.is_file():
        sys.exit(f"ABORT: {f} missing")
    return list(csv.DictReader(f.open(), delimiter="\t"))


def decided(v):
    return v in ("sat", "unsat")


def report(name, rows):
    print(f"=== {name}: {len(rows)} runs over {len({r['file'] for r in rows})} files ===")
    gains, losses, flips, rc_moves = [], [], [], []
    for r in rows:
        b, a = r["base"], r["arm"]
        if decided(b) and decided(a) and b != a:
            flips.append((r["file"], b, a))
        elif not decided(b) and decided(a):
            gains.append((r["file"], b, a))
        elif decided(b) and not decided(a):
            losses.append((r["file"], b, a))
        if r["base_rc"] != r["arm_rc"]:
            rc_moves.append((r["file"], r["base_rc"], r["arm_rc"]))
    print(f"  gains            : {len(gains)}")
    print(f"  losses           : {len(losses)}")
    print(f"  FLIPS (sat<->unsat): {len(flips)}")
    print(f"  exit-status moves: {len(rc_moves)}   (R7: carried separately from verdicts)")
    for lbl, xs in (("GAIN", gains), ("LOSS", losses), ("FLIP", flips), ("RC", rc_moves)):
        for x in xs:
            print(f"    {lbl}: {x}")

    # Timing, as the ONLY available read on whether the changed code runs here
    # at all (the breadcrumb probe cannot fire on a row that returns before the
    # watchdog -- see the ADR). A per-row median ratio far from 1.0 on some rows
    # and exactly 1.0 on all of them are different findings.
    ratios = []
    for r in rows:
        try:
            b, a = int(r["base_ms"]), int(r["arm_ms"])
        except (ValueError, KeyError):
            continue
        if b > 0:
            ratios.append(a / b)
    if ratios:
        ratios.sort()
        print(f"  arm/base wall ratio: median={statistics.median(ratios):.3f} "
              f"min={ratios[0]:.3f} max={ratios[-1]:.3f} n={len(ratios)}")
        big = sum(1 for x in ratios if x < 0.8)
        print(f"  runs where the arm was >20 % faster: {big}")
    print()
    return flips, rc_moves


bad = []
for name, path in (("TREATMENT (the 9)", "ab-treatment-9.tsv"),
                   ("CONTROL (53 decided UFNIA)", "ab-control-53.tsv")):
    f, rc = report(name, load(path))
    bad += f + rc

# Per-row stability across passes on the treatment: a row must give the same
# verdict on every pass of an arm, or it is UNSTABLE and no gain may be claimed.
tre = load("ab-treatment-9.tsv")
by_file = {}
for r in tre:
    by_file.setdefault(r["file"], []).append((r["base"], r["arm"]))
unstable = [f for f, vs in by_file.items() if len({v[0] for v in vs}) > 1 or len({v[1] for v in vs}) > 1]
print(f"treatment files with >1 pass : {sum(1 for v in by_file.values() if len(v) > 1)}")
print(f"UNSTABLE across passes       : {len(unstable)} {unstable}")

if bad:
    print("\nFINDING-CHECK FAILED: a verdict flip or an exit-status move occurred")
    sys.exit(1)
print("\nOK: no flip and no exit-status move in either arm.")
