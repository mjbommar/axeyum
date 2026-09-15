#!/usr/bin/env python3
"""SILENT-HANG -- split the bucket by MECHANISM, never by label.

`bound_by=NONE` was one label over several program points.  This reads the
committed phase census and reports, per row, the three facts the old census
could not see:

  in       the INNERMOST open frame at the instant the watchdog read the
           breadcrumb -- the code that was running
  deepest  the deepest chain the run ever reached -- "we got at least this
           far", which is a different fact from "we are here now" and is the
           only one available when `in` is none
  enters   per-label entry counts.  A count of 5 and a count of 163,583 on the
           SAME label are not the same phenomenon, and nothing short of this
           counter distinguishes them.

Exit status depends on the finding (the ledger rule): a bucket that does not
split, or a row whose phase line is missing, is a non-zero exit.
"""

import csv
import re
import sys
from pathlib import Path

W = Path(__file__).resolve().parent
src = W / "ref" / "phase-24s.tsv"
if not src.is_file():
    sys.exit(f"ABORT: {src} missing")

rows = list(csv.DictReader(src.open(), delimiter="\t"))
if not rows:
    sys.exit("ABORT: census is empty")


def field(line, key):
    m = re.search(rf"\b{key}=(\S+)", line or "")
    return m.group(1) if m else None


out = []
for r in rows:
    pl = r["phase_line"]
    enters = {}
    if pl and pl != "NO-PHASE-LINE":
        m = re.search(r"\benters=(\S+)", pl)
        if m:
            for part in m.group(1).split(","):
                if ":" in part:
                    lbl, _, n = part.rpartition(":")
                    if n.isdigit():
                        enters[lbl] = int(n)
    out.append(
        {
            "file": r["file"],
            "short": r["file"].split("/")[-1][:46],
            "verdict": r["verdict"],
            "rc": r["rc"],
            "route_line": r["route_line"],
            "bound_by": r["bound_by"],
            "in": r["phase_in"],
            "in_ms": r["phase_in_ms"],
            "depth": r["depth"],
            "rss_mb": (int(r["peak_rss_kb"]) // 1024) if r["peak_rss_kb"].isdigit() else None,
            "deepest": field(pl, "deepest"),
            "enters": enters,
        }
    )

still = [r for r in out if r["route_line"] != "attributed"]
gone = [r for r in out if r["route_line"] == "attributed"]

print(f"population inherited from the census : {len(out)}")
print(f"  re-derived OUT (a `; route ' line)  : {len(gone)}")
print(f"  still watchdog-killed               : {len(still)}")
print()

print("=== re-derived OUT (R1) -- these now bind to a route and are NOT this bucket ===")
for r in gone:
    print(f"  {r['short']:48s} bound_by={r['bound_by']}")
print()

print("=== still watchdog-killed: the INNERMOST running phase ===")
for r in sorted(still, key=lambda x: (x["in"], x["short"])):
    hot = sorted(r["enters"].items(), key=lambda kv: -kv[1])[:3]
    hot_s = " ".join(f"{k}:{v}" for k, v in hot)
    print(f"  {r['short']:48s} in={r['in']:<30s} in_ms={r['in_ms']:>6s} d={r['depth']:>2s} rss={r['rss_mb']}MB")
    print(f"      hottest enters: {hot_s}")
print()

by_in = {}
for r in still:
    by_in.setdefault(r["in"], []).append(r["short"])
print("=== the split, by mechanism ===")
for k, v in sorted(by_in.items(), key=lambda kv: -len(kv[1])):
    print(f"  {len(v):>2d}  in={k}")
print()

deepest = {r["deepest"] for r in still if r["deepest"]}
print(f"=== distinct `deepest' chains among the {len(still)} ===")
for d in sorted(deepest):
    n = sum(1 for r in still if r["deepest"] == d)
    print(f"  n={n}  {d}")
print()

# The re-entry regime: `dpll-lia:abstract` is entered by every one of them, and
# the COUNT is what separates a tight refinement loop from a single long call.
print("=== dpll-lia:abstract entry count -- the same label, two regimes ===")
for r in sorted(still, key=lambda x: -x["enters"].get("dpll-lia:abstract", 0)):
    print(f"  {r['enters'].get('dpll-lia:abstract', 0):>8d}  {r['short']}")
print()

peak = max((r["rss_mb"] or 0) for r in out)
print(f"peak RSS over the whole population: {peak} MB")
print(f"exit statuses: {sorted({r['rc'] for r in out})}  (R7: a killed process is not an `unknown')")

problems = []
if len(by_in) < 2:
    problems.append("the bucket did NOT split -- one mechanism for every row")
missing = [r["short"] for r in still if r["in"] == "NO-PHASE-LINE"]
if missing:
    problems.append(f"no phase line on watchdog-killed rows: {missing}")
if problems:
    print()
    for p in problems:
        print(f"FINDING-CHECK FAILED: {p}")
    sys.exit(1)
print("\nOK: the bucket splits, and every watchdog-killed row carries a phase reading.")
