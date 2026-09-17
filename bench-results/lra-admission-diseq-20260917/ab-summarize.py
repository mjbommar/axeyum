#!/usr/bin/env python3
"""Summarize `ab-arms.sh` TSVs (any number of shards) per ARM against `base`.

For every non-base arm: decided counts, gains (base undecided, arm decided),
losses (base decided, arm undecided), FLIPS (both decided, different verdict),
`:status` disagreements (a decided verdict against a file header that says the
opposite), rc-134 aborts per arm and NEW aborts (arm aborted, base did not),
and the wall-clock sum. Movers are written to `<out>-movers-<arm>.txt` for the
3x recheck.

Usage: ab-summarize.py <name> <tsv>... [--movers-dir DIR] [--base NAME]
"""
import argparse
import csv
import sys
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("name")
ap.add_argument("tsv", nargs="+")
ap.add_argument("--movers-dir", default=None)
ap.add_argument("--base", default="base")
a = ap.parse_args()

rows = []
for t in a.tsv:
    with open(t) as fh:
        rows.extend(csv.DictReader(fh, delimiter="\t"))
if not rows:
    sys.exit(f"{a.name}: no rows")
arms = [c for c in rows[0].keys() if c not in ("file", "first", "status") and not c.endswith("_ms") and not c.endswith("_rc")]
base = a.base
assert base in arms, f"base arm {base!r} not among {arms}"

def decided(v):
    return v in ("sat", "unsat")

print(f"== {a.name}: {len(rows)} rows, arms {arms}")
hdr = f"{'arm':<8} {'decided':>7} {'gain':>5} {'loss':>5} {'flip':>5} {'status!':>7} {'rc134':>6} {'newabort':>8} {'wall_s':>8}"
print(hdr)
for arm in arms:
    dec = sum(decided(r[arm]) for r in rows)
    aborts = sum(r[f"{arm}_rc"] == "134" for r in rows)
    wall = sum(int(r[f"{arm}_ms"]) for r in rows) / 1000
    status_bad = sum(decided(r[arm]) and r["status"] in ("sat", "unsat") and r[arm] != r["status"] for r in rows)
    if arm == base:
        print(f"{arm:<8} {dec:>7} {'-':>5} {'-':>5} {'-':>5} {status_bad:>7} {aborts:>6} {'-':>8} {wall:>8.0f}")
        continue
    gains = [r for r in rows if not decided(r[base]) and decided(r[arm])]
    losses = [r for r in rows if decided(r[base]) and not decided(r[arm])]
    flips = [r for r in rows if decided(r[base]) and decided(r[arm]) and r[base] != r[arm]]
    new_aborts = [r for r in rows if r[f"{arm}_rc"] == "134" and r[f"{base}_rc"] != "134"]
    print(f"{arm:<8} {dec:>7} {len(gains):>5} {len(losses):>5} {len(flips):>5} {status_bad:>7} {aborts:>6} {len(new_aborts):>8} {wall:>8.0f}")
    for r in gains:
        print(f"    GAIN  {arm}: {r[base]}->{r[arm]} ({r[f'{arm}_ms']} ms, status {r['status']}) {r['file']}")
    for r in losses:
        print(f"    LOSS  {arm}: {r[base]}->{r[arm]} (base {r[f'{base}_ms']} ms, status {r['status']}) {r['file']}")
    for r in flips:
        print(f"    FLIP  {arm}: {r[base]}->{r[arm]} (status {r['status']}) {r['file']}")
    for r in new_aborts:
        print(f"    ABORT {arm}: rc {r[f'{arm}_rc']} {r['file']}")
    if a.movers_dir:
        movers = sorted({r["file"] for r in gains + losses + flips})
        out = Path(a.movers_dir) / f"{a.name}-movers-{arm}.txt"
        out.write_text("".join(f"{m}\n" for m in movers))
        print(f"    movers -> {out} ({len(movers)})")
