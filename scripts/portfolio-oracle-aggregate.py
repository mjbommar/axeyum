#!/usr/bin/env python3
"""Aggregate `portfolio-oracle.py` TSVs into the per-division decision table.

The table this prints is the whole business case for a parallel portfolio: per
division, how many files the ladder loses that some route we already own would
have decided inside the competition budget, and which route.

It refuses to report a prize count without also reporting the denominator it
came from, including the rows it could not attribute (`DECIDED-NO-TRAIL`,
`NO-ROUTE-NO-TRAIL`) and the rows the population had already gone stale on
(`STALE-DECIDED`).  A coverage number that quietly drops what it never saw is
how a stable number becomes a wrong one.
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import sys

ORDER = [
    "PRIZE",
    "PRIZE-UNCONFIRMED",
    "PRIZE-UNSTABLE",
    "TOO-SLOW-ARM",
    "NO-ROUTE",
    "NO-ROUTE-NO-TRAIL",
    "ABORTED",
    "DECIDED-NO-TRAIL",
    "DECIDED-NO-WINNER",
    "STALE-DECIDED",
    "MISSING",
]


def read(path: pathlib.Path):
    """Read one oracle TSV, repairing the pre-`ABORTED` label in place.

    A run that printed no verdict line at all did not "find no route": it
    aborted, and the TSV records that faithfully as `control_verdict=none` /
    `probe_verdict=none` even though sweeps produced before the `ABORTED` status
    existed filed it under `NO-ROUTE-NO-TRAIL`.  The repair is derived from the
    recorded field rather than from the status string, so it is a measurement,
    not a patch of a label by another label.
    """
    rows = []
    with path.open() as fh:
        header = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            if line.startswith("#"):
                continue
            vals = line.rstrip("\n").split("\t")
            row = dict(zip(header, vals))
            if row.get("control_verdict") == "none" or row.get("probe_verdict") == "none":
                row["status"] = "ABORTED"
            rows.append(row)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tsv", nargs="+")
    args = ap.parse_args()

    by_div = collections.defaultdict(list)
    for p in args.tsv:
        for r in read(pathlib.Path(p)):
            by_div[r.get("division", "?")].append(r)

    print(f"{'division':<10} {'files':>5} {'stale':>6} {'PRIZE':>6} {'unconf':>7} "
          f"{'slow-arm':>9} {'no-route':>9} {'abort':>6} {'blind':>6}")
    totals = collections.Counter()
    for div in sorted(by_div):
        rows = by_div[div]
        c = collections.Counter(r.get("status", "?") for r in rows)
        blind = c["NO-ROUTE-NO-TRAIL"] + c["DECIDED-NO-TRAIL"] + c["DECIDED-NO-WINNER"]
        c["PRIZE-UNCONFIRMED"] += c["PRIZE-UNSTABLE"]
        print(f"{div:<10} {len(rows):>5} {c['STALE-DECIDED']:>6} {c['PRIZE']:>6} "
              f"{c['PRIZE-UNCONFIRMED']:>7} {c['TOO-SLOW-ARM']:>9} {c['NO-ROUTE']:>9} "
              f"{c['ABORTED']:>6} {blind:>6}")
        totals.update(c)
        totals["files"] += len(rows)
    blind = (totals["NO-ROUTE-NO-TRAIL"] + totals["DECIDED-NO-TRAIL"]
             + totals["DECIDED-NO-WINNER"])
    print(f"{'TOTAL':<10} {totals['files']:>5} {totals['STALE-DECIDED']:>6} "
          f"{totals['PRIZE']:>6} {totals['PRIZE-UNCONFIRMED']:>7} "
          f"{totals['TOO-SLOW-ARM']:>9} {totals['NO-ROUTE']:>9} "
          f"{totals['ABORTED']:>6} {blind:>6}")

    print("\nprizes, by winning route:")
    winners = collections.Counter(
        r["winner"] for rows in by_div.values() for r in rows
        if r.get("status") == "PRIZE" and r.get("winner")
    )
    if not winners:
        print("  (none)")
    for route, n in winners.most_common():
        print(f"  {route:<40} {n}")

    print("\nevery prize, with the arm time a portfolio would have paid:")
    any_prize = False
    for div in sorted(by_div):
        for r in by_div[div]:
            if r.get("status") != "PRIZE":
                continue
            any_prize = True
            print(f"  {div:<9} {r['winner']:<26} arm={r.get('arm_ms'):>9} ms "
                  f"(preamble {r.get('preamble_ms')} + own {r.get('winner_own_ms')}; "
                  f"confirm {r.get('confirm_own_ms')})  "
                  f"{r['file'].split('non-incremental/')[-1]}")
    if not any_prize:
        print("  (none)")

    print("\nfiles a route decides but too slowly to be a portfolio arm:")
    slow = [r for rows in by_div.values() for r in rows
            if r.get("status") == "TOO-SLOW-ARM"]
    if not slow:
        print("  (none)")
    for r in sorted(slow, key=lambda r: float(r.get("arm_ms") or 0))[:20]:
        print(f"  {r['division']:<9} {r.get('winner',''):<26} arm={r.get('arm_ms'):>9} ms  "
              f"{r['file'].split('non-incremental/')[-1]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
