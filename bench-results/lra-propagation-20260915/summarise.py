#!/usr/bin/env python3
"""Summarise the ADR-2122 sizing sweep: the ceiling, per row and over the set.

The ceiling this reports is `decisions_on_implied_atoms / decisions_on_tracked_atoms`
-- decisions the search spent on an atom the column bounds already entailed,
over decisions it spent on an atom the theory tracks at all. BOTH denominators
are printed, because the share of ALL decisions is a different and smaller
number (a `QF_LRA` skeleton has Tseitin variables the theory knows nothing
about, and a decision on one of those is not a decision propagation could have
removed).

A row that printed no `; theory-layer` line contributes an EMPTY cell, not a
zero, and is counted separately. Reporting it as zero would put rows that never
reached the engine into the numerator's denominator.
"""

from __future__ import annotations

import statistics
import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        sys.stderr.write(__doc__ or "")
        return 2
    rows: list[dict[str, str]] = []
    head: list[str] = []
    for path in argv[1:]:
        lines = Path(path).read_text().splitlines()
        if not lines:
            continue
        head = lines[0].split("\t")
        for ln in lines[1:]:
            if ln.strip():
                rows.append(dict(zip(head, ln.split("\t"), strict=False)))

    def numeric(v: str | None) -> bool:
        return bool(v) and v not in ("n/a", "none")

    silent = [r for r in rows if not r.get("dec_tracked")]
    # `n/a` is NOT zero and NOT silence: it is `TheoryEngineCounters == None`,
    # i.e. this theory kept no warm simplex at all and fell back to
    # Fourier-Motzkin. The ADR-2122 counters ride on that same Option, so such a
    # row reports nothing about propagation even though its search ran. Counted
    # separately rather than folded into either side.
    na = [r for r in rows if r.get("dec_tracked") == "n/a"]
    live = [r for r in rows if numeric(r.get("dec_tracked"))]
    print(
        f"rows: {len(rows)}   counters present: {len(live)}   "
        f"no warm engine (n/a): {len(na)}   no theory-layer line: {len(silent)}"
    )
    if not live:
        print("NOTHING TO SUMMARISE: no row reported the counters")
        return 1

    def col(name: str) -> list[int]:
        return [int(r[name]) for r in live if numeric(r.get(name))]

    tracked = col("dec_tracked")
    implied = col("dec_implied")
    total = col("decisions")
    props = col("theory_props")

    print()
    print(f"{'file':78s} {'decisions':>11s} {'tracked':>10s} {'implied':>10s} {'share':>7s} {'th.props':>9s}")
    for r in sorted(live, key=lambda r: -int(r["dec_tracked"])):
        t = int(r["dec_tracked"])
        i = int(r["dec_implied"])
        share = f"{100.0 * i / t:.1f}%" if t else "n/a"
        print(
            f"{r['file'][-78:]:78s} {int(r['decisions']):11d} {t:10d} {i:10d} {share:>7s} "
            f"{int(r['theory_props']):9d}"
        )

    print()
    print(f"SUM  decisions={sum(total)}  tracked={sum(tracked)}  implied={sum(implied)}")
    print(f"POOLED share of TRACKED decisions already implied: {100.0 * sum(implied) / sum(tracked):.1f}%")
    print(f"POOLED share of ALL decisions already implied:     {100.0 * sum(implied) / sum(total):.1f}%")
    shares = [
        100.0 * int(r["dec_implied"]) / int(r["dec_tracked"])
        for r in live
        if int(r["dec_tracked"])
    ]
    print(f"MEDIAN per-row share of tracked: {statistics.median(shares):.1f}%   min {min(shares):.1f}%   max {max(shares):.1f}%")
    print(f"MEDIAN theory_propagations on these rows (today): {statistics.median(props)}")
    print()
    print("cost, clock-free:")
    for name in ("passes", "row_cells", "derived"):
        vals = col(name)
        if vals:
            print(f"  {name:12s} median {statistics.median(vals):>12.0f}  sum {sum(vals):>14d}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
