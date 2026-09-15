#!/usr/bin/env python3
"""ADR-2103: are the 53 "a rung stopped the ladder" rows really that?

`size-q-ceiling.py` classifies a row as a candidate when a rung below the
terminal one did not run and neither `q:timeout` nor a partial trail explains
it. All 53 it returns have `terminal=q:uf-fmf-full`, `skipped=[q:nat-induction]`
-- one shape, which is itself a reason to distrust the classification.

`finish_quantified_solve_or_induct` is why:

    let Some(induction_config) = config_with_remaining_timeout(config, deadline)
    else { return Ok(result); };            // <-- records NOTHING

`config_with_remaining_timeout` returns `None` only when the deadline has
already passed. So this exit IS the clock -- it is the one budget exit in the
quantified ladder that does not go through `quantified_timeout`, and therefore
the one the `q:timeout` sink cannot see. A classifier keyed on the sink reads it
as "a rung stopped the ladder", which is the opposite of what happened.

This script settles it from the WALL CLOCK, which is a channel the missing
record cannot corrupt: if these rows sit at the 24 s budget, the deadline had
passed and the clock ended them.

Usage: check-candidates.py <trace.tsv> <sizing.txt>
"""

import re
import statistics
import sys


def main():
    trace_tsv, sizing_txt = sys.argv[1:3]
    wanted = set()
    for line in open(sizing_txt):
        stripped = line.strip()
        if stripped.endswith(".smt2") and "/" in stripped and " " not in stripped:
            wanted.add(stripped)
    if not wanted:
        sys.exit("ABORT: parsed no candidate paths out of the sizing output")

    rows = []
    for line in open(trace_tsv):
        cells = line.rstrip("\n").split("\t")
        if len(cells) < 6:
            continue
        path, verdict, rc, ms, route_line, _cell = cells[:6]
        if path not in wanted:
            continue
        total = re.search(r"total_ms=(\d+)", route_line)
        rows.append((path, verdict, int(rc), int(ms), int(total.group(1)) if total else None))

    print(f"candidate paths parsed : {len(wanted)}")
    print(f"matched in the capture : {len(rows)}")
    if len(rows) != len(wanted):
        sys.exit("ABORT: a candidate path is not in the capture it came from")

    harness_ms = [r[3] for r in rows]
    trail_ms = [r[4] for r in rows if r[4] is not None]
    print()
    print(f"harness wall ms  min={min(harness_ms)} median={statistics.median(harness_ms):.0f} "
          f"max={max(harness_ms)}")
    print(f"trail total_ms   min={min(trail_ms)} median={statistics.median(trail_ms):.0f} "
          f"max={max(trail_ms)}  (n={len(trail_ms)})")
    # The sweep ran at a 24 s budget. "At the budget" is the finding; anything
    # materially under it would be a row the clock did NOT end, and the only
    # kind this analysis must look at by hand.
    budget_ms = 24000
    under = [r for r in rows if r[4] is not None and r[4] < budget_ms * 0.9]
    print()
    print(f"rows whose trail total_ms is under 90% of the {budget_ms} ms budget: {len(under)}")
    for row in under:
        print(f"   {row}")
    print()
    if under:
        print("NOT all clock -- the rows above need a per-row ownership check.")
        sys.exit(1)
    print("EVERY candidate row is at the budget. The clock ended all of them, through")
    print("the one budget exit that records nothing. The ceiling is 0, and the finding")
    print("is the missing record rather than a reachable row.")


if __name__ == "__main__":
    main()
