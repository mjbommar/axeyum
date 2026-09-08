#!/usr/bin/env python3
"""Where do the offline decider's entries actually come from?

The post-merge sweep shows `offline_calls` flat between the cold and warm arms,
which reads as "warming bought nothing". Before reporting that, check the
denominator: `offline_calls` counts every entry to `lia_simplex_capped` — the
front door, `dpll_lia`'s inner oracle, and `LiaTheory`'s feasibility path — while
the warm decider serves only the last of those. A ratio over a denominator the
change cannot touch is not a measurement of the change.
"""
import argparse
import collections
import json
import os


def g(row, k):
    try:
        return int(row["counters"].get(k))
    except (TypeError, ValueError):
        return 0


ap = argparse.ArgumentParser()
ap.add_argument("--rows", required=True)
args = ap.parse_args()
rows = json.load(open(args.rows))

by_file = collections.defaultdict(dict)
for r in rows:
    by_file[r["file"]][r["arm"]] = r

print(
    f"{'file':40s} {'off.offline':>12s} {'warm.offline':>12s} {'warm.checks':>12s} "
    f"{'warm share':>11s} {'off.feas':>9s} {'warm.feas':>9s}"
)
print("-" * 112)

tot_off = tot_warm = tot_checks = 0
covered_files = 0
for path, per in sorted(by_file.items()):
    if "off" not in per or "warm" not in per:
        continue
    off = g(per["off"], "offline_calls")
    warm = g(per["warm"], "offline_calls")
    checks = g(per["warm"], "warm_checks")
    if off == 0 and warm == 0:
        continue
    share = checks / warm if warm else 0.0
    if share > 0.5:
        covered_files += 1
    tot_off += off
    tot_warm += warm
    tot_checks += checks
    print(
        f"{os.path.basename(path)[:40]:40s} {off:12d} {warm:12d} {checks:12d} "
        f"{share:10.1%} {g(per['off'], 'feasibility_checks'):9d} "
        f"{g(per['warm'], 'feasibility_checks'):9d}"
    )

print()
print(f"offline calls, cold arm : {tot_off}")
print(f"offline calls, warm arm : {tot_warm}")
print(f"of which WARM           : {tot_checks} ({tot_checks / max(tot_warm, 1):.1%})")
print(
    f"files where the warm decider serves >50% of offline entries: {covered_files}"
)
print()
print(
    "The warm decider is wired to `LiaTheory::feasibility` and its core\n"
    "minimisation. Everything else that enters `lia_simplex_capped` — the front\n"
    "door's own `lia-simplex` route and `dpll_lia`'s inner oracle — is untouched\n"
    "by it, and a flat `offline_calls` total says nothing about warming unless\n"
    "the warm share is large."
)
