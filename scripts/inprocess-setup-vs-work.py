#!/usr/bin/env python3
"""How much of each pass's cost is paid whether or not it finds anything.

Usage:
    python3 scripts/inprocess-setup-vs-work.py <pass-wall.jsonl>

`inprocess_pass_cost` runs every pass TWICE — the second time on its own output,
where it rebuilds the same occurrence lists and (nearly) nothing is left to
find. So `setup_seconds` is the floor the pass pays for existing, and
`pass_seconds - setup_seconds` is the part that depends on there being work.

The distinction decides what to fix. A pass that is nearly all setup gets cheaper
from a schedule that reduces repeatedly and reuses its indices, and not at all
from a faster inner loop. A pass that is nearly all work is the opposite.

The second run's own reduction counters are printed, because "the second run
found nothing" is an assumption this script must not make on the reader's
behalf: on a pass that has not reached a fixpoint the re-run does real work, and
then `setup_seconds` overstates the floor and the split is not what it claims.
"""

import json
import statistics
import sys

path = sys.argv[1] if len(sys.argv) > 1 else (
    "bench-results/inprocess-cost-2026-09-08/pass-wall-24s.jsonl"
)
rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
rows = [r for r in rows if "pass_seconds" in r]
if not rows:
    print("FAIL: no rows with timings — this measured nothing", file=sys.stderr)
    raise SystemExit(1)

print(f"{len(rows)} rows with timings\n")
print("| arm | file | pass s | setup s | setup share | re-run found | vars | cl ratio | lit ratio |")
print("|---|---|---:|---:|---:|---|---:|---:|---:|")
shares = {}
for r in sorted(rows, key=lambda r: (r["arm"], r["file"])):
    if r["arm"] == "off":
        continue
    share = r["setup_seconds"] / max(r["pass_seconds"], 1e-9)
    shares.setdefault(r["arm"], []).append(share)
    found = (
        f"sub={r['rerun_clauses_subsumed']} bve={r['rerun_variables_eliminated']} "
        f"viv={r['rerun_vivify_strengthened']}"
    )
    print(
        f"| {r['arm']} | {r['file'].split('/')[-1][:34]} | {r['pass_seconds']:.3f} | "
        f"{r['setup_seconds']:.3f} | {share * 100:.0f}% | {found} | "
        f"{r['variables_live_before']}→{r['variables_live_after']} | "
        f"{r['clauses_after'] / max(r['clauses_before'], 1):.3f} | "
        f"{r['literals_after'] / max(r['literals_before'], 1):.3f} |"
    )

print("\n## median setup share, by pass")
for arm, s in sorted(shares.items()):
    print(f"  {arm:16s} n={len(s):2d}  median {statistics.median(s) * 100:.0f}%  "
          f"min {min(s) * 100:.0f}%  max {max(s) * 100:.0f}%")

print("\n## verdict at the 24 s wall budget, by arm")
by_arm = {}
for r in rows:
    by_arm.setdefault(r["arm"], []).append(r["verdict"])
for arm, v in sorted(by_arm.items()):
    decided = sum(1 for x in v if x in ("sat", "unsat"))
    print(f"  {arm:16s} decided {decided}/{len(v)}  ({', '.join(sorted(set(v)))})")
