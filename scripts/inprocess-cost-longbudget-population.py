#!/usr/bin/env python3
"""Select the only files whose verdict can differ at a LONGER budget.

Usage:
    python3 scripts/inprocess-cost-longbudget-population.py <out.txt> <arm.jsonl> [...]

A full 200-file sweep at 120 s costs about 6.5 h on this host, and almost all of
it re-decides files that decided in 90 ms. Only two kinds of file can answer
differently at a longer budget, and this selects exactly them:

1. **Undecided at the short budget.** More time can only help these.
2. **A pass was cut off by its deadline.** Inprocessing is granted HALF the
   remaining solve budget, so a longer budget is a longer slice, and a pass that
   was truncated at 24 s may run to completion — or may simply spend five times
   as long and still not finish, which is the more interesting outcome. These
   are the only files where a longer budget can make the `on` arm WORSE.

Every other file decided inside the short budget with every pass reaching its
own fixpoint (`*_deadline_expired == 0`), so granting it more time and a larger
slice changes nothing it does. That is an argument, not a measurement, and it
rests on the truncation counters being right — which is why this script prints
how many files it is asserting that about, rather than leaving the count
implicit.

The 120 s solved count is then: (files decided at the short budget and NOT in
this population) + (files this population decides at 120 s).
"""

import json
import sys


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    out_path = sys.argv[1]
    arms = {}
    for path in sys.argv[2:]:
        rows = [json.loads(line) for line in open(path, encoding="utf-8") if line.strip()]
        if not rows:
            print(f"FAIL: {path} has no rows", file=sys.stderr)
            return 1
        arms[rows[0]["arm"]] = {r["file"]: r for r in rows}

    populations = {frozenset(v) for v in arms.values()}
    if len(populations) != 1:
        print("FAIL: arms cover different files", file=sys.stderr)
        return 1
    files = sorted(next(iter(populations)))

    expiry_keys = (
        "bve_deadline_expired",
        "subsume_deadline_expired",
        "vivify_deadline_expired",
    )
    selected, undecided, truncated, carried = [], 0, 0, 0
    for f in files:
        rows = [arms[a][f] for a in arms]
        is_undecided = any(r["verdict"] not in ("sat", "unsat") for r in rows)
        is_truncated = any(
            r.get("counters", {}).get(k) == 1.0 for r in rows for k in expiry_keys
        )
        if is_undecided or is_truncated:
            selected.append(f)
            undecided += is_undecided
            truncated += is_truncated and not is_undecided
        else:
            carried += 1

    if not selected:
        print("FAIL: nothing can change at a longer budget — refusing to write an empty list",
              file=sys.stderr)
        return 1
    with open(out_path, "w", encoding="utf-8") as handle:
        handle.write("\n".join(selected) + "\n")
    print(f"selected {len(selected)} of {len(files)} files -> {out_path}")
    print(f"  undecided by some arm: {undecided}")
    print(f"  decided, but a pass was truncated: {truncated}")
    print(f"  carried forward unchanged (decided, no pass truncated): {carried}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
