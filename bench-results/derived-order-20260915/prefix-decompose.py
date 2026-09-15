#!/usr/bin/env python3
"""Where does a class's "prefix cost" actually go -- above the decider, or INSIDE it?

`bench-results/ledger-structure-20260915/README.md` ranked Phase 4's two
candidate classes by `prefix_cost_ms`, defined there as "the summed timed cost
of every attempt strictly BEFORE the top decider's own `decided` occurrence".

That definition is right for a route that appears ONCE on a trail.  It is
wrong for a route that records a **probe**, hands off to another ladder, and
records its decision only when the hand-off returns -- because then everything
the hand-off did lands between the probe and the decision and is counted as
"before the decider" when it IS the decider.

`q:skolem-qf` is exactly such a route (`auto.rs::solve_inner`: it records
`record_quant_rung_probe(SKOLEM_QF, ..)`, calls `check_auto` -- the whole
quantifier-free ladder -- and then records the result).  So this script splits
the README's number into the two halves that behave differently under a
reorder:

  * **before the decider's FIRST trail entry** -- the genuinely reorderable
    prefix.  A reorder that promotes the decider recovers this.
  * **between its first entry and its decision** -- the decider's own work.  A
    reorder recovers none of it, by definition.

Usage:
    python3 prefix-decompose.py [--ledger-dir DIR] [--repo PATH]
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
for extra in (str(REPO / "scripts"), str(HERE), str(REPO / "bench-results" / "ledger-structure-20260915")):
    if extra not in sys.path:
        sys.path.insert(0, extra)

import outcome_ledger as ol  # noqa: E402
from analyze import division_of  # noqa: E402
from size import CLASSES, SWEEPS, timed_attempts  # noqa: E402

#: The reorderable window per class -- the routes that sit inside ONE
#: straight-line body in `auto.rs` and can therefore actually trade places.
#: Anything in the prefix that is NOT in the window is above the window and a
#: reorder inside it cannot touch that money either.
WINDOW = {
    "QF_NIA": {
        "nia-square",
        "int-real-relax",
        "nia-linearize",
        "nia-bounded-blast",
        "cas-ideal-refuter",
        "int-blast-ladder",
    },
    "UFNIA": {"q:ground-subset", "q:bool-skeleton", "q:skolem-qf"},
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    ap.add_argument("--repo", default=str(REPO))
    args = ap.parse_args()

    rows, _flagged = ol.load(SWEEPS, ledger_dir=args.ledger_dir, repo=args.repo)
    reorderable_any = False

    for division, features, decider in CLASSES:
        group = [
            r for r in rows
            if division_of(r.corpus_path) == division and r.features == features
        ]
        decided = [r for r in group if r.decided_by == decider]
        print(f"=== {division} / {features} -- {decider}, {len(decided)} rows it decided ===")
        if not decided:
            print("  (none)\n")
            continue

        multi = sum(
            1 for r in decided
            if sum(1 for rt, _o, _m in timed_attempts(r) if rt == decider) > 1
        )
        print(f"  rows where {decider} appears MORE THAN ONCE on the trail: {multi}")

        before = Counter()
        inside = Counter()
        for r in decided:
            ta = timed_attempts(r)
            first = next(i for i, (rt, _o, _m) in enumerate(ta) if rt == decider)
            last_dec = max(
                (i for i, (rt, o, _m) in enumerate(ta) if rt == decider and o == "decided"),
                default=first,
            )
            for rt, _o, ms in ta[:first]:
                before[rt] += ms or 0
            for rt, _o, ms in ta[first + 1 : last_dec]:
                inside[rt] += ms or 0

        tot_before = sum(before.values())
        tot_inside = sum(inside.values())
        n = len(decided)
        print(
            f"  BEFORE its first trail entry (reorderable): "
            f"{tot_before} ms ({tot_before / n:.1f} ms/file)"
        )
        print(
            f"  BETWEEN its first entry and its decision (its OWN work): "
            f"{tot_inside} ms ({tot_inside / n:.1f} ms/file)"
        )
        print(
            f"  the ledger-structure README's prefix_cost_ms = the SUM: "
            f"{tot_before + tot_inside} ms"
        )

        win = WINDOW[division]
        in_window = sum(v for k, v in before.items() if k in win)
        print(
            f"  of the reorderable half, inside the window: "
            f"{in_window} ms ({in_window / n:.1f} ms/file)"
        )
        if in_window > 0:
            reorderable_any = True

        print("  top routes BEFORE its first entry:")
        for rt, ms in before.most_common(6):
            mark = " [in window]" if rt in win else ""
            print(f"    {rt:<30} {ms:>8} ms{mark}")
        if tot_inside:
            print("  top routes INSIDE its own hand-off:")
            for rt, ms in inside.most_common(6):
                print(f"    {rt:<30} {ms:>8} ms")
        print()

    # Exit status depends on the finding: non-zero when NO class has any
    # reorderable clock inside its window at all.
    return 0 if reorderable_any else 3


if __name__ == "__main__":
    raise SystemExit(main())
