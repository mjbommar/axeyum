#!/usr/bin/env python3
"""What does each rung cost on the rows it does NOT decide?

Phase 4's ordering key is "(decision rate, then median elapsed)".  It does not
say WHOSE elapsed, and the two readings give different orders:

  * the clock a rung needs when it WINS -- what `derive.py` uses, and the right
    number for "how long until the answer";
  * the clock it spends when it LOSES -- the money the rungs below it do not
    get, and the number that decides whether promoting it to the ladder's HEAD
    is safe.

A rung with a high decision rate and a cheap win can still be a bad head if its
losses are expensive, because at the head its losses are paid out of every
other rung's budget.  `int_tail_order::DERIVED` promoted `int-blast-ladder`
from the ladder's tail to its head on a 339 ms median WINNING clock, and five
`hypothesis_min` capability tests went red at a 2 s budget -- the minimiser's
small nonlinear-integer subsets stopped being refuted because the rungs that
refute them (`nia-linearize`, `int-real-relax`) no longer had the clock.

This script prints both numbers so that failure is a measurement and not a
surprise.

Usage:
    python3 cost-when-declining.py [--ledger-dir DIR] [--repo PATH]
"""

from __future__ import annotations

import argparse
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
for extra in (str(REPO / "scripts"), str(HERE), str(REPO / "bench-results" / "ledger-structure-20260915")):
    if extra not in sys.path:
        sys.path.insert(0, extra)

import outcome_ledger as ol  # noqa: E402
from analyze import division_of  # noqa: E402
from derive import WINDOWS  # noqa: E402
from size import SWEEPS, timed_attempts  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    ap.add_argument("--repo", default=str(REPO))
    args = ap.parse_args()

    rows, _flagged = ol.load(SWEEPS, ledger_dir=args.ledger_dir, repo=args.repo)
    head_is_cheap_when_losing = True

    for window in WINDOWS:
        hand = list(window["hand"])
        if not hand:
            continue
        group = [
            r for r in rows
            if division_of(r.corpus_path) == window["division"]
            and r.features == window["features"]
        ]
        print(f"=== {window['name']} -- {window['division']} / {window['features']} ===")
        print(
            f"  {'rung':<20} {'wins':>5} {'losses':>7} "
            f"{'win med':>9} {'LOSS med':>9} {'LOSS p90':>9} {'LOSS max':>9} {'LOSS total':>11}"
        )
        for route in hand:
            wins, losses = [], []
            for row in group:
                got, decided = 0, False
                seen = False
                for rt, outcome, ms in timed_attempts(row):
                    if rt != route:
                        continue
                    seen = True
                    got += ms or 0
                    if outcome == "decided":
                        decided = True
                if not seen:
                    continue
                (wins if decided else losses).append(got)
            win_med = statistics.median(wins) if wins else 0
            loss_med = statistics.median(losses) if losses else 0
            loss_p90 = (
                statistics.quantiles(losses, n=10)[8] if len(losses) >= 2 else (losses[0] if losses else 0)
            )
            loss_max = max(losses) if losses else 0
            print(
                f"  {route:<20} {len(wins):>5} {len(losses):>7} "
                f"{win_med:>9.0f} {loss_med:>9.0f} {loss_p90:>9.0f} "
                f"{loss_max:>9} {sum(losses):>11}"
            )

        # The head of the DERIVED order: is it cheap when it loses?
        stats_route = None
        # Re-derive the derived head the same way derive.py does, rather than
        # carrying a literal.
        from derive import derived_order, route_stats

        order = derived_order(route_stats(group, set(hand)))
        head = order[0]
        head_losses = []
        for row in group:
            got, decided, seen = 0, False, False
            for rt, outcome, ms in timed_attempts(row):
                if rt != head:
                    continue
                seen = True
                got += ms or 0
                if outcome == "decided":
                    decided = True
            if seen and not decided:
                head_losses.append(got)
        med = statistics.median(head_losses) if head_losses else 0
        total = sum(head_losses)
        print(f"  derived HEAD is {head}: loses {len(head_losses)} times, "
              f"median loss {med:.0f} ms, total {total} ms")
        # A head whose losing median is above a tenth of the 24,000 ms budget
        # is a head that starves the ladder below it on the rows it cannot
        # decide -- which is the whole population that still needs the ladder.
        if med > 2400:
            head_is_cheap_when_losing = False
            print("  -> EXPENSIVE WHEN LOSING. Promoting it to the head starves "
                  "every rung below it on exactly the rows that still need one.")
        else:
            print("  -> cheap when losing.")
        print()

    # Exit status depends on the finding.
    return 0 if head_is_cheap_when_losing else 3


if __name__ == "__main__":
    raise SystemExit(main())
