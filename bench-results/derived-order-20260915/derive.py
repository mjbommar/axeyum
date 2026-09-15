#!/usr/bin/env python3
"""The DERIVED ladder order, computed from the outcome ledger alone.

Phase 4's shape (`docs/plan/dispatch-and-instrumentation-2026-09-15.md` §5):

    "Per feature class: order routes by (decision rate, then median elapsed)
    from the ledger."

This is that computation and nothing else.  It reads
`scripts/outcome_ledger.py`'s `load()`, is deterministic (run it twice and
`diff` the output -- the ordering key is a total order with the route NAME as
its final tiebreak, so no two routes can trade places between runs), and
prints the numbers beside every route so the order can be checked rather than
believed.

----------------------------------------------------------------------------
What a "route in the class's ladder" is, and why the window is bounded
----------------------------------------------------------------------------

A class's ladder is not the whole 32-rung trail.  It is the contiguous run of
rungs that (a) actually appear on that class's rows and (b) live inside ONE
reorderable body in `auto.rs` -- a straight-line sequence of `if let Some(..)
= route(..) { return }` steps with no branch between them.  Reordering across
a branch is not a reorder, it is a rewrite, and Phase 4 is explicitly not a
rewrite of `auto.rs`.

The two windows are named in `WINDOWS` below, each with the function that
holds it, so a reader can go check the source rather than trust this file.

----------------------------------------------------------------------------
The ordering key
----------------------------------------------------------------------------

Per route, over the class's rows:

    decisions      rows this route DECIDED (outcome `decided` on the trail)
    attempts       rows where it was attempted at all
    decision_rate  decisions / attempts        -- descending, the primary key
    median_ms      median clock of its DECIDING attempts, or of all its
                   attempts when it never decided  -- ascending, the secondary
    name           ascending -- the tiebreak that makes this a TOTAL order

A route that never decides sorts below every route that does, which is the
plan's key read literally (rate 0.0 is the smallest rate).  Among those, the
cheapest goes first: a route that cannot decide this class should at least
not be the one eating the clock.

----------------------------------------------------------------------------
Usage
----------------------------------------------------------------------------

    python3 derive.py [--ledger-dir DIR] [--repo PATH] [--tsv-out PATH]

The committed `--tsv-out` target is `docs/plan/fixtures/derived-ladder-order-20260915.tsv`,
and it is there rather than beside this script because
`scripts/tests/mutation_controls.py` excludes `bench-results` from the tree it
copies -- a Rust fixture included from this directory makes every mutation on
`auto.rs` report `BASELINE DID NOT BUILD` instead of a result.

Exit status depends on the finding: non-zero when the derived order for every
window is identical to the hand order already in the source, because a
"derived" order that changes nothing is a result to report, not a lever to
ship.
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
from size import SWEEPS, timed_attempts  # noqa: E402

#: The reorderable windows, one per feature class.
#:
#: `hand` is the order the source ships TODAY, read off the function named in
#: `body` top to bottom.  It is written here as a literal on purpose and
#: `check_hand_order_against_source` re-derives it from `auto.rs` so the
#: literal cannot drift silently.
WINDOWS: tuple[dict, ...] = (
    {
        "name": "qf_nia_int",
        "division": "QF_NIA",
        "features": "Int",
        "body": "auto.rs::dispatch_nonlinear_int_tail",
        "hand": (
            "nia-square",
            "int-real-relax",
            "nia-linearize",
            "nia-bounded-blast",
            "cas-ideal-refuter",
            "int-blast-ladder",
        ),
    },
    {
        "name": "ufnia_int_function",
        "division": "UFNIA",
        "features": "Int|Function",
        "body": "auto.rs::solve_inner (quantified ladder head)",
        # The three rungs that RECORD on this class's rows.  ADR-2103's
        # `SILENT_ON_DECLINE` names six rungs that record nothing when they
        # decline -- `q:checked-fast-path` is one, and it sits between
        # `q:bool-skeleton` and `q:skolem-qf` in the source.  Its absence from
        # the trail is therefore NOT evidence it was skipped, and it is left
        # out of the window rather than silently treated as costing nothing.
        "hand": (
            "q:ground-subset",
            "q:bool-skeleton",
            "q:skolem-qf",
        ),
    },
)


def route_stats(rows, window_routes: set[str]) -> dict[str, dict]:
    """`{route: {decisions, attempts, median_ms}}` over `rows`.

    An attempt is counted once per ROW even when the route appears twice in
    that row's trail (a probe and a real attempt): the question is "on how
    many files was this route tried", and double-counting a probe inflates the
    denominator of exactly the routes that have one.  Its clock is the SUM
    over occurrences on that row, for the same reason `size.py` sums it.
    """
    stats: dict[str, dict] = {
        r: {"decisions": 0, "attempts": 0, "decide_ms": [], "all_ms": []}
        for r in window_routes
    }
    for row in rows:
        seen: dict[str, dict] = {}
        for route, outcome, ms in timed_attempts(row):
            if route not in window_routes:
                continue
            entry = seen.setdefault(route, {"decided": False, "ms": 0})
            if outcome == "decided":
                entry["decided"] = True
            entry["ms"] += ms or 0
        for route, entry in seen.items():
            s = stats[route]
            s["attempts"] += 1
            s["all_ms"].append(entry["ms"])
            if entry["decided"]:
                s["decisions"] += 1
                s["decide_ms"].append(entry["ms"])
    for s in stats.values():
        pool = s["decide_ms"] or s["all_ms"]
        s["median_ms"] = statistics.median(pool) if pool else 0.0
        s["rate"] = (s["decisions"] / s["attempts"]) if s["attempts"] else 0.0
    return stats


def derived_order(stats: dict[str, dict]) -> list[str]:
    """(decision rate desc, median elapsed asc, name asc) -- a TOTAL order."""
    return sorted(
        stats,
        key=lambda r: (-stats[r]["rate"], stats[r]["median_ms"], r),
    )


def observed_routes(rows) -> list[str]:
    """Routes that appear on these rows, in first-appearance order.

    The empirical reading of the class's current ladder, used to FILL a
    window whose hand order this file does not carry a literal for, and to
    CHECK one it does.
    """
    order: list[str] = []
    seen = set()
    for row in rows:
        for route, _outcome, _ms in timed_attempts(row):
            if route not in seen:
                seen.add(route)
                order.append(route)
    return order


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    ap.add_argument("--repo", default=str(REPO))
    ap.add_argument("--tsv-out", default=None)
    ap.add_argument(
        "--print-observed",
        action="store_true",
        help="print every route observed on each class's rows, in first-appearance order",
    )
    args = ap.parse_args()

    rows, _flagged = ol.load(SWEEPS, ledger_dir=args.ledger_dir, repo=args.repo)

    tsv = ["\t".join(("window", "position", "route", "decisions", "attempts", "rate", "median_ms"))]
    any_change = False

    for window in WINDOWS:
        group = [
            r for r in rows
            if division_of(r.corpus_path) == window["division"]
            and r.features == window["features"]
        ]
        print(f"=== {window['name']} -- {window['division']} / {window['features']} ===")
        print(f"  body: {window['body']}")
        print(f"  rows: {len(group)}")

        if args.print_observed:
            print("  routes observed, first-appearance order:")
            for i, route in enumerate(observed_routes(group)):
                print(f"    {i:>3} {route}")

        hand = list(window["hand"])
        if not hand:
            print("  (no hand order literal for this window -- nothing to derive against)")
            print()
            continue

        stats = route_stats(group, set(hand))
        order = derived_order(stats)

        print("  hand order (source today) -> derived order (this ledger):")
        width = max(len(r) for r in hand)
        for i in range(len(hand)):
            h = hand[i]
            d = order[i]
            s = stats[d]
            moved = "  <-- moved" if h != d else ""
            print(
                f"    {i}. {h:<{width}}  ->  {d:<{width}}"
                f"  decides {s['decisions']:>3}/{s['attempts']:<4}"
                f" rate {s['rate']:.3f}  median {s['median_ms']:.0f} ms{moved}"
            )
            tsv.append(
                "\t".join(
                    (
                        window["name"],
                        str(i),
                        d,
                        str(s["decisions"]),
                        str(s["attempts"]),
                        f"{s['rate']:.6f}",
                        f"{s['median_ms']:.0f}",
                    )
                )
            )
        if order != hand:
            any_change = True
            print("  ORDER DIFFERS from the hand order.")
        else:
            print("  order is IDENTICAL to the hand order.")
        print()

    if args.tsv_out:
        Path(args.tsv_out).write_text("\n".join(tsv) + "\n", encoding="utf-8")
        print(f"wrote {args.tsv_out}")

    return 0 if any_change else 3


if __name__ == "__main__":
    raise SystemExit(main())
