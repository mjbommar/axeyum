#!/usr/bin/env python3
"""Why did the top decider not decide, on the rows `size.py` counted?

`size.py`'s ceiling counts an undecided row as a candidate when the class's
top decider was never reached or got less clock than its median winning time.
That test is necessary and it is NOT sufficient, and the difference is the
whole honesty of the number.

A route can fail to decide for two kinds of reason:

  * **the clock** -- it ran out of budget, so a reorder that hands it the
    seconds the routes above it were spending is exactly the fix;
  * **anything else** -- an oversized encoding, an out-of-fragment atom, a
    capacity ceiling.  More clock changes nothing on those rows, and counting
    them in a ceiling that is presented as "files a reorder could convert" is
    a claim the data does not make.

The first row of `bench-results/ledger/t1-QF_NIA-db31113fa.tsv` is the worked
example, and it is why this script exists: `int-blast-ladder` got 146 ms and
declined with `budget` / "estimated 130191180 CNF clauses before lowering
exceeds budget 64000000 (oversized encoding refused gracefully)".  That is a
CNF-SIZE refusal wearing the word `budget`.  Twelve seconds of freed clock
would buy that row nothing.

So this splits `size.py`'s candidates by the decider's own recorded decline
`reason` and typed `name` (ADR-2104/ADR-2105), and by whether the detail text
names a size ceiling rather than a clock.  The refined ceiling is the subset
whose refusal is plausibly clock-shaped.

Usage:
    python3 size-why.py [--ledger-dir DIR] [--repo PATH]
"""

from __future__ import annotations

import argparse
import statistics
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
from size import CLASSES, SWEEPS, deciding_ms, reached_ms  # noqa: E402

#: Substrings that identify a decline detail as a CAPACITY refusal rather than
#: a clock one.  Matched against the detail text the route itself wrote, which
#: is the only channel that distinguishes them -- `DeclineReason` renders both
#: as the single word `budget`, which is ADR-2060's defect in miniature and is
#: why this list is needed at all.
CAPACITY_MARKERS = (
    "exceeds budget",
    "oversized encoding",
    "past the consuming engine's capacity",
    "exceeds the joint resource boundary",
    "capacity of",
)

#: Substrings that identify a decline as a FRAGMENT refusal -- the route
#: cannot represent the query at all at its configured width.  Also not a
#: clock, and the reason word is `incomplete` rather than `budget`, so it is a
#: third bucket and not a variant of the second.
FRAGMENT_MARKERS = (
    "does not fit the bounded width",
    "widen the bound",
)


def decider_decline(row: "ol.LedgerRow", decider: str) -> tuple[str, str, str]:
    """`(reason, typed_name, detail)` for `decider`'s LAST decline on `row`.

    The last one, not the first: a route can appear twice in a trail and the
    occurrence that mattered is the one nearest the decision point.
    """
    found = ("", "", "")
    for (route, reason), name, detail in zip(row.reasons, row.names, row.details):
        if route == decider:
            found = (reason, name, detail)
    return found


def is_capacity(detail: str) -> bool:
    return any(marker in detail for marker in CAPACITY_MARKERS)


def is_fragment(detail: str) -> bool:
    return any(marker in detail for marker in FRAGMENT_MARKERS)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    ap.add_argument("--repo", default=str(REPO))
    args = ap.parse_args()

    rows, _flagged = ol.load(SWEEPS, ledger_dir=args.ledger_dir, repo=args.repo)

    refined_any = False
    for division, features, decider in CLASSES:
        group = [
            r for r in rows
            if division_of(r.corpus_path) == division and r.features == features
        ]
        decided = [r for r in group if r.decided_by != "none"]
        undecided = [r for r in group if r.decided_by == "none"]
        wins = [ms for r in decided if r.decided_by == decider
                for ms in (deciding_ms(r, decider),) if ms is not None]
        win_median = statistics.median(wins)

        candidates = []
        for r in undecided:
            got = reached_ms(r, decider)
            if got is None or got < win_median:
                candidates.append(r)

        print(f"=== {division} / {features} -- {decider} ===")
        print(f"  size.py candidates: {len(candidates)} of {len(undecided)} undecided")
        if not candidates:
            print("  (nothing to refine)\n")
            continue

        by_reason: Counter[tuple[str, str]] = Counter()
        capacity = []
        fragment = []
        clockish = []
        silent = []
        for r in candidates:
            reason, name, detail = decider_decline(r, decider)
            if not reason:
                silent.append(r)
                by_reason[("<no recorded decline>", "")] += 1
                continue
            by_reason[(reason, name)] += 1
            if is_capacity(detail):
                capacity.append((r, detail))
            elif is_fragment(detail):
                fragment.append((r, detail))
            else:
                clockish.append((r, reason, name, detail))

        print("  the decider's own recorded decline, on those rows:")
        for (reason, name), n in sorted(by_reason.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"    {n:>4}  reason={reason or '-'}  name={name or '-'}")

        print(f"  CAPACITY refusals (a size ceiling, not a clock): {len(capacity)}")
        print(f"  FRAGMENT refusals (a width ceiling, not a clock): {len(fragment)}")
        print(f"  not-capacity, not-fragment / clock-shaped:       {len(clockish)}")
        print(f"  no recorded decline by the decider at all:       {len(silent)}")
        never_and_silent = [r for r in silent if reached_ms(r, decider) is None]
        print(f"    ... of which the decider was NEVER reached:    {len(never_and_silent)}")
        refined = len(clockish) + len(silent)
        print(f"  REFINED CEILING IN FILES = {refined} of {len(undecided)} undecided")
        if refined >= 5:
            refined_any = True

        if capacity:
            sample = capacity[0][1]
            print(f"  one capacity detail, verbatim: {sample[:160]}")
        for r, detail in fragment[:10]:
            print(f"    FRAGMENT {r.corpus_path}")
            print(f"             detail={detail[:120]}")
        for r, reason, name, detail in clockish[:10]:
            print(f"    CLOCKISH {r.corpus_path}")
            print(f"             reason={reason} name={name} detail={detail[:120]}")
        for r in silent[:10]:
            got = reached_ms(r, decider)
            where = "NEVER REACHED" if got is None else f"reached, {got} ms"
            print(f"    SILENT   {r.corpus_path}  ({where})")
        print()

    return 0 if refined_any else 3


if __name__ == "__main__":
    raise SystemExit(main())
