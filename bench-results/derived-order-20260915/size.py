#!/usr/bin/env python3
"""Phase 4 SIZING: how many FILES could a derived ladder order convert?

The brief's rule, verbatim, and the reason this script exists before any Rust:

    "The ledger ceiling is in TIME on files that already decide. Phase 4 is
    only worth files if the freed clock decides files that are undecided
    today."

`bench-results/ledger-structure-20260915/README.md` sized Phase 4 in
MILLISECONDS -- 631,307 ms over 65 `QF_NIA/Int` files and 126,764 ms over 24
`UFNIA/Int|Function` files.  Every one of those 89 files ALREADY DECIDES.
Reordering the ladder makes them decide sooner; it cannot make them decide,
because they already do.  The gain, if there is one, is on the rows that do
NOT decide today and would decide if the deciding route got the clock the
routes above it are spending.

So the ceiling in FILES is, per class, the count of UNDECIDED rows where:

  * the class's top decider was **never reached** at all (every millisecond
    went to routes above it), or
  * it was reached but got **less than its typical winning time** -- the
    median clock it needed on the rows it actually decided.

Both halves are necessary and neither is sufficient.  A row where the decider
was reached and given MORE than its typical winning time and still did not
decide is a row a reorder cannot help: it already had the clock.  A row where
the decider was never reached is the clearest candidate.  A row where it was
reached with less than the median is the interesting middle, and it is a
CEILING rather than a prediction -- the median is a summary of the rows that
decided, and an undecided row may simply be harder than any of them.

Stated as a bound the other way: this number can only OVERSTATE the gain.
That is what a ceiling is for.

Everything here reads `scripts/outcome_ledger.py`'s `load()` only -- no
re-parse of a `--trace` capture, no second authority.  Trail entries are split
on the LAST colon (`bench-results/ledger-structure-20260915/analyze.py`'s own
`_route_outcome`, and the reason is in its docstring: route names carry
colons, outcome tokens do not), and the deciding attempt is located by its
`decided` OUTCOME rather than by the first occurrence of the name -- a route
can appear twice in one trail, once as a probe.

Usage:
    python3 size.py [--ledger-dir DIR] [--repo PATH] [--tsv-out PATH]
"""

from __future__ import annotations

import argparse
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
SCRIPTS = REPO / "scripts"
for extra in (str(SCRIPTS), str(REPO / "bench-results" / "ledger-structure-20260915")):
    if extra not in sys.path:
        sys.path.insert(0, extra)

import outcome_ledger as ol  # noqa: E402
from analyze import _route_outcome, division_of  # noqa: E402

#: The two classes the ledger-structure README ranked #1 and #2 and the brief
#: names.  `(division, features-column-value, top decider)` -- the decider is
#: NOT trusted from this constant; `main` asserts it back out of the rows.
CLASSES: tuple[tuple[str, str, str], ...] = (
    ("QF_NIA", "Int", "int-blast-ladder"),
    ("UFNIA", "Int|Function", "q:skolem-qf"),
)

SWEEPS = [
    "t1-QF_NIA-db31113fa",
    "t1-UFNIA-db31113fa",
]


def timed_attempts(row: "ol.LedgerRow") -> list[tuple[str, str, int | None]]:
    """`(route, outcome, ms_or_None)` per trail entry, positionally aligned.

    `attempt_trail` and `elapsed_ms_per_attempt` are written as one pair by
    the producer and are the same length on every row of this sweep; a row
    where they are not is REFUSED rather than zipped short, because a silent
    `zip` truncation is how an axis gets read off by one.
    """
    trail = row.trail
    times = row.per_attempt_ms
    if len(trail) != len(times):
        raise SystemExit(
            f"MISALIGNED trail/elapsed on {row.corpus_path}: "
            f"{len(trail)} attempts vs {len(times)} times"
        )
    out = []
    for entry, ms in zip(trail, times):
        route, outcome = _route_outcome(entry)
        out.append((route, outcome, ms))
    return out


def deciding_ms(row: "ol.LedgerRow", decider: str) -> int | None:
    """The clock the DECIDING occurrence of `decider` got on a decided row.

    Located by `outcome == "decided"`, never by the first occurrence of the
    name: `q:skolem-qf` appears as a `probe` early and again as the real
    decision later on real rows (`UFNIA/2019-Preiner/qf/f2_rw8.smt2`), and
    matching the first occurrence credits the decision to the probe.
    """
    for route, outcome, ms in timed_attempts(row):
        if route == decider and outcome == "decided":
            return ms
    return None


def reached_ms(row: "ol.LedgerRow", decider: str) -> int | None:
    """Total clock `decider` got on this row across EVERY occurrence.

    `None` means the route does not appear in the trail at all -- never
    reached.  `0` means it was reached and given nothing measurable, which is
    a different answer and the two must not be conflated: `None or 0` would
    fold "never ran" into "ran for under a millisecond" and the ceiling's two
    halves would stop being separable.
    """
    total: int | None = None
    for route, _outcome, ms in timed_attempts(row):
        if route == decider:
            total = (total or 0) + (ms or 0)
    return total


def clock_above(row: "ol.LedgerRow", decider: str) -> tuple[int, list[tuple[str, int]]]:
    """Clock spent strictly BEFORE the first occurrence of `decider`.

    On a row where the decider never appears, that is the whole trail -- which
    is the right answer: every millisecond went to a route above it.
    """
    above = 0
    spent: list[tuple[str, int]] = []
    for route, _outcome, ms in timed_attempts(row):
        if route == decider:
            break
        if ms:
            above += ms
            spent.append((route, ms))
    spent.sort(key=lambda kv: -kv[1])
    return above, spent


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger-dir", default=str(REPO / "bench-results" / "ledger"))
    ap.add_argument("--repo", default=str(REPO))
    ap.add_argument("--tsv-out", default=None)
    args = ap.parse_args()

    rows, flagged = ol.load(SWEEPS, ledger_dir=args.ledger_dir, repo=args.repo)
    print(f"loaded {len(rows)} rows from {len(SWEEPS)} sweeps; {len(flagged)} flagged stale")

    tsv: list[str] = [
        "\t".join(
            (
                "division",
                "features",
                "decider",
                "rows",
                "decided",
                "decided_by_decider",
                "undecided",
                "win_ms_median",
                "win_ms_p75",
                "never_reached",
                "reached_under_median",
                "reached_at_or_over_median",
                "ceiling_files",
                "ceiling_pct_of_undecided",
            )
        )
    ]

    any_class_worth_files = False
    for division, features, decider in CLASSES:
        group = [
            r
            for r in rows
            if division_of(r.corpus_path) == division and r.features == features
        ]
        decided = [r for r in group if r.decided_by != "none"]
        undecided = [r for r in group if r.decided_by == "none"]

        # ASSERT the README's decider back out of the rows rather than
        # trusting the constant.  A class whose top decider moved is a
        # different question and this script must not answer the old one.
        by_decider: dict[str, int] = {}
        for r in decided:
            by_decider[r.decided_by] = by_decider.get(r.decided_by, 0) + 1
        top = max(by_decider.items(), key=lambda kv: (kv[1], kv[0]))[0] if by_decider else "none"
        if top != decider:
            raise SystemExit(
                f"REFUSING: {division}/{features} top decider is {top!r}, "
                f"not the {decider!r} this script was written against"
            )

        wins = []
        for r in decided:
            if r.decided_by != decider:
                continue
            ms = deciding_ms(r, decider)
            if ms is not None:
                wins.append(ms)
        if not wins:
            raise SystemExit(f"REFUSING: no timed winning attempt for {decider} in {division}")
        win_median = statistics.median(wins)
        win_p75 = statistics.quantiles(wins, n=4)[2] if len(wins) >= 2 else float(wins[0])

        never = []
        under = []
        at_or_over = []
        for r in undecided:
            got = reached_ms(r, decider)
            if got is None:
                never.append(r)
            elif got < win_median:
                under.append(r)
            else:
                at_or_over.append(r)

        ceiling = len(never) + len(under)
        pct = (100.0 * ceiling / len(undecided)) if undecided else 0.0

        print()
        print(f"=== {division} / {features} -- top decider {decider} ===")
        print(f"  rows                            {len(group)}")
        print(f"  decided                         {len(decided)}")
        print(f"  decided BY {decider:<20} {by_decider.get(decider, 0)}")
        print(f"  undecided (THE DENOMINATOR)     {len(undecided)}")
        print(
            f"  {decider} winning clock: median {win_median:.0f} ms, "
            f"p75 {win_p75:.0f} ms, n={len(wins)}"
        )
        print(f"  undecided rows where it was NEVER reached          {len(never)}")
        print(f"  undecided rows where it got LESS than the median   {len(under)}")
        print(f"  undecided rows where it got the median or MORE     {len(at_or_over)}")
        print(f"  CEILING IN FILES = {ceiling} of {len(undecided)} undecided ({pct:.1f}%)")
        if ceiling < 5:
            print("  -> UNDER FIVE. This class is a TIME SAVING, not a gain.")
        else:
            any_class_worth_files = True
            print("  -> five or more. A files gain is possible and must be measured.")

        tsv.append(
            "\t".join(
                (
                    division,
                    features,
                    decider,
                    str(len(group)),
                    str(len(decided)),
                    str(by_decider.get(decider, 0)),
                    str(len(undecided)),
                    f"{win_median:.0f}",
                    f"{win_p75:.0f}",
                    str(len(never)),
                    str(len(under)),
                    str(len(at_or_over)),
                    str(ceiling),
                    f"{pct:.1f}",
                )
            )
        )

        # Per-row detail for the undecided candidates: which routes ate the
        # clock, and how much the decider got.  This is what the brief asks to
        # be LISTED, not only counted.
        print(f"  --- the {ceiling} candidate rows, by clock spent above {decider} ---")
        detail = []
        for r in never + under:
            got = reached_ms(r, decider)
            above, spent = clock_above(r, decider)
            detail.append((above, r.corpus_path, got, spent[:3]))
        detail.sort(key=lambda t: (-t[0], t[1]))
        for above, path, got, spent in detail:
            got_s = "NEVER REACHED" if got is None else f"{got} ms"
            top3 = ", ".join(f"{route}={ms}ms" for route, ms in spent)
            print(f"    {above:>7} ms above | got {got_s:<14} | {path}")
            print(f"            {top3}")

    if args.tsv_out:
        Path(args.tsv_out).write_text("\n".join(tsv) + "\n", encoding="utf-8")
        print(f"\nwrote {args.tsv_out}")

    # Exit status depends on the FINDING: non-zero when no class clears the
    # five-file bar, so a caller cannot read "sizing ran" as "sizing found
    # something".
    return 0 if any_class_worth_files else 3


if __name__ == "__main__":
    raise SystemExit(main())
