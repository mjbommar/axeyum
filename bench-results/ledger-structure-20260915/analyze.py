#!/usr/bin/env python3
"""Answer Phase 4's one question from `bench-results/ledger/` rows alone.

Plan (`docs/plan/dispatch-and-instrumentation-2026-09-15.md` §5): "Phase 4
runs only if Phase 3's ledger shows structure. Specifically: if, for some
feature class, one route decides a large majority of what gets decided and a
different route is tried first, then ladder order for that class should come
from the table."

This module reads through `scripts/outcome_ledger.py`'s `load()` -- no
re-parsing of `--trace` captures, no second authority for anything the ledger
already recorded, per this repository's own rule about where the five
instruments in the plan's own §0 failed.

Definitions used below, stated once so a reader can check them rather than
the numbers:

* **class** = a row's `features` column verbatim (ADR-2105's four-valued
  column: a real construct-class string, `"none"`, `"not-dispatched"`, or the
  empty string for a binary that predates the instrument -- none of this
  sweep's rows carry the empty value, since all of it ran on a schema-3
  binary).
* **decided rows** = rows whose `decided_by != "none"`.
* **first-attempted route** = the route named in the first entry of
  `attempt_trail` (empty when `attempts == 0`).
* **top decider** = the `decided_by` value with the most decided rows, within
  one (division, class) group.
* **modal first route** = the most common first-attempted route, within the
  same group, over ALL rows (decided and undecided) -- the group's current
  ladder head.
* **STRUCTURE** (the plan's test, applied per group): decided rows >= 5 (a
  floor against single-digit noise -- printed beside every verdict) AND the
  top decider holds >= 70% of decided rows AND the top decider is NOT the
  modal first route.
* **reorder-affected rows** = decided rows whose `decided_by` is the top
  decider but whose OWN first-attempted route is something else -- the rows
  whose attempt order would actually change under a reorder.
* **ceiling_ms** = the sum, over every row in the group whose first-attempted
  route is the modal first route AND which that route did NOT decide
  (including undecided rows), of that row's FIRST attempt's `elapsed_ms`
  (from `elapsed_ms_per_attempt`, positionally aligned with `attempt_trail`
  -- both are `LedgerRow` fields, not a re-parse). This is the time a reorder
  could recover AT MOST: money already being spent on a route that, on these
  rows, never decides. It is a ceiling, not a promised gain -- the *decided*
  routing conditions could differ when the head of the ladder changes.

Also computes the plan's §5 portfolio criterion: pairs of routes that each
account for >= 50% of one row's total per-attempt clock, restricted to
UNDECIDED rows, and grouped by the PAIR of routes rather than by row -- "two
routes each needing most of one clock" read across a population rather than
asserted from one file.

Usage:
    python3 analyze.py --sweep-id S1 --sweep-id S2 ... [--repo PATH]
        [--ledger-dir DIR] [--min-decided N] [--top-share 0.70]
"""

from __future__ import annotations

import argparse
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Sequence

HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent.parent / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import outcome_ledger as ol  # noqa: E402

DEFAULT_MIN_DECIDED = 5
DEFAULT_TOP_SHARE = 0.70
DEFAULT_PORTFOLIO_SHARE = 0.50


def division_of(corpus_path: str) -> str:
    """The Tier 1 division name: the corpus-relative path's first segment."""
    return corpus_path.split("/", 1)[0] if corpus_path else "unknown"


def _route_outcome(entry: str) -> tuple[str, str]:
    """Split one `attempt_trail` entry (`f"{route}:{outcome}"`) correctly.

    Route names are NOT colon-free (`fd:parse`, `q:mbqi-quick`, `fd:word-route`
    all appear in this sweep), while the three outcome tokens
    (`probe`/`decided`/`declined`, `RouteOutcome`'s own vocabulary) never
    contain one. `outcome_ledger.py` itself never re-parses this column -- it
    only exposes the raw split entries via `LedgerRow.trail` -- so a consumer
    that does `entry.partition(":")` (first colon) silently truncates every
    `fd:*`/`q:*` route to its bare prefix. Caught by a dry run against this
    lane's own partial sweep data: `first_route` on an all-quantified
    `AUFDTLIRA` slice came back as the single token `"fd"` on 67 of 67 rows,
    which does not exist as a route name. `rpartition(":")` (LAST colon) is
    correct because only the outcome side is colon-free.
    """
    route, _, outcome = entry.rpartition(":")
    return (route, outcome) if route else (entry, "")


def first_route(row: "ol.LedgerRow") -> str:
    trail = row.trail
    if not trail:
        return "none"
    route, _ = _route_outcome(trail[0])
    return route


def first_substantive_route(row: "ol.LedgerRow") -> str:
    """The first-attempted route that is not `fd:parse`'s own bound probe.

    Measured on this sweep: `fd:parse` is the first trail entry on 1,393 of
    1,400 rows and its own outcome is `probe`, never `decided` -- it cannot be
    a `top_decider` by construction. So "modal first route != top decider" is
    close to TAUTOLOGICALLY true for almost every group here, which would make
    the plan's literal STRUCTURE test look far more universal than the ladder
    actually is. This is the second-best answer to "what does the ladder
    actually try first among routes that could decide": the first trail entry
    that is not `fd:parse`. When the trail has only one entry (`fd:parse`
    alone, or empty) this returns `"none"`.
    """
    trail = row.trail
    for entry in trail:
        route, _ = _route_outcome(entry)
        if route != "fd:parse":
            return route
    return "none"


def per_attempt_routes_times(row: "ol.LedgerRow") -> list[tuple[str, str, int]]:
    """`(route, outcome, ms)` triples for every TIMED attempt in the trail.

    Attempts whose `elapsed_ms_per_attempt` entry is empty (the producer did
    not time that attempt -- ADR-2101's byte-stability tests cover this as a
    real, documented case) are excluded from the CLOCK computation but not
    from `first_route`: a route can be attempted first without a timed
    duration, and dropping it from the trail entirely would misstate `attempts`.

    `outcome` is kept, not discarded, because a route can appear MORE THAN
    ONCE in one trail -- `q:skolem-qf` shows up as `probe` early and again as
    `decided` at the end on real rows in this sweep
    (`UFNIA/2019-Preiner/qf/f2_rw8.smt2`: attempts 3 and 9 are both
    `q:skolem-qf`, `outcome=probe` then `outcome=decided`). A caller matching
    on route name ALONE and stopping at the first hit -- an earlier version of
    this function's caller did exactly that -- attributes the decision to the
    PROBE occurrence and undercounts every route attempted between the probe
    and the real decision. `decided_by`'s actual position is the LAST attempt
    named `route` whose `outcome == "decided"`.
    """
    trail = row.trail
    times = row.per_attempt_ms
    out: list[tuple[str, str, int]] = []
    for i, entry in enumerate(trail):
        route, outcome = _route_outcome(entry)
        ms = times[i] if i < len(times) else None
        if ms is not None:
            out.append((route, outcome, ms))
    return out


class Group:
    __slots__ = ("division", "features", "rows")

    def __init__(self, division: str, features: str) -> None:
        self.division = division
        self.features = features
        self.rows: list["ol.LedgerRow"] = []


def build_groups(rows: Sequence["ol.LedgerRow"]) -> dict[tuple[str, str], Group]:
    groups: dict[tuple[str, str], Group] = {}
    for row in rows:
        key = (division_of(row.corpus_path), row.features)
        g = groups.setdefault(key, Group(*key))
        g.rows.append(row)
    return groups


def analyze_group(
    g: Group, *, min_decided: int, top_share: float
) -> dict:
    rows = g.rows
    n = len(rows)
    decided_rows = [r for r in rows if r.decided_by != "none"]
    n_decided = len(decided_rows)

    decided_by_counts = Counter(r.decided_by for r in decided_rows)
    first_route_counts = Counter(first_route(r) for r in rows)
    substantive_counts = Counter(first_substantive_route(r) for r in rows)

    top_decider, top_decider_n = (
        decided_by_counts.most_common(1)[0] if decided_by_counts else (None, 0)
    )
    modal_first, modal_first_n = (
        first_route_counts.most_common(1)[0] if first_route_counts else (None, 0)
    )
    modal_substantive, modal_substantive_n = (
        substantive_counts.most_common(1)[0] if substantive_counts else (None, 0)
    )

    top_share_actual = (top_decider_n / n_decided) if n_decided else 0.0

    # The plan's literal test, applied verbatim.
    is_structure = (
        n_decided >= min_decided
        and top_share_actual >= top_share
        and top_decider is not None
        and top_decider != modal_first
    )
    # The same test against the SUBSTANTIVE first route (skipping `fd:parse`'s
    # free bound probe, which is first on 1,393/1,400 rows and never itself a
    # decider -- see `first_substantive_route`). This is the harder bar: it is
    # NOT satisfied merely because the ladder's own zero-cost probe precedes
    # every real route.
    is_structure_substantive = (
        n_decided >= min_decided
        and top_share_actual >= top_share
        and top_decider is not None
        and top_decider != modal_substantive
    )

    reorder_rows = 0
    if top_decider is not None:
        reorder_rows = sum(
            1
            for r in decided_rows
            if r.decided_by == top_decider and first_route(r) != top_decider
        )

    ceiling_ms = 0
    ceiling_files = 0
    if modal_first is not None:
        for r in rows:
            if first_route(r) != modal_first:
                continue
            if r.decided_by == modal_first:
                continue
            pr = per_attempt_routes_times(r)
            if pr and pr[0][0] == modal_first:
                ceiling_ms += pr[0][2]
                ceiling_files += 1

    # `prefix_cost_ms`: a second, more informative ceiling. `ceiling_ms` above
    # is exactly what the brief asks for -- the time the single
    # FIRST-attempted route spent on rows it did not decide -- but on every
    # quantified group here that route is `fd:parse`, a near-free bound probe
    # (single-digit-to-low-double-digit ms; see the README), not a competing
    # decider. `ceiling_ms` alone would understate the real reorder ceiling by
    # construction. `prefix_cost_ms` sums, over exactly the REORDER-AFFECTED
    # rows (decided by the top decider, whose OWN first-attempted route was
    # something else), every attempt's timed cost strictly BEFORE the top
    # decider's own (first) appearance in that row's trail -- i.e. everything
    # that promoting the top decider to the head of the ladder would let this
    # row skip entirely.
    prefix_cost_ms = 0
    prefix_cost_files = 0
    if top_decider is not None:
        for r in decided_rows:
            if r.decided_by != top_decider:
                continue
            pr = per_attempt_routes_times(r)
            prefix = 0
            found = False
            for route, outcome, ms in pr:
                # Match the DECISION occurrence, not any earlier same-named
                # probe -- see `per_attempt_routes_times`'s own docstring for
                # the real row (`q:skolem-qf` at both a `probe` and a later
                # `decided` position) that this guards against.
                if route == top_decider and outcome == "decided":
                    found = True
                    break
                prefix += ms
            if found:
                prefix_cost_ms += prefix
                prefix_cost_files += 1

    # Median elapsed_ms (whole-file wall clock) per deciding route, top 3.
    elapsed_by_decider: dict[str, list[int]] = defaultdict(list)
    for r in decided_rows:
        try:
            elapsed_by_decider[r.decided_by].append(int(r.elapsed_ms))
        except ValueError:
            pass
    median_by_decider = {
        route: statistics.median(vals) for route, vals in elapsed_by_decider.items()
    }

    return {
        "division": g.division,
        "features": g.features,
        "rows": n,
        "decided": n_decided,
        "decided_by_top3": decided_by_counts.most_common(3),
        "first_route_top3": first_route_counts.most_common(3),
        "top_decider": top_decider,
        "top_decider_n": top_decider_n,
        "top_share": top_share_actual,
        "modal_first": modal_first,
        "modal_first_n": modal_first_n,
        "modal_substantive": modal_substantive,
        "modal_substantive_n": modal_substantive_n,
        "median_by_decider_top3": [
            (route, median_by_decider[route])
            for route, _ in decided_by_counts.most_common(3)
        ],
        "structure": is_structure,
        "structure_substantive": is_structure_substantive,
        "reorder_rows": reorder_rows,
        "ceiling_ms": ceiling_ms,
        "ceiling_files": ceiling_files,
        "prefix_cost_ms": prefix_cost_ms,
        "prefix_cost_files": prefix_cost_files,
    }


def portfolio_pairs(
    rows: Sequence["ol.LedgerRow"], *, share: float = DEFAULT_PORTFOLIO_SHARE
) -> Counter:
    """Pairs of routes that EACH take >= `share` of the clock on undecided rows.

    Per row: find every route whose own summed attempt time (a route can be
    attempted more than once inside one trail on a retry path, though this is
    rare) is >= `share` of the row's total timed attempt time. On a row with
    exactly two attempts split close to 50/50 this can name two routes; on a
    row with one attempt dominating it names one route or none. The counter
    tallies, per PAIR of routes named on the SAME row, how many undecided rows
    produced that pair -- the population the plan's own portfolio criterion
    ("two routes each needing most of one clock") asks about, read across
    files rather than asserted from one.
    """
    pair_counts: Counter = Counter()
    for r in rows:
        if r.decided_by != "none":
            continue
        pr = per_attempt_routes_times(r)
        total = sum(ms for _, _, ms in pr)
        if total <= 0:
            continue
        per_route: dict[str, int] = defaultdict(int)
        for route, _outcome, ms in pr:
            per_route[route] += ms
        heavy = sorted(
            route for route, ms in per_route.items() if ms / total >= share
        )
        if len(heavy) >= 2:
            for i in range(len(heavy)):
                for j in range(i + 1, len(heavy)):
                    pair_counts[(heavy[i], heavy[j])] += 1
    return pair_counts


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--sweep-id", action="append", required=True)
    ap.add_argument("--ledger-dir", default=str(ol.LEDGER_DIR))
    ap.add_argument("--repo", default=None)
    ap.add_argument("--allow-branch", action="store_true")
    ap.add_argument("--min-decided", type=int, default=DEFAULT_MIN_DECIDED)
    ap.add_argument("--top-share", type=float, default=DEFAULT_TOP_SHARE)
    ap.add_argument("--portfolio-share", type=float, default=DEFAULT_PORTFOLIO_SHARE)
    ap.add_argument("--tsv-out", default=None, help="write the per-group table as TSV")
    args = ap.parse_args(argv)

    try:
        rows, flagged = ol.load(
            args.sweep_id,
            ledger_dir=args.ledger_dir,
            allow_branch=args.allow_branch,
            repo=args.repo,
        )
    except ol.StaleRows as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 2

    if flagged:
        print(
            f"NOTE: {len(flagged)} of {len(rows)} rows are branch measurements "
            "(--allow-branch was given)",
            file=sys.stderr,
        )

    groups = build_groups(rows)
    results = [
        analyze_group(g, min_decided=args.min_decided, top_share=args.top_share)
        for g in groups.values()
    ]
    results.sort(key=lambda r: (r["division"], r["features"]))

    print(f"rows total: {len(rows)}  groups: {len(results)}")
    print()
    header = (
        "division\tfeatures\trows\tdecided\ttop_decider\ttop_n\ttop_share\t"
        "modal_first\tmodal_first_n\tstructure\t"
        "modal_substantive\tmodal_substantive_n\tstructure_substantive\t"
        "reorder_rows\tceiling_ms\tceiling_files\t"
        "prefix_cost_ms\tprefix_cost_files"
    )
    print(header)
    if args.tsv_out:
        out_lines = [header]
    for r in results:
        line = (
            f"{r['division']}\t{r['features']}\t{r['rows']}\t{r['decided']}\t"
            f"{r['top_decider']}\t{r['top_decider_n']}\t{r['top_share']:.3f}\t"
            f"{r['modal_first']}\t{r['modal_first_n']}\t"
            f"{'STRUCTURE' if r['structure'] else 'no'}\t"
            f"{r['modal_substantive']}\t{r['modal_substantive_n']}\t"
            f"{'STRUCTURE' if r['structure_substantive'] else 'no'}\t"
            f"{r['reorder_rows']}\t{r['ceiling_ms']}\t{r['ceiling_files']}\t"
            f"{r['prefix_cost_ms']}\t{r['prefix_cost_files']}"
        )
        print(line)
        if args.tsv_out:
            out_lines.append(line)

    if args.tsv_out:
        Path(args.tsv_out).write_text("\n".join(out_lines) + "\n", encoding="utf-8")

    print()
    print("-- decided_by top3 / first_route top3 / median elapsed_ms by decider --")
    for r in results:
        print(
            f"{r['division']}\t{r['features']}\t"
            f"decided_by={r['decided_by_top3']}\t"
            f"first_route={r['first_route_top3']}\t"
            f"median_ms={r['median_by_decider_top3']}"
        )

    print()
    structure_groups = [r for r in results if r["structure"]]
    print(f"STRUCTURE groups (literal test): {len(structure_groups)} of {len(results)}")
    for r in structure_groups:
        print(
            f"  {r['division']}/{r['features']}: top_decider={r['top_decider']} "
            f"({r['top_decider_n']}/{r['decided']}={r['top_share']:.0%}), "
            f"modal_first={r['modal_first']}, reorder_rows={r['reorder_rows']}, "
            f"ceiling_ms={r['ceiling_ms']} over {r['ceiling_files']} files, "
            f"prefix_cost_ms={r['prefix_cost_ms']} over {r['prefix_cost_files']} files"
        )

    print()
    structure_sub_groups = [r for r in results if r["structure_substantive"]]
    print(
        f"STRUCTURE groups (substantive-first test, skipping fd:parse's free "
        f"probe): {len(structure_sub_groups)} of {len(results)}"
    )
    for r in structure_sub_groups:
        print(
            f"  {r['division']}/{r['features']}: top_decider={r['top_decider']} "
            f"({r['top_decider_n']}/{r['decided']}={r['top_share']:.0%}), "
            f"modal_substantive={r['modal_substantive']} ({r['modal_substantive_n']}/{r['rows']})"
        )

    print()
    pairs = portfolio_pairs(rows, share=args.portfolio_share)
    print(f"portfolio pairs (>= {args.portfolio_share:.0%} of clock, undecided rows): "
          f"{len(pairs)} distinct pairs")
    for (a, b), n in pairs.most_common(10):
        print(f"  {a} / {b}: {n} rows")

    return 0


if __name__ == "__main__":
    sys.exit(main())
