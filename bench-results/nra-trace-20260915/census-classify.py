#!/usr/bin/env python3
"""The QF_NRA census: bucket every undecided file by what actually stopped it.

ADR-2110, lane NRA-TRACE.  Reads outcome-ledger rows (ADR-2102) written by
`census-run.sh` and joins them against `shape-83.tsv`.

Two axes, kept apart on purpose
-------------------------------

**What stopped it** is read from the TYPED trail, never from the prose:
`LedgerRow.reasons` / `.details` / `.names` come from the route-trail JSON via
`route_trace_reader`, which is the whole point of ADR-2101.  The bucket key is
the LAST NON-FRONT-DOOR decline -- `fd:parse` carries a probe note
(`string_bound=12`) that is not a reason at all, and every `fd:` attempt logged
after a theory route copies that route's text verbatim, so the literal last
entry classified one file by the parser's probe string in the 2026-09-09 sweep.

A row the watchdog killed is a **different** bucket from a row that declined,
even when the last recorded decline is the same: the first says "we were still
working in route X when the clock ran out", the second says "route X refused".
`LedgerRow.is_partial` is the authority for which, and a partial row's counters
are lower bounds that are never averaged into a rate.

**What shape it is** is the join against `shape-83.tsv` -- declared `:status`,
variable count, maximum polynomial degree, real division.  The two axes answer
different questions ("why did it stop" vs "what would it take") and a table
that fuses them hides both.

Exit status depends on the finding: a file in the population with no ledger row
is NAMED and makes this command non-zero.  A census that quietly covered 80 of
83 is a measurement of the 80.
"""

from __future__ import annotations

import argparse
import collections
import os
import sys
from pathlib import Path

sys.path.insert(0, os.environ.get("AXEYUM_SCRIPTS", "scripts"))
import outcome_ledger as ol  # noqa: E402

#: Front-door attempts are instrumentation, not routes; see the module
#: docstring for the two ways reading them as reasons has already gone wrong.
FRONT_DOOR = "fd:"

#: Wrappers that RESTATE an inner route's reason as their own. Each is a
#: prefix plus the marker after which the quoted inner reason begins. Reading
#: past them is not cosmetic: on the first 40 rows of this census the LAST
#: non-front-door decline was `q:skolem-qf/unsupported` on 18 files and
#: `q:nat-induction/not-applicable` on 17 -- quantifier rungs that run AFTER
#: the whole real branch on a quantifier-free query and whose text quotes the
#: `nra` reason verbatim. Bucketing on them produced a table in which the two
#: largest QF_NRA buckets were quantifier routes. This is the 2026-09-09
#: sweep's hazard 3 in a new place.
RESTATING_WRAPPERS = (
    "Its own reason was: ",
    "the reduced solve's own reason was ",
)

#: A bracketed `UnknownKind` the dispatch wrapper prefixes onto the quoted
#: reason (`[ResourceLimit] nonlinear abstraction: ...`).
KIND_PREFIX = "["


def unwrap(detail: str) -> str:
    """The innermost quoted reason inside a chain of restating wrappers."""
    seen = 0
    while seen < 8:
        for marker in RESTATING_WRAPPERS:
            idx = detail.rfind(marker)
            if idx >= 0:
                detail = detail[idx + len(marker) :]
                break
        else:
            break
        seen += 1
    detail = detail.strip()
    if detail.startswith(KIND_PREFIX) and "]" in detail:
        detail = detail.split("]", 1)[1].strip()
    return detail


def normalize(detail: str) -> str:
    """Collapse the counts out of a reason so one CAUSE is one bucket.

    `771 cross-products project to 36945 linear-real atoms` and
    `500 cross-products project to 9559 linear-real atoms` are one finding
    with two sizes, and the sizes belong in the per-file TSV, not in the key.
    """
    out: list[str] = []
    in_digits = False
    for ch in detail:
        if ch.isdigit():
            if not in_digits:
                out.append("N")
                in_digits = True
        else:
            in_digits = False
            out.append(ch)
    return "".join(out)


def terminal(row: ol.LedgerRow) -> tuple[str, str, str]:
    """`(route, reason, detail)` of the decline that actually stopped the run.

    The route of record is the one that HELD THE BUDGET (`bound_by`), not the
    last one in the trail: the ladder keeps walking past the real branch on a
    QF_NRA query and every later rung restates the reason it inherited. When
    `bound_by` recorded no decline of its own (it decided, or the reading is
    partial), fall back to the last non-front-door decline -- unwrapped.

    `("none", "none", "")` when the trail records no decline at all, which is
    a real answer and not a missing one.
    """
    reasons = row.reasons
    details = row.details
    bound = row.bound_by
    if bound:
        for i, (route, reason) in enumerate(reasons):
            if route == bound:
                detail = details[i] if i < len(details) else ""
                return route, reason, unwrap(detail)
    for i in range(len(reasons) - 1, -1, -1):
        route, reason = reasons[i]
        if route.startswith(FRONT_DOOR):
            continue
        detail = details[i] if i < len(details) else ""
        return route, reason, unwrap(detail)
    return "none", "none", ""


def bucket(row: ol.LedgerRow) -> str:
    """The census bucket for one row."""
    if row.verdict in ("sat", "unsat"):
        return f"DECIDED:{row.verdict}"
    route, reason, detail = terminal(row)
    if route == "none":
        if row.is_partial:
            return f"killed mid-search in {row.bound_by or 'unknown'}"
        return "no typed decline recorded"
    key = f"{route}/{reason}"
    if detail:
        key += f" [{normalize(detail)[:78]}]"
    if row.is_partial:
        key = "killed mid-search: " + key
    return key


def load_shapes(path: Path) -> dict[str, dict[str, str]]:
    rows: dict[str, dict[str, str]] = {}
    with path.open(encoding="utf-8") as fh:
        header = next(fh).rstrip("\n").split("\t")
        for line in fh:
            values = line.rstrip("\n").split("\t")
            record = dict(zip(header, values, strict=False))
            rows[record["file"]] = record
    return rows


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ledger", action="append", required=True,
                    help="a ledger TSV (repeatable, one per shard)")
    ap.add_argument("--shapes", required=True)
    ap.add_argument("--population", required=True,
                    help="the file list the census was supposed to cover")
    ap.add_argument("--tsv", help="write the per-file join here")
    args = ap.parse_args(argv)

    rows: list[ol.LedgerRow] = []
    for path in args.ledger:
        rows.extend(ol.read_ledger(path))
    by_file = {r.corpus_path: r for r in rows}
    shapes = load_shapes(Path(args.shapes))
    population = [p for p in Path(args.population).read_text().split() if p]

    missing = [p for p in population if p not in by_file]
    duplicates = len(rows) - len(by_file)

    print(f"population {len(population)}   ledger rows {len(rows)} "
          f"({len(by_file)} distinct files, {duplicates} repeats)")
    print(f"shape rows {len(shapes)}\n")

    covered = [p for p in population if p in by_file]

    print("== verdicts ==")
    for v, c in collections.Counter(by_file[p].verdict for p in covered).most_common():
        print(f"  {v:10s} {c:3d}")

    partial = [p for p in covered if by_file[p].is_partial]
    print(f"\n  partial (watchdog-killed) readings: {len(partial)} of {len(covered)}")

    print("\n== BUCKETS (typed terminal reason; biggest first) ==")
    buckets: dict[str, list[str]] = collections.defaultdict(list)
    for p in covered:
        buckets[bucket(by_file[p])].append(p)
    order = sorted(buckets, key=lambda k: (-len(buckets[k]), k))
    for key in order:
        members = buckets[key]
        ms = [int(by_file[p].elapsed_ms) for p in members]
        print(f"  {len(members):3d}  {sum(ms) / 1000:7.1f}s  {key}")

    print("\n== bucket x declared :status ==")
    print(f"  {'bucket':58s} {'sat':>4s} {'unsat':>6s} {'unk':>4s}")
    for key in order:
        counts = collections.Counter(
            shapes.get(p, {}).get("status", "?") for p in buckets[key]
        )
        print(f"  {key[:58]:58s} {counts['sat']:4d} {counts['unsat']:6d} "
              f"{counts['unknown']:4d}")

    print("\n== bucket x shape (medians over the bucket) ==")
    print(f"  {'bucket':48s} {'n':>3s} {'vars':>6s} {'deg':>5s} {'div':>4s} "
          f"{'atoms':>6s}")
    for key in order:
        members = [p for p in buckets[key] if p in shapes]
        if not members:
            print(f"  {key[:48]:48s} {len(buckets[key]):3d} {'-':>6s} {'-':>5s} "
                  f"{'-':>4s} {'-':>6s}")
            continue

        def med(field: str, group: list[str] = members) -> float:
            vals = sorted(int(shapes[p][field]) for p in group)
            mid = len(vals) // 2
            return (vals[mid] if len(vals) % 2 else (vals[mid - 1] + vals[mid]) / 2)

        div = sum(int(shapes[p]["has_div"]) for p in members)
        print(f"  {key[:48]:48s} {len(members):3d} {med('n_vars'):6.0f} "
              f"{med('max_degree'):5.0f} {div:4d} {med('n_assert'):6.0f}")

    print("\n== which route held the budget (bound_by) ==")
    for k, c in collections.Counter(
        by_file[p].bound_by or "none" for p in covered
    ).most_common():
        print(f"  {k:30s} {c:3d}")

    print("\n== every distinct typed decline (route/reason), any position ==")
    seen: collections.Counter[str] = collections.Counter()
    for p in covered:
        for route, reason in by_file[p].reasons:
            if not route.startswith(FRONT_DOOR):
                seen[f"{route}/{reason}"] += 1
    for k, c in seen.most_common():
        print(f"  {k:46s} {c:3d}")

    if args.tsv:
        cols = ("file", "verdict", "partial", "bucket", "terminal_route",
                "terminal_reason", "terminal_detail", "bound_by", "elapsed_ms",
                "status", "n_vars", "max_degree", "n_assert", "has_div")
        with open(args.tsv, "w", encoding="utf-8") as fh:
            fh.write("\t".join(cols) + "\n")
            for p in covered:
                r = by_file[p]
                route, reason, detail = terminal(r)
                sh = shapes.get(p, {})
                fh.write("\t".join(str(x) for x in (
                    p, r.verdict, r.partial, bucket(r), route, reason,
                    detail.replace("\t", " ")[:160], r.bound_by, r.elapsed_ms,
                    sh.get("status", "?"), sh.get("n_vars", "?"),
                    sh.get("max_degree", "?"), sh.get("n_assert", "?"),
                    sh.get("has_div", "?"),
                )) + "\n")
        print(f"\nwrote {args.tsv}")

    if missing:
        print(f"\ncensus-classify: {len(missing)} POPULATION FILES WITH NO "
              f"LEDGER ROW", file=sys.stderr)
        for p in missing[:20]:
            print(f"  {p}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
