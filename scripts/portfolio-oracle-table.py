#!/usr/bin/env python3
"""The per-division decision table: what a parallel portfolio would actually buy.

Joins the two instruments, which see different things and are not redundant:

* `portfolio-oracle.py` (enlarged-budget probe) says whether the LADDER decides
  the file at the competition budget, and at 5x it.  Its `STALE-DECIDED` rows
  are the ones the committed loss population has gone stale on -- the current
  tree already wins them -- and excluding those is the whole reason it is run.

* `route-solo-sweep.py` (solo prober) says which routes decide the file ALONE
  inside the competition budget, and how fast.  This is the instrument that sees
  the case the probe cannot: a route starving the ladder gets a *fraction of the
  wall budget*, so raising the wall raises its share too and the routes behind
  it never run however long you wait.  `bmc-arrays/bubbleSort.smt2` is unknown
  at 24 s and still unknown at 120 s, while `abv-lazy-row` alone decides it in
  1,202 ms.

A file is counted a **prize** when the ladder does not decide it at the
competition budget AND some single route decides it alone inside that budget.
That is a lower bound in both directions: the solo prober runs the flat
assertion view with no preprocessing (so a route may decline here that the
dispatcher would have fed a normal form), and it covers seventeen named routes
rather than every route the ladder can reach.

Exit status is 2 if the solo data contains a cross-route verdict disagreement,
so a soundness break fails rather than being tabulated.
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import sys

DECIDED = ("sat", "unsat")


def read_tsv(path: pathlib.Path):
    rows = []
    with path.open() as fh:
        header = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            if line.startswith("#"):
                continue
            rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--probe", nargs="*", default=[], help="portfolio-oracle.py TSVs")
    ap.add_argument("--solo", nargs="*", default=[], help="route-solo-sweep.py TSVs")
    ap.add_argument("--budget-ms", type=int, default=24_000)
    args = ap.parse_args()

    # Ladder status per file, from the probe arm.
    ladder = {}
    for p in args.probe:
        for r in read_tsv(pathlib.Path(p)):
            status = r.get("status", "")
            if r.get("control_verdict") == "none" or r.get("probe_verdict") == "none":
                status = "ABORTED"
            ladder[r["file"]] = (r.get("division", "?"), status)

    # Solo verdicts per file.
    solo = collections.defaultdict(dict)
    division_of = {}
    for p in args.solo:
        for r in read_tsv(pathlib.Path(p)):
            solo[r["file"]][r["route"]] = (r["verdict"], int(r["wall_ms"] or 0))
            division_of[r["file"]] = r.get("division", "?")

    disagreements = []
    for path, rs in solo.items():
        verdicts = {v for v, _ in rs.values() if v in DECIDED}
        if len(verdicts) > 1:
            disagreements.append((path, rs))

    per_div = collections.defaultdict(lambda: collections.Counter())
    prizes = []
    for path, rs in sorted(solo.items()):
        div = division_of[path]
        winners = sorted(
            (w, route) for route, (v, w) in rs.items() if v in DECIDED and w <= args.budget_ms
        )
        _, ladder_status = ladder.get(path, ("?", "NOT-PROBED"))
        per_div[div]["solo_files"] += 1
        if ladder_status == "STALE-DECIDED":
            per_div[div]["ladder_wins"] += 1
            continue
        if ladder_status == "NOT-PROBED":
            per_div[div]["not_probed"] += 1
        per_div[div]["ladder_loses"] += 1
        if winners:
            per_div[div]["PRIZE-CANDIDATE"] += 1
            prizes.append((div, path, winners))
        else:
            per_div[div]["no_solo_route"] += 1

    print(f"{'division':<10} {'solo files':>10} {'ladder wins':>12} "
          f"{'ladder loses':>13} {'CAND':>6} {'no route':>9}")
    total = collections.Counter()
    for div in sorted(per_div):
        c = per_div[div]
        print(f"{div:<10} {c['solo_files']:>10} {c['ladder_wins']:>12} "
              f"{c['ladder_loses']:>13} {c['PRIZE-CANDIDATE']:>6} {c['no_solo_route']:>9}")
        total.update(c)
    print(f"{'TOTAL':<10} {total['solo_files']:>10} {total['ladder_wins']:>12} "
          f"{total['ladder_loses']:>13} {total['PRIZE-CANDIDATE']:>6} {total['no_solo_route']:>9}")
    if total["not_probed"]:
        print(f"\n{total['not_probed']} file(s) had no probe row and are counted as "
              f"ladder-loses; that is an assumption, not a measurement.")

    print("\nfastest deciding route on each prize:")
    fastest = collections.Counter()
    for div, path, winners in prizes:
        ms, route = winners[0]
        fastest[route] += 1
        others = ", ".join(f"{r}@{w}ms" for w, r in winners[1:4])
        print(f"  {div:<9} {route:<20} {ms:>7} ms   {path.split('/')[-1]}"
              + (f"   (also {others})" if others else ""))
    if not prizes:
        print("  (none)")
    else:
        print("\nprize count by fastest route:")
        for route, n in fastest.most_common():
            print(f"  {route:<24} {n}")

    # The band table IS the decision, so it is computed rather than asserted.
    #
    # A portfolio uniquely serves ONE band: a winner that needs a large fraction
    # of the budget, queued behind a route that needs the same.  A per-route
    # reserve cannot serve that band, because splitting one clock N ways leaves
    # the winner too little.  Either end of it belongs to something cheaper: a
    # sub-second winner is reached by a one-second reserve, and a winner that
    # wants more than the whole budget is reached by neither.
    bands = collections.Counter()
    for div, path, winners in prizes:
        ms = winners[0][0]
        if ms < 1_000:
            bands["under 1 s (a reserve reaches it)"] += 1
        elif ms < args.budget_ms // 4:
            bands[f"1 s to {args.budget_ms // 4000} s (a reserve reaches it)"] += 1
        else:
            bands[f"{args.budget_ms // 4000} s to {args.budget_ms // 1000} s "
                  f"(MIDDLE BAND: only a portfolio)"] += 1
    for path, rs in sorted(solo.items()):
        if ladder.get(path, ("?", "NOT-PROBED"))[1] == "STALE-DECIDED":
            continue
        over = [w for _, (v, w) in rs.items() if v in DECIDED and w > args.budget_ms]
        if over and not any(w <= args.budget_ms for _, (v, w) in rs.items() if v in DECIDED):
            bands[f"over {args.budget_ms // 1000} s (neither reaches it)"] += 1
    print("\nfastest route that decides ALONE, on files the ladder loses:")
    if not bands:
        print("  (no file the ladder loses is decided alone by any probed route)")
    for band in sorted(bands):
        print(f"  {band:<48} {bands[band]:>4}")

    if disagreements:
        print("\nCROSS-ROUTE VERDICT DISAGREEMENT -- soundness alarm:", file=sys.stderr)
        for path, rs in disagreements:
            print(f"  {path}", file=sys.stderr)
            for route, (verdict, _) in sorted(rs.items()):
                if verdict in DECIDED:
                    print(f"    {route:<22} {verdict}", file=sys.stderr)
        return 2
    print("\ncross-route soundness: no two routes disagreed on any file measured here")
    return 0


if __name__ == "__main__":
    sys.exit(main())
