#!/usr/bin/env python3
"""EXPLORATORY (ADR-2103): WHAT stopped the `q:` ladder on each of the 482 rows?

The sizing question is "is there an enterable owning rung BELOW the terminal
one". That presupposes the ladder was stopped BY A RUNG. This script checks the
presupposition first, because a ceiling computed over rows the CLOCK ended is
a ceiling on nothing.

Usage: explore-terminals.py <trace.tsv> <phase1-ceiling.tsv>
"""

import collections
import json
import sys

QF_LADDER = set(
    """datatype-acyclicity datatype-elim datatype-native dl-online lira-dpll uf-nra
nra-real-root cas-ideal-refuter nra uf-arith-overbound-probe bv2nat-range bv2nat-blast
int-linear-refuters uf-routes abv-online-cdclt array-fast-path nia-square int-blast-ladder
nia-linearize int-real-relax qf-bv""".split()
)
SUBROUTE_OF_RUNG = {
    "lia-dpll": "int-linear-refuters", "lia-simplex": "int-linear-refuters",
    "lia-diophantine": "int-linear-refuters", "milp": "int-linear-refuters",
    "euf-online": "uf-routes", "euf-offline": "uf-routes",
    "uf-arithmetic": "uf-routes", "uf-arith-online": "uf-routes",
    "uf-arith-lazy-overbound": "uf-routes",
    "uf-arith-lazy-overbound-pre-lia": "uf-arith-overbound-probe",
    "ufbv-declared-sort-lazy": "uf-routes", "uf-finite-domain-pigeonhole": "uf-routes",
    "nia-bounded-blast": "nia-linearize", "nra-even-power": "nra",
    "integer-algebraic-refutation": "int-linear-refuters", "coercion-relax": "int-real-relax",
}


def trail(cell):
    for marker in ("; route-trail ", "; partial route-trail "):
        if cell.startswith(marker):
            try:
                return json.loads(cell[len(marker):]), marker.startswith("; partial")
            except json.JSONDecodeError:
                return None, None
    return None, None


def main():
    trace_tsv, frame_tsv = sys.argv[1:3]
    frame = {}
    for line in open(frame_tsv):
        cells = line.rstrip("\n").split("\t")
        if cells[0] == "division":
            continue
        frame[cells[1]] = cells

    outcomes = collections.Counter()
    q_outcomes = collections.Counter()
    stop_class = collections.Counter()
    egraph_result_rows = []
    rows = 0
    for line in open(trace_tsv):
        cells = line.rstrip("\n").split("\t")
        if len(cells) < 6:
            continue
        path, verdict, _rc, _ms, route_line, cell = cells[:6]
        if verdict in ("sat", "unsat"):
            continue
        row = frame.get(path)
        if row is None or row[7] != "yes" or "decided_by=none" not in route_line:
            continue
        tr, partial = trail(cell)
        if tr is None:
            continue
        attempts = tr.get("attempts", [])
        routes = [SUBROUTE_OF_RUNG.get(a.get("route", ""), a.get("route", "")) for a in attempts]
        if any(r in QF_LADDER for r in routes):
            continue
        rows += 1
        for a in attempts:
            outcomes[a.get("outcome")] += 1
            if a.get("route", "").startswith("q:"):
                q_outcomes[(a.get("route"), a.get("outcome"))] += 1
        # A `q:egraph` recorded as a RESULT (not `declined`) is the
        # `finite_unknown` early return -- the one site in the quantified
        # ladder where a route's `Err(Unsupported)` ends the ladder outright.
        for a in attempts:
            if a.get("route") == "q:egraph" and a.get("outcome") != "declined":
                egraph_result_rows.append((path, a.get("outcome"), (a.get("detail") or "")[:70]))

        qs = [a for a in attempts if a.get("route", "").startswith("q:")]
        q_names = [a.get("route") for a in qs]
        saw_timeout = "q:timeout" in q_names
        saw_induction = "q:nat-induction" in q_names
        if saw_timeout:
            stop_class["clock (q:timeout recorded)"] += 1
        elif partial:
            stop_class["watchdog kill (partial trail, no q:timeout)"] += 1
        elif saw_induction:
            stop_class["ladder exhausted (q:nat-induction ran, declined)"] += 1
        else:
            stop_class[f"OTHER -- last q: rung = {q_names[-1] if q_names else 'none'}"] += 1

    print(f"no-QF-dispatch rows: {rows}")
    print("\n-- every attempt outcome spelling seen --")
    for k, v in outcomes.most_common():
        print(f"  {v:>6}  {k!r}")
    print("\n-- what ENDED the ladder --")
    for k, v in stop_class.most_common():
        print(f"  {v:>5}  {k}")
    print("\n-- q: (route, outcome) pairs that are NOT 'declined' --")
    for (r, o), v in sorted(q_outcomes.items()):
        if o != "declined":
            print(f"  {v:>5}  {r} -> {o!r}")
    print(f"\n-- q:egraph recorded as a RESULT (the finite_unknown early return): "
          f"{len(egraph_result_rows)} attempts --")
    for row in egraph_result_rows[:10]:
        print(f"     {row}")


if __name__ == "__main__":
    main()
