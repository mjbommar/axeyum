#!/usr/bin/env python3
"""EXPLORATORY (ADR-2103): which `q:` rungs appear at all, and which never run?

CORRECTION this script exists to record: `RouteTrace::record_result` maps a
`CheckResult::Unknown` to `record_declined`, so the trail's `declined` outcome
does NOT distinguish "this rung declined and the ladder continued" from "this
rung's `Unknown` WAS the answer". A first pass here tested `outcome != declined`
as a detector of terminal unknowns and got 0 of 482 -- which is what a detector
that cannot fire prints. Terminality has to be read off the LADDER'S CONTROL
FLOW plus which rungs are absent from the trail, never off the outcome word.

Usage: explore-rung-incidence.py <trace.tsv> <phase1-ceiling.tsv>
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

    present = collections.Counter()
    rows = 0
    # Rows on which a "QF-residual" rung ran -- the four that end the ladder by
    # `return check_auto(residual)` and so skip `q:nat-induction`, which is the
    # only rung below them that consumes the ORIGINAL assertions.
    residual_rungs = {
        "q:skolem-qf", "q:valid-universal-qf", "q:vacuous-universal-qf", "q:fourier-motzkin",
    }
    residual_rows = collections.Counter()
    residual_without_induction = collections.Counter()
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
        tr, _partial = trail(cell)
        if tr is None:
            continue
        attempts = tr.get("attempts", [])
        routes = [SUBROUTE_OF_RUNG.get(a.get("route", ""), a.get("route", "")) for a in attempts]
        if any(r in QF_LADDER for r in routes):
            continue
        rows += 1
        names = {a.get("route") for a in attempts}
        for name in names:
            if name.startswith("q:"):
                present[name] += 1
        for rung in residual_rungs & names:
            # A `probe` outcome on these four means the rung DID hand a
            # quantifier-free residual to `check_auto`; a `declined` means it
            # did not apply. Only the probe form is the terminal-return path.
            probed = any(
                a.get("route") == rung and a.get("outcome") == "probe" for a in attempts
            )
            if probed:
                residual_rows[rung] += 1
                if "q:nat-induction" not in names:
                    residual_without_induction[rung] += 1

    print(f"no-QF-dispatch rows: {rows}")
    print("\n-- rows on which each q: rung appears at least once --")
    for name, count in present.most_common():
        print(f"  {count:>5}  {name}")
    print("\n-- rungs that NEVER appear on any of these rows --")
    known = [
        "q:ground-subset", "q:bool-skeleton", "q:checked-fast-path", "q:skolem-qf",
        "q:valid-universal-qf", "q:vacuous-universal-qf", "q:eq-partition",
        "q:unsat-universal", "q:fourier-motzkin", "q:forall-exists-witness",
        "q:finite-expansion", "q:uf-fmf-probe", "q:mbqi-quick", "q:egraph", "q:mbqi",
        "q:uf-fmf-full", "q:nat-induction", "q:timeout",
    ]
    for name in known:
        if name not in present:
            print(f"         {name}")
    print("\n-- rows where a QF-residual rung PROBED (handed the residual to check_auto) --")
    for name in sorted(residual_rows):
        print(f"  {residual_rows[name]:>5}  {name}   "
              f"(of which {residual_without_induction[name]} never ran q:nat-induction)")
    if not residual_rows:
        print("  none")


if __name__ == "__main__":
    main()
