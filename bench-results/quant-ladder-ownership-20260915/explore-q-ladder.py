#!/usr/bin/env python3
"""EXPLORATORY (ADR-2103): what does the `q:` ladder actually do on the 482 rows?

Run BEFORE the sizing so the sizing's vocabulary is chosen from what the rows
say rather than from what the quantifier-free ADR-2100 table happened to use.
Reads the committed ADR-2100 `--trace` capture; re-runs nothing.

Usage: explore-q-ladder.py <trace.tsv> <phase1-ceiling.tsv>
"""

import collections
import json
import sys

# The quantifier-free ladder's rung names (ADR-2100's `size-ceiling.py` LADDER),
# used here only to answer "did this row reach the QF ladder at all".
QF_LADDER = set(
    """datatype-acyclicity datatype-elim datatype-native dl-online lira-dpll uf-nra
nra-real-root cas-ideal-refuter nra uf-arith-overbound-probe bv2nat-range bv2nat-blast
int-linear-refuters uf-routes abv-online-cdclt array-fast-path nia-square int-blast-ladder
nia-linearize int-real-relax qf-bv""".split()
)
SUBROUTE_OF_RUNG = {
    "lia-dpll": "int-linear-refuters",
    "lia-simplex": "int-linear-refuters",
    "lia-diophantine": "int-linear-refuters",
    "milp": "int-linear-refuters",
    "euf-online": "uf-routes",
    "euf-offline": "uf-routes",
    "uf-arithmetic": "uf-routes",
    "uf-arith-online": "uf-routes",
    "uf-arith-lazy-overbound": "uf-routes",
    "uf-arith-lazy-overbound-pre-lia": "uf-arith-overbound-probe",
    "ufbv-declared-sort-lazy": "uf-routes",
    "uf-finite-domain-pigeonhole": "uf-routes",
    "nia-bounded-blast": "nia-linearize",
    "nra-even-power": "nra",
    "integer-algebraic-refutation": "int-linear-refuters",
    "coercion-relax": "int-real-relax",
}


def trail(cell):
    """Both prefixes. ADR-2075: reading only `; route-trail ` drops the
    watchdog-killed rows, which is most of this population."""
    for marker in ("; route-trail ", "; partial route-trail "):
        if cell.startswith(marker):
            try:
                return json.loads(cell[len(marker):])
            except json.JSONDecodeError:
                return None
    return None


def main():
    trace_tsv, frame_tsv = sys.argv[1:3]
    frame = {}
    for line in open(frame_tsv):
        cells = line.rstrip("\n").split("\t")
        if cells[0] == "division":
            continue
        frame[cells[1]] = cells
    if len(frame) < 600:
        sys.exit(f"ABORT: frame parse found {len(frame)} rows")

    rows = []
    scanned = 0
    for line in open(trace_tsv):
        cells = line.rstrip("\n").split("\t")
        if len(cells) < 6:
            continue
        path, verdict, _rc, _ms, route_line, cell = cells[:6]
        if verdict in ("sat", "unsat"):
            continue
        scanned += 1
        row = frame.get(path)
        if row is None:
            sys.exit(f"ABORT: {path} is in the capture and not in the frame")
        if row[7] != "yes" or "decided_by=none" not in route_line:
            continue
        tr = trail(cell)
        if tr is None:
            continue
        routes = [
            SUBROUTE_OF_RUNG.get(a.get("route", ""), a.get("route", ""))
            for a in tr.get("attempts", [])
        ]
        if any(r in QF_LADDER for r in routes):
            continue
        rows.append((path, tr, route_line))

    print(f"undecided scanned         : {scanned}")
    print(f"no-QF-dispatch rows       : {len(rows)}")

    last_q = collections.Counter()
    last_full = collections.Counter()
    bound = collections.Counter()
    for _path, tr, route_line in rows:
        qs = [a for a in tr.get("attempts", []) if a.get("route", "").startswith("q:")]
        if not qs:
            last_q["<no q: attempt>"] += 1
            continue
        non_sink = [a for a in qs if a.get("route") != "q:timeout"]
        attempt = (non_sink or qs)[-1]
        last_q[attempt["route"]] += 1
        last_full[(attempt["route"], attempt.get("outcome"), attempt.get("reason"))] += 1
        for field in route_line.split():
            if field.startswith("bound_by="):
                bound[field[len("bound_by="):]] += 1

    print("\n-- last non-sink q: attempt --")
    for key, count in last_q.most_common():
        print(f"  {count:>4}  {key}")
    print("\n-- (route, outcome, reason) of that last attempt --")
    for key, count in last_full.most_common(25):
        print(f"  {count:>4}  {key}")
    print("\n-- bound_by --")
    for key, count in bound.most_common():
        print(f"  {count:>4}  {key}")

    detail = collections.Counter()
    for _path, tr, _rl in rows:
        for attempt in tr.get("attempts", []):
            if attempt.get("route", "").startswith("q:") and attempt.get("outcome") == "declined":
                detail[
                    (attempt["route"], attempt.get("reason"), (attempt.get("detail") or "")[:95])
                ] += 1
    print("\n-- top q: declines (route, reason, detail) --")
    for key, count in detail.most_common(35):
        print(f"  {count:>5}  {key}")


if __name__ == "__main__":
    main()
