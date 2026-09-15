#!/usr/bin/env python3
"""ADR-2103 SIZING: what can quantified-ladder ownership reach?

The question, from the exit criteria: over the **482** undecided Tier 1 rows
that ADR-2100 measured as never reaching the quantifier-free dispatch ladder,
how many have an **enterable owning rung BELOW their terminal one**?

METHOD, and why it needs no ownership table
-------------------------------------------

"A rung below the terminal one" presupposes that a RUNG ended the ladder. On
this ladder that presupposition is checkable on its own, and it is checked
FIRST, because a ceiling computed over rows the CLOCK ended is a ceiling on
nothing. Three things can end the quantified ladder in `solve`:

  1. **A rung's non-decision.** The only case an ownership declaration can
     change. On the trail it looks like: rung `R` ran, some rung below `R` did
     not, and neither `q:timeout` nor a partial (watchdog-killed) trail
     explains the absence.
  2. **The clock.** `config_with_remaining_timeout` returns `None` and
     `quantified_timeout(..)` records `q:timeout`; or the harness watchdog kills
     the process and the trail is written with the `; partial ` prefix. No
     declaration on any route changes either.
  3. **Running out of rungs.** `q:nat-induction` ran and declined; there is
     nothing below it.

So the ceiling is bounded above by |class 1|, and that count is computed from
the ladder ORDER and the trail alone. If it is zero, the ceiling is zero for
EVERY possible ownership table, which is a stronger statement than one derived
from a particular table -- and it is the statement this script makes.

A nonzero class-1 count is NOT reported as the ceiling: each such row is printed
individually with the rungs it skipped, to be checked for ownership and
enterability by hand. Ten rows is a hand-check; the script says so rather than
inventing an `EVIDENCE` table for a ladder whose rungs all run on every row and
whose trail is therefore no evidence about constructs at all.

TWO CORRECTIONS this script's own runs produced, recorded beside the rules
-------------------------------------------------------------------------

**First: `outcome != "declined"` does not detect a terminal `Unknown`.**
`RouteTrace::record_result` maps `CheckResult::Unknown` to `record_declined`, so
a rung whose `Unknown` WAS the ladder's answer and a rung that declined and let
it continue are the same word on the trail. The first pass tested that word and
got 0 of 482 -- which is exactly what a detector that cannot fire prints.
Terminality is read off the ladder's control flow and the ABSENCE of rungs
below, never off the outcome word.

**Second: six rungs record nothing when they decline.** `q:checked-fast-path`,
`q:skolem-qf`, `q:vacuous-universal-qf`, `q:eq-partition`, `q:unsat-universal`
and `q:fourier-motzkin` call `record_quant_rung_result` only on a DECISION (and
`q:skolem-qf` / `q:fourier-motzkin` a `probe` only when they hand a
quantifier-free residual on). Their absence from a trail is therefore not
evidence that they were skipped, and treating it as such would have reported
every one of the 482 rows as a candidate. They are listed in
`SILENT_ON_DECLINE` and excluded from the "was a rung below skipped" test.

Usage: size-q-ceiling.py <trace.tsv> <phase1-ceiling.tsv>
"""

import collections
import json
import sys

# The quantified ladder, in the order `solve` -> `finish_quantified_solve` ->
# `finish_quantified_solve_or_induct` RUNS it (control flow, not source order:
# ADR-2100's first sizing run read the order off the source TEXT and reported
# 102 rows against a true 0).
#
#   solve:                      ground-subset, bool-skeleton, checked-fast-path,
#                               skolem-qf, valid-universal-qf,
#                               vacuous-universal-qf, eq-partition,
#                               unsat-universal, fourier-motzkin
#   finish_quantified_solve:    forall-exists-witness, finite-expansion,
#                               uf-fmf-probe, mbqi-quick, egraph, mbqi,
#                               uf-fmf-full
#   ..._or_induct:              nat-induction
LADDER = [
    "q:ground-subset",
    "q:bool-skeleton",
    "q:checked-fast-path",
    "q:skolem-qf",
    "q:valid-universal-qf",
    "q:vacuous-universal-qf",
    "q:eq-partition",
    "q:unsat-universal",
    "q:fourier-motzkin",
    "q:forall-exists-witness",
    "q:finite-expansion",
    "q:uf-fmf-probe",
    "q:mbqi-quick",
    "q:egraph",
    "q:mbqi",
    "q:uf-fmf-full",
    "q:nat-induction",
]
POSITION = {name: i for i, name in enumerate(LADDER)}

# `q:timeout` is the ladder's BUDGET SINK, not a rung: `quantified_timeout`
# records it from nine different program points. Its presence is the evidence
# that the clock ended the ladder, and it is never a "rung below" anything.
BUDGET_SINK = "q:timeout"

# Rungs that record NOTHING when they decline -- see the second correction in
# the module docstring. Their absence from a trail is not evidence of a skip.
SILENT_ON_DECLINE = {
    "q:checked-fast-path",
    "q:skolem-qf",
    "q:vacuous-universal-qf",
    "q:eq-partition",
    "q:unsat-universal",
    "q:fourier-motzkin",
}

# ADR-2100's quantifier-free ladder, to identify rows that reached it. Those are
# ADR-2100's population, not this one's.
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
    """Both prefixes. The watchdog path prints `; partial route-trail ` -- the
    prefix ADR-2075 published and ADR-2100's own runner then re-broke. A partial
    trail is a trail; it is a PREFIX of the attempt list, and the fact that it
    is a prefix is itself the finding this script needs from it."""
    for marker in ("; route-trail ", "; partial route-trail "):
        if cell.startswith(marker):
            try:
                return json.loads(cell[len(marker):]), marker.startswith("; partial")
            except json.JSONDecodeError:
                return None, None
    return None, None


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__.strip().splitlines()[-1])
    trace_tsv, frame_tsv = sys.argv[1:3]

    frame = {}
    for line in open(frame_tsv):
        cells = line.rstrip("\n").split("\t")
        if cells[0] == "division":
            continue
        frame[cells[1]] = cells
    if len(frame) < 600:
        sys.exit(f"ABORT: the frame parse found {len(frame)} rows, not a plausible count")

    scanned = joined = 0
    population = 0
    per_div = {}
    classes = collections.Counter()
    candidates = []

    for line in open(trace_tsv):
        cells = line.rstrip("\n").split("\t")
        if len(cells) < 6 or cells[0] == "file":
            continue
        path, verdict, _rc, _ms, route_line, cell = cells[:6]
        if verdict in ("sat", "unsat"):
            continue
        scanned += 1
        row = frame.get(path)
        if row is None:
            sys.exit(
                f"ABORT: {path} is in this lane's capture and not in PLAN-SIZING's "
                "inventory. The two populations must be the same rows or the "
                "denominators below describe different things."
            )
        joined += 1
        if row[7] != "yes" or "decided_by=none" not in route_line:
            continue
        parsed, partial = trail(cell)
        if parsed is None:
            continue
        attempts = parsed.get("attempts", [])
        qf_seen = [
            SUBROUTE_OF_RUNG.get(a.get("route", ""), a.get("route", ""))
            for a in attempts
        ]
        if any(r in QF_LADDER for r in qf_seen):
            continue  # ADR-2100's population, not this one's

        population += 1
        div = path.split("/", 1)[0]
        per_div.setdefault(div, collections.Counter())
        per_div[div]["rows"] += 1

        names = [a.get("route") for a in attempts]
        q_names = [n for n in names if n in POSITION]
        saw_sink = BUDGET_SINK in names
        if not q_names:
            classes["no q: rung ran at all"] += 1
            per_div[div]["no-rung"] += 1
            continue

        terminal = max(q_names, key=lambda n: POSITION[n])
        below = [
            n for n in LADDER
            if POSITION[n] > POSITION[terminal] and n not in SILENT_ON_DECLINE
        ]

        if not below:
            classes["ladder exhausted (nothing below the terminal rung)"] += 1
            per_div[div]["exhausted"] += 1
        elif saw_sink:
            classes["clock (q:timeout recorded)"] += 1
            per_div[div]["clock"] += 1
        elif partial:
            classes["watchdog kill (partial trail)"] += 1
            per_div[div]["watchdog"] += 1
        else:
            # CLASS 1: a rung below the terminal one did not run, and neither the
            # budget sink nor a watchdog kill explains it. The only class an
            # ownership declaration can reach.
            classes["A RUNG STOPPED THE LADDER (candidate)"] += 1
            per_div[div]["candidate"] += 1
            reasons = [
                (a.get("route"), a.get("reason"), (a.get("detail") or "")[:70])
                for a in attempts
                if a.get("route") == terminal
            ]
            candidates.append((path, terminal, below, reasons[-1] if reasons else None))

    print(f"undecided rows scanned              : {scanned}")
    print(f"  joined to PLAN-SIZING               : {joined} (must equal the line above)")
    print(f"  POPULATION (never reached the QF ladder) : {population}")
    print()
    print("-- what ended the quantified ladder --")
    for key, count in classes.most_common():
        print(f"  {count:>5}  {key}")
    print()
    candidate_total = classes["A RUNG STOPPED THE LADDER (candidate)"]
    print(f"CEILING (upper bound, before any ownership table): {candidate_total}")
    print("  A rung below the terminal one is skipped on this many rows for a reason")
    print("  an ownership declaration could change. Every other row is ended by the")
    print("  clock or has nothing below it, and NO ownership table changes either.")
    print()
    header = f"{'division':<12} {'rows':>5} {'cand':>5} {'clock':>6} {'watchdog':>9} {'exhausted':>10}"
    print(header)
    for div in sorted(per_div):
        d = per_div[div]
        print(
            f"{div:<12} {d['rows']:>5} {d['candidate']:>5} {d['clock']:>6} "
            f"{d['watchdog']:>9} {d['exhausted']:>10}"
        )
    totals = collections.Counter()
    for d in per_div.values():
        totals.update(d)
    print(
        f"{'TOTAL':<12} {totals['rows']:>5} {totals['candidate']:>5} {totals['clock']:>6} "
        f"{totals['watchdog']:>9} {totals['exhausted']:>10}"
    )

    if candidates:
        print()
        print(f"-- the {len(candidates)} candidate rows, for per-row ownership checking --")
        # NO CAP. A truncated candidate list makes the per-row check that
        # follows it cover a SUBSET while reporting on the whole -- the first
        # run of `check-candidates.py` verified 40 of 53 and said "every".
        for path, terminal, below, reason in candidates:
            print(f"  {path}")
            print(f"      terminal={terminal} skipped={below} last-reason={reason}")
    if population == 0:
        sys.exit("ABORT: the population is empty -- this script never saw its subject")


if __name__ == "__main__":
    main()
