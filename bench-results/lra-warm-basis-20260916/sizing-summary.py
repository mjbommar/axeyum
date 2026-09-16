#!/usr/bin/env python3
"""ADR-2125 sizing: the share of wall clock spent RE-SOLVING from scratch.

The ceiling on a warm basis is what the from-scratch path costs today. Three
nested quantities, each with its own denominator, and the ADR quotes all three
because they answer different questions:

  simplex_cold_build_ms / total_ms   what a warm basis removes OUTRIGHT
  simplex_cold_ms       / total_ms   the whole from-scratch call: construction,
                                     pivots and witness -- the CEILING
  (cold + collect)      / total_ms   the ceiling if the per-cube LINEARIZATION
                                     is also made persistent, which is a second
                                     and larger change this lane did not make

Reported PER FILE and as a median, never pooled into one number. ADR-2122
measured the spread on this division to be the finding -- 0.3 % to 70.5 % on the
ceiling it sized -- and a pooled share over a heterogeneous population is
compatible with almost any per-file picture.

Rows that never reached the lazy-SMT loop report NOTHING about it, not zero, and
are counted separately. Folding them in would put rows of silence into the
denominator and make every share smaller for a reason that has nothing to do
with re-solving.

Usage: sizing-summary.py <sizing.tsv>...
"""

import statistics
import sys


def num(row, key):
    """One field as an int, or None when the row is silent about it.

    An empty string is NOT zero here. A file that never entered the lazy-SMT
    loop prints no `; lazy-smt` line at all, and reading that as `0 ms of
    re-solving' would be a measurement of the loop on a file the loop never ran
    on.
    """
    v = row.get(key, "")
    if v is None or v.strip() == "" or v.strip() == "n/a":
        return None
    try:
        return int(v)
    except ValueError:
        return None


def main(paths):
    rows = []
    header = None
    for path in paths:
        with open(path) as handle:
            lines = handle.read().splitlines()
        if not lines:
            continue
        cols = lines[0].split("\t")
        if header is None:
            header = cols
        elif header != cols:
            sys.exit(f"ABORT: {path} has a different header; refusing to pool")
        for line in lines[1:]:
            parts = line.split("\t")
            if len(parts) != len(cols):
                continue
            rows.append(dict(zip(cols, parts)))

    total = len(rows)
    decided = [r for r in rows if r["verdict"] in ("sat", "unsat")]
    reached = [r for r in rows if num(r, "cube_decisions") is not None]
    resolving = [r for r in reached if (num(r, "cold_builds") or 0) > 0]

    print(f"population: {total} rows   decided {len(decided)}   undecided {total - len(decided)}")
    print(f"  reached the lazy-SMT loop (a `; lazy-smt` line):      {len(reached)}")
    print(f"  of those, built >=1 from-scratch tableau:             {len(resolving)}")
    print(f"  never reached it (silent, NOT zero):                  {total - len(reached)}")
    print()

    if not resolving:
        print("NO ROW RE-SOLVES. The ceiling on a warm basis is 0 on this population.")
        return

    def shares(rs, num_keys):
        out = []
        for r in rs:
            tot = num(r, "total_ms")
            if not tot:
                continue
            acc = 0
            for k in num_keys:
                acc += num(r, k) or 0
            out.append(100.0 * acc / tot)
        return out

    build = shares(resolving, ["cold_build_ms"])
    cold = shares(resolving, ["cold_ms"])
    cold_collect = shares(resolving, ["cold_ms", "cube_collect_ms"])

    print(f"share of wall clock, over the {len(resolving)} rows that re-solve")
    print("  quantity                              median     min      max")
    for label, xs in (
        ("tableau CONSTRUCTION only", build),
        ("the whole from-scratch call (CEILING)", cold),
        ("  ... plus per-cube linearization", cold_collect),
    ):
        if xs:
            print(
                f"  {label:<38}{statistics.median(xs):6.2f} % {min(xs):6.2f} % {max(xs):6.2f} %"
            )
    print()

    # THE LEVER'S OWN CEILING, over the right population.
    #
    # The three shares above price the FROM-SCRATCH SIMPLEX. The ADR-2125
    # decider does not only replace that: because it holds the atom translation
    # for the whole entry, a cube it answers pays no per-cube LINEARIZATION
    # either -- `lra::decide_within`, and with it the `Collector` rebuild the
    # `cube_collect_ms` clock measures, is never entered.
    #
    # So the quantity the lever competes for is `cube_collect_ms +
    # cube_simplex_ms` over EVERY row that reaches the loop, not just the rows
    # that re-solve: a row whose cubes are all decided by Fourier-Motzkin pays
    # the linearization and no simplex, and the lever removes that too.
    #
    # The complement is printed beside it and is the honest ceiling on the
    # ceiling: whatever share the propositional half (`skeleton_ms`) holds is
    # work no theory-side change of any kind can touch.
    lever = []
    for r in reached:
        tot = num(r, "total_ms")
        if not tot:
            continue
        theory = (num(r, "cube_collect_ms") or 0) + (num(r, "cube_simplex_ms") or 0)
        lever.append(100.0 * theory / tot)
    if lever:
        print(
            f"THE LEVER'S CEILING (cube_collect_ms + cube_simplex_ms), over all "
            f"{len(lever)} rows that reach the loop"
        )
        print(
            f"  median {statistics.median(lever):6.2f} %   min {min(lever):6.2f} %   "
            f"max {max(lever):6.2f} %"
        )
        over10 = sum(1 for x in lever if x >= 10.0)
        over25 = sum(1 for x in lever if x >= 25.0)
        print(f"  rows at or above 10 %: {over10} of {len(lever)}    at or above 25 %: {over25}")
        # A median near zero over every row that reaches the loop is REAL and is
        # not the whole picture: a row the ladder already decides in 107 ms spends
        # no measurable time in this loop, and a lever cannot win a file that is
        # already won. The addressable half is the UNDECIDED rows, and it is
        # reported separately rather than pooled -- exactly the split ADR-2122
        # made when it refused to size a ceiling over 93 rows of which 70 were
        # silent.
        und = []
        for r in reached:
            tot = num(r, "total_ms")
            if not tot or r["verdict"] in ("sat", "unsat"):
                continue
            theory = (num(r, "cube_collect_ms") or 0) + (num(r, "cube_simplex_ms") or 0)
            und.append(100.0 * theory / tot)
        if und:
            print(
                f"  restricted to the {len(und)} UNDECIDED rows that reach it: "
                f"median {statistics.median(und):6.2f} %   min {min(und):6.2f} %   "
                f"max {max(und):6.2f} %"
            )
        print()

    builds = [num(r, "cold_builds") or 0 for r in resolving]
    pivots = [num(r, "cold_pivots") or 0 for r in resolving]
    rounds = [num(r, "lra_rounds") or 0 for r in resolving]
    flips = [num(r, "cube_flips") or 0 for r in resolving]
    atoms = [num(r, "atoms") or 0 for r in resolving]
    print("counts, median over the same rows")
    print(f"  from-scratch tableaux built        {statistics.median(builds):10.0f}  (max {max(builds)})")
    print(f"  pivots from a pristine basis       {statistics.median(pivots):10.0f}  (max {max(pivots)})")
    print(f"  refinement rounds                  {statistics.median(rounds):10.0f}")
    print(f"  atoms                              {statistics.median(atoms):10.0f}")
    print(f"  cube flips (summed over rounds)    {statistics.median(flips):10.0f}")
    print()

    # The churn ratio is the reason a warm basis is worth trying at all: if each
    # round hands the theory a genuinely different problem there is nothing to
    # warm-start, and if it differs in a handful of bounds the cold re-decision
    # is redundant work rather than search. ADR-2111 measured 1.1-4.2 flips
    # against 265-1,736 atoms and this re-derives it on a different population.
    per_round = []
    for r in resolving:
        rd, fl = num(r, "lra_rounds") or 0, num(r, "cube_flips") or 0
        ent = num(r, "lra_entries") or 0
        denom = rd - ent
        if denom > 0:
            per_round.append(fl / denom)
    if per_round:
        print(
            f"cube churn: median {statistics.median(per_round):.2f} flipped literals per round "
            f"against a median {statistics.median(atoms):.0f} atoms "
            f"({len(per_round)} rows with a predecessor)"
        )

    # The top rows by ceiling, published so the ADR quotes files rather than a
    # summary statistic the spread makes meaningless.
    ranked = sorted(
        (
            (100.0 * (num(r, "cold_ms") or 0) / (num(r, "total_ms") or 1), r)
            for r in resolving
        ),
        reverse=True,
    )
    print()
    print("the ten highest ceilings, by file")
    print(f"  {'share':>7}  {'cold_ms':>8} {'total_ms':>9} {'builds':>7}  file")
    for share, r in ranked[:10]:
        print(
            f"  {share:6.2f} % {num(r, 'cold_ms') or 0:8d} {num(r, 'total_ms') or 0:9d} "
            f"{num(r, 'cold_builds') or 0:7d}  {r['file']}"
        )


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    main(sys.argv[1:])
