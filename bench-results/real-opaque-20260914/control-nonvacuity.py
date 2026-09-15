#!/usr/bin/env python3
"""REAL-OPAQUE R7 -- is the control division NON-VACUOUS?

A control reported at zero is worth nothing until you show it had somewhere to
move. Two questions, and they are different:

  1. **Did it have room?** How many rows were UNDECIDED in the base arm — a
     division already decided end to end cannot move and its zero is empty.
  2. **Does the changed code RUN there?** Which route binds those undecided
     rows, and is it one that executes `lra::decide_within_with_options`?

`QF_LRA` is the control precisely because the answer to (2) is yes and the
abstraction still cannot fire: the division has no uninterpreted real
application and no array, so `Collector::linearize`'s opaque arm is unreachable
while every other line this change touched — the shared column allocator
(`index_of` / `next_var`), `variable_count()` replacing `vars.len()`, and
`simplex_fallback`'s `var_index`-keyed model — runs on every row. It is the
division where the COLUMN-SPACE refactor would show up if it were wrong, which
is the part of this change most likely to be.

Usage: control-nonvacuity.py <tsv> [<tsv> ...]
"""

import sys
from collections import Counter

DECIDED = {"sat", "unsat"}


def main(paths):
    rows = []
    for path in paths:
        with open(path) as fh:
            line = fh.readline()
            while line.startswith("#"):
                line = fh.readline()
            header = line.rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))

    undecided = [r for r in rows if r["off_verdict"] not in DECIDED]
    bound = Counter()
    decided_by = Counter()
    for r in undecided:
        parts = r["off_route"].split("|")
        bound[parts[1] if len(parts) > 1 else "?"] += 1
    for r in rows:
        if r["off_verdict"] in DECIDED:
            decided_by[r["off_route"].split("|")[0]] += 1

    print(f"rows                 : {len(rows)}")
    print(f"UNDECIDED in base    : {len(undecided)}/{len(rows)}   <- the room the zero had")
    print(f"non-ok exit in base  : {sum(1 for r in rows if r['off_exit'] != 'ok')}/{len(rows)}")
    print("\nroute BINDING the undecided rows (base arm):")
    for k, v in bound.most_common():
        print(f"   {v:4d}  {k}")
    print("\nroute that DECIDED the decided rows (base arm):")
    for k, v in decided_by.most_common():
        print(f"   {v:4d}  {k}")

    # The finding, and the exit status depends on it.
    if not undecided:
        print("\nVACUOUS: nothing was undecided, so the zero says nothing.")
        return 1
    lra_bound = sum(v for k, v in bound.items() if "lra" in k or "dl" in k or "arith" in k)
    print(
        f"\nNON-VACUOUS: {len(undecided)} rows were undecided in the base arm and did not "
        f"move;\n  {lra_bound} of them are bound by an arithmetic route."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
