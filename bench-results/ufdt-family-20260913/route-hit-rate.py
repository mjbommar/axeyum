"""How often the route this lane changes actually RUNS on the measured population.

Three lanes this week shipped controls structurally unable to exercise the route
they changed (`ufbv_online` on 0 of 400 files; `q:egraph` on 0 of 200 for three
QUANTIFIER-FREE divisions). A null result from a population the change cannot
reach is not a null result -- it is a measurement of nothing, and it reads
identically.

So the hit rate is derived here from the census's own `qtrace` column, which
records `[qtrace] egraph +<s> <note>` at the rung's exit on every file that
entered it. Printed beside the decision rate, because "the rung ran" and "the
rung decided" are different numbers and only the pair says whether a budget
handed to it was earning anything.
"""

import collections
import csv
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
# A `qtrace` cell can exceed csv's 128 KiB default field limit -- one AUFLIA
# file emits a rung trail that long.
csv.field_size_limit(1 << 24)


def main() -> int:
    seen = 0
    # AUFLIA is the CONTROL, and it is here for the same reason its A/B is:
    # a null from a population the changed route never enters is not a null.
    for div, name in (("UFNIA", "UFNIA.tsv"), ("UFLIA", "UFLIA.tsv"),
                      ("AUFLIA (control)", "AUFLIA.control.tsv")):
        p = HERE / "census" / name
        if not p.exists():
            print(f"== {div}: DID NOT RUN")
            continue
        seen += 1
        rows = list(csv.DictReader(open(p), delimiter="\t"))
        entered = [r for r in rows if "egraph@" in r["qtrace"]]
        decided_here = [r for r in rows if r["decided_by"] == "q:egraph"]
        bound_here = [r for r in rows if r["bound_by"] == "q:egraph"]
        notes = collections.Counter(
            seg.split(":", 1)[1]
            for r in entered
            for seg in r["qtrace"].split(";")
            if seg.startswith("egraph@")
        )
        print(f"== {div}  n={len(rows)}")
        print(f"   q:egraph ENTERED on   {len(entered):3d} / {len(rows)}"
              f"   ({len(entered) / len(rows):.0%})")
        print(f"   q:egraph DECIDED      {len(decided_here):3d} / {len(rows)}")
        print(f"   q:egraph BOUND the run{len(bound_here):4d} / {len(rows)}"
              f"   (it held the largest attributed segment)")
        print(f"   its own exit notes:   {dict(notes.most_common())}")
        if not entered:
            print("   !! the route never ran here: this population CANNOT control the change")
    return 0 if seen else 1


if __name__ == "__main__":
    sys.exit(main())
