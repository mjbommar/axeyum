"""Split the pre-SAT skeleton boundary population by HOW the query arrived there.

[ADR-2030] split by `lemmas_added >= 100` (a THRESHOLD) and reported 10 flooded
/ 12 unflooded OBSERVATIONS.  A threshold is the wrong instrument: it cannot
distinguish "the flood pushed this over the boundary" from "this was already
over the boundary and happens to have emitted lemmas".

The CEGAR loop's own statistics make the split MECHANICAL.  The inner solve for
each round is `check_with_incremental_arith`, which reaches the boundary at
`IncrementalArithDpll::solve` (`dpll_lia.rs:1158`, stage "declining before the
first SAT round").  So:

  * `sat_candidates >= 1`  =>  some round's solve was ADMITTED past the boundary
    and returned a model.  The refusal therefore happened on a LATER round, on a
    skeleton grown by the lemma batch.  The flood is on the causal path.
    -> population GROWN.

  * `sat_candidates == 0` and `solve_rounds == 1` and `lemmas_added == 0`
    =>  the FIRST solve was refused.  The instantiated conjunction crossed the
    boundary before a single lemma existed.  No per-round lemma cap, and no
    round cap, can move it.
    -> population BORN-OVER.

Anything else is reported as UNCLASSIFIED rather than forced into a bucket.

Usage: split-populations.py <repo-root>
"""

import csv
import glob
import re
import sys
import collections

BASE = sys.argv[1] if len(sys.argv) > 1 else "."

# The record separator is `;QPROBE`, not a bare `;` -- a `why=` detail contains
# `;` (the boundary reason ends `...); <stage>`).  [ADR-2020] truncated its own
# largest bucket by splitting on the bare character.
BOUNDARY = "pre-SAT_skeleton_exceeds_the_joint_resource_boundary"
CEGAR = re.compile(r"CEGAR_inconclusive_\(([^)]*)\)")
KV = re.compile(r"(\w+)=(-?\d+)")
SIZE = re.compile(BOUNDARY + r"_\(atoms=(\d+),_cnf_vars=(\d+)")
STAGE = re.compile(r"_(declining_before_the_[a-zA-Z_()]+)")

rows = []
for path in sorted(
    glob.glob(BASE + "/bench-results/round-head-20260914/census/FAMILY.shard0*.tsv")
):
    rows += list(csv.DictReader(open(path), delimiter="\t"))

obs = []
for row in rows:
    for col, val in row.items():
        if not isinstance(val, str) or BOUNDARY not in val:
            continue
        for rec in val.split(";QPROBE"):
            if BOUNDARY not in rec:
                continue
            size = SIZE.search(rec)
            stage = STAGE.search(rec[rec.index(BOUNDARY) :])
            cegar = CEGAR.search(rec)
            # `\w` matches `_`, and the field separator in a censused `why=` is
            # `,_`, so every key but the first arrives as `_solve_rounds`.  A
            # silent miss here reports every field as -1 and the whole split as
            # UNCLASSIFIED -- which is what this script did on its first run.
            stats = (
                {k.lstrip("_"): int(v) for k, v in KV.findall(cegar.group(1))}
                if cegar
                else {}
            )
            obs.append(
                {
                    "file": row["file"],
                    "col": col,
                    "atoms": int(size.group(1)) if size else -1,
                    "cnf_vars": int(size.group(2)) if size else -1,
                    "stage": stage.group(1).replace("_", " ") if stage else "UNPARSED",
                    "cegar": bool(cegar),
                    **{
                        k: stats.get(k, -1)
                        for k in (
                            "solve_rounds",
                            "sat_candidates",
                            "lemmas_added",
                            "equal_arg_pairs",
                            "violated_pairs",
                        )
                    },
                }
            )


def classify(o):
    if not o["cegar"]:
        return "NO-CEGAR"
    if o["sat_candidates"] >= 1:
        return "GROWN"
    if o["sat_candidates"] == 0 and o["solve_rounds"] == 1 and o["lemmas_added"] == 0:
        return "BORN-OVER"
    return "UNCLASSIFIED"


for o in obs:
    o["pop"] = classify(o)

print(f"boundary observations: {len(obs)}")
print(f"distinct files:        {len(set(o['file'] for o in obs))}")
print()
print("=== which of the TWO code sites emitted the boundary reason ===")
print("(one census label, two sites, DIFFERENT rescue wiring -- see the ADR)")
for stage, n in collections.Counter(o["stage"] for o in obs).most_common():
    print(f"  {n:>3}  {stage}")
print()
print("=== population split (mechanical, no threshold) ===")
for pop, n in collections.Counter(o["pop"] for o in obs).most_common():
    files = len(set(o["file"] for o in obs if o["pop"] == pop))
    print(f"  {n:>3} obs / {files:>3} files   {pop}")
print()
print("=== ADR-2030's threshold split, for comparison, on the SAME rows ===")
for label, sel in (
    ("lemmas_added >= 100 (its FLOODED)", lambda x: x["lemmas_added"] >= 100),
    ("lemmas_added == 0", lambda x: x["lemmas_added"] == 0),
    ("0 < lemmas_added < 100", lambda x: 0 < x["lemmas_added"] < 100),
):
    sub = [o for o in obs if sel(o)]
    byp = collections.Counter(o["pop"] for o in sub)
    print(f"  {len(sub):>3}  {label:<34} -> {dict(byp)}")
print()
print("=== per observation ===")
print(
    f"{'pop':<10} {'atoms':>7} {'cnfv':>7} {'rnds':>4} {'satc':>4} "
    f"{'lemmas':>7} {'eqarg':>7} {'viol':>5}  file"
)
for o in sorted(obs, key=lambda x: (x["pop"], -x["atoms"])):
    print(
        f"{o['pop']:<10} {o['atoms']:>7} {o['cnf_vars']:>7} {o['solve_rounds']:>4} "
        f"{o['sat_candidates']:>4} {o['lemmas_added']:>7} {o['equal_arg_pairs']:>7} "
        f"{o['violated_pairs']:>5}  {o['file']}"
    )
