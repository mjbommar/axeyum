#!/usr/bin/env python3
"""Is the control's "0 losses" vacuous?

A control population that never reaches the cap being raised cannot lose, and
its zero would mean nothing. So this asks the only question that makes the zero
worth quoting: **on how many control files does the route these caps govern
actually run, and on how many does the cap actually fire?**

Two readings, both printed:
  * EXPOSED -- the file's route trail names an `ufbv_online` route
    (`*ufbv-online*`, `*aufbv-online*`, `*abv-online*`), so `admit_input` and
    `build_theory_atoms` ran on it.
  * FIRED -- some arm's give-up text names one of the two caps, so the file was
    actually turned away by the value under test.
"""
import collections
import glob
import re
import sys

outdir = sys.argv[1]
rows = []
for p in glob.glob(f"{outdir}/shard*.tsv"):
    with open(p) as fh:
        h = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            q = line.rstrip("\n").split("\t")
            if len(q) == len(h):
                rows.append(dict(zip(h, q)))
by = collections.defaultdict(dict)
for r in rows:
    by[r["file"]][r["arm"]] = r
arms = sorted({r["arm"] for r in rows})
complete = [f for f, d in by.items() if len(d) == len(arms)]
ONLINE = re.compile(r"(ufbv-online|aufbv-online|abv-online)")
CAPS = re.compile(r"(semantic atoms|dynamic theory atoms|DAG nodes)")


def div(f):
    m = re.search(r"(QF_[A-Z0-9]+)/", f)
    return m.group(1) if m else "?"


exposed = collections.Counter()
fired = collections.Counter()
total = collections.Counter()
for f in complete:
    d = by[f]
    total[div(f)] += 1
    if any(ONLINE.search(f"{r['decided_by']} {r['bound_by']}") for r in d.values()):
        exposed[div(f)] += 1
    if any(CAPS.search(r["giveup"]) for r in d.values()):
        fired[div(f)] += 1
print(f"complete files: {len(complete)} (arms {arms})")
print(f"{'division':<12} {'files':>6} {'route ran':>10} {'cap fired':>10}")
for k in sorted(total):
    print(f"{k:<12} {total[k]:>6} {exposed[k]:>10} {fired[k]:>10}")
print(f"{'TOTAL':<12} {sum(total.values()):>6} {sum(exposed.values()):>10} {sum(fired.values()):>10}")
if sum(exposed.values()) == 0:
    print("\nVACUOUS: the route these caps govern never ran on this population.")
elif sum(fired.values()) == 0:
    print(
        "\nThe route RAN but neither cap turned a file away. That does NOT mean a "
        "raise cannot change this population -- the other loss mechanism is a file "
        "the raise ADMITS, which then spends budget the later routes needed. Read "
        "the loss column; do not infer safety from this line."
    )
else:
    print("\nThe caps FIRE on this population, so a loss was possible and did not occur.")
