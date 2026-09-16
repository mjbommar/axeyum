#!/usr/bin/env python3
"""Split the census target population by whether the query was ULTIMATELY
decided.

A census block fires whenever the online CDCL(T) route produced a candidate
model and it failed. That can happen on a file the ladder then decides by
another route -- in which case the wall was hit but nothing was lost. The
histogram that matters is over files where the wall is the FINAL answer.

Usage: refine.py <per-file.tsv>
"""

import collections
import csv
import sys

rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
tgt = [r for r in rows if r["last_arm"] in ("no-model", "no-replay")]

lost = [r for r in tgt if r["verdict"] in ("unknown", "none")]
survived = [r for r in tgt if r["verdict"] in ("sat", "unsat")]


def bucket(r):
    if r["last_arm"] == "no-model":
        site = r["model_decline"].split("|")[0] if r["model_decline"] else "?"
        gone = "deadline=true" in r["model_decline"]
        return f"NO-MODEL:{site}:" + ("clock-gone" if gone else "clock-left")
    return r["construct"] or "no-replay:(no-offending-atom)"


print(f"census blocks ended in a failure on: {len(tgt)} files")
print(f"  of which the query was STILL DECIDED by a later route: {len(survived)}")
for r in sorted(survived, key=lambda r: r["file"]):
    print(f"      {r['verdict']:6s} {bucket(r):46s} {r['file']}")
print(f"  of which the query ended UNDECIDED (the wall is the answer): {len(lost)}")
print()
print("HISTOGRAM over the UNDECIDED target population:")
h = collections.Counter(bucket(r) for r in lost)
with open("histogram.tsv", "w") as fh:
    fh.write("bucket\tfiles\n")
    for k, v in sorted(h.items(), key=lambda kv: (-kv[1], kv[0])):
        fh.write(f"{k}\t{v}\n")
for k, v in sorted(h.items(), key=lambda kv: (-kv[1], kv[0])):
    print(f"  {v:4d}  {k}")
print()
print("  exit statuses in that population:")
for k, v in sorted(collections.Counter(r["exit"] for r in lost).items()):
    print(f"  {v:4d}  exit={k}")
print()
print("  unsupported atoms across that population:",
      sum(int(r["unsupported"] or 0) for r in lost))
print("  files with any unsupported atom:",
      sum(1 for r in lost if int(r["unsupported"] or 0) > 0))
print()
print("  tableau present/absent:")
for k, v in sorted(collections.Counter(
        "ABSENT" if r["simplex_rows"] in ("n/a", "") else "present" for r in lost
).items()):
    print(f"  {v:4d}  tableau {k}")
print()
print("DISEQUALITY bucket, per file (the only construct):")
print("file\teq_atoms\teq_asserted_false\tassertions\tassert_false\tverdict")
for r in sorted(lost, key=lambda r: r["file"]):
    if bucket(r).startswith("disequality"):
        print(f"{r['file']}\t{r['equality']}\t{r['eq_asserted_false']}\t"
              f"{r['assertions']}\t{r['assert_false']}\t{r['verdict']}")
