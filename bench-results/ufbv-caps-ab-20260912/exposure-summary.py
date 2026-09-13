#!/usr/bin/env python3
"""Summarize the exposure probe, and require its own positive control.

A count of "the route ran on N files" is only worth quoting if the probe can
also say NO. So this refuses to report unless the population contains at least
one `yes` and one `no`: an all-`yes` or all-`no` answer from a detector nobody
has seen discriminate is indistinguishable from a broken detector.
"""
import collections
import glob
import re
import sys

rows = []
for p in glob.glob(f"{sys.argv[1]}/shard*.tsv"):
    with open(p) as fh:
        h = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            q = line.rstrip("\n").split("\t")
            if len(q) == len(h):
                rows.append(dict(zip(h, q)))
if not rows:
    print("ABORT: no rows")
    sys.exit(2)


def div(f):
    m = re.search(r"(QF_[A-Z0-9]+)/", f)
    return m.group(1) if m else "?"


tot = collections.Counter()
on = collections.Counter()
cap = collections.Counter()
for r in rows:
    d = div(r["file"])
    tot[d] += 1
    on[d] += r["online_route_in_trail"] == "yes"
    cap[d] += r["cap_text_anywhere"] == "yes"
yes, no = sum(on.values()), len(rows) - sum(on.values())
print(f"rows {len(rows)}")
print(f"{'division':<12} {'files':>6} {'ufbv_online ran':>16} {'a cap fired':>12}")
for k in sorted(tot):
    print(f"{k:<12} {tot[k]:>6} {on[k]:>16} {cap[k]:>12}")
print(f"{'TOTAL':<12} {len(rows):>6} {yes:>16} {sum(cap.values()):>12}")
if yes == 0 or no == 0:
    print(
        f"\nABORT: the probe answered the same way on every file "
        f"({yes} yes / {no} no). It has not been shown to discriminate on this "
        "population, so neither answer is evidence."
    )
    sys.exit(2)
print(
    f"\nThe probe discriminates on this population ({yes} yes / {no} no), so both "
    "readings are evidence."
)
