"""ADR-2035 -- does the censused target population exist on the SHIPPED path?

The 22 boundary observations everything since [ADR-2015] has been mining live in
`r1_lines`, i.e. inside the HELD-SET REPLAY probe, which re-runs a discarded
ground set on its own fresh 10 s budget. The A/B that scores any lever is run on
the SHIPPED 24 s path. If the two populations differ, a lever is being measured
where its target may not be -- which would be a standing explanation for
[ADR-2020]'s 0-of-129 and [ADR-2030]'s 1-of-129 as much as for anything here.

This cross-references the ordered probe's shipped-path crossing counts against
the censused target list and reports the overlap. It does NOT assume the answer:
both "the target is present" and "the target is absent" are reported with their
counts, and the non-target files that DO cross are reported too, because a lever
aimed at 22 files that fires on a different set is a different lever.

Usage: target-reachability.py <target-list> <probe-tsv>...
"""

import csv
import sys

targets = {l.strip() for l in open(sys.argv[1]) if l.strip()}
rows = []
for path in sys.argv[2:]:
    rows += list(csv.DictReader(open(path), delimiter="\t"))

seen = {r["file"]: r for r in rows}
crossed = {f for f, r in seen.items() if int(r["solve"]) + int(r["preflight"]) > 0}

in_probe = targets & set(seen)
print(f"censused target files                       {len(targets)}")
print(f"  ...present in this probe sweep            {len(in_probe)}")
print(f"  ...that CROSS on the shipped path         {len(targets & crossed)}")
print(f"  ...present but NEVER cross                {len(in_probe - crossed)}")
print(f"files crossing that are NOT in the target   {len(crossed - targets)}")
print(f"total files crossing                        {len(crossed)}")
print()
missing = sorted(in_probe - crossed)
if missing:
    print("censused targets that DO NOT cross the boundary on the shipped path:")
    for f in missing:
        print(f"  verdict={seen[f]['verdict']:<8} ms={seen[f]['ms']:>6}  {f}")
extra = sorted(crossed - targets)
if extra:
    print("\nfiles crossing that the census never named:")
    for f in extra:
        r = seen[f]
        print(
            f"  solve={r['solve']:>4} preflight={r['preflight']:>3} "
            f"verdict={r['verdict']:<8}  {f}"
        )
