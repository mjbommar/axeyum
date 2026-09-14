#!/usr/bin/env python3
"""Did the idle-host re-take change the 'nobody decides it' verdict?

The first reference pass ran six concurrent shards on s4.  Load can only make a
deadline-bounded solver decide FEWER files, so that pass understates
addressability, and the rows it understates are exactly the ones it called
"decided by nobody".  Re-taken on idle hosts, one pinned pair each.

A row that decides here and did not there was a FALSE 'nobody' and moves into
the addressable set.
"""
import sys
from collections import Counter

DEC = ("sat", "unsat")
rows = []
for p in sys.argv[1:]:
    with open(p) as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

print(f"re-checked on idle hosts: {len(rows)} rows "
      f"(the 'decided by nobody' set from the loaded pass)")
now = [r for r in rows if r["z3"] in DEC or r["cvc5"] in DEC]
print(f"\nNOW DECIDED by a reference: {len(now)} of {len(rows)}")
for r in now:
    print(f"  z3={r['z3']:>7} cvc5={r['cvc5']:>7} status={r['status']:>7}  "
          f"{r['file'].split('non-incremental/')[-1]}")
print(f"\nstill decided by nobody: {len(rows) - len(now)}")
print(f"z3:   {Counter(r['z3'] for r in rows).most_common()}")
print(f"cvc5: {Counter(r['cvc5'] for r in rows).most_common()}")

comp = dis = 0
for r in rows:
    for k in ("z3", "cvc5"):
        if r[k] in DEC and r["status"] in DEC:
            comp += 1
            if r[k] != r["status"]:
                dis += 1
                print(f"  REFERENCE DISAGREEMENT {k}={r[k]} status={r['status']} {r['file']}")
print(f"\nreference vs declared :status -- comparable={comp} disagreements={dis}")
