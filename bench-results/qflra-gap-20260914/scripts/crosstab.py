#!/usr/bin/env python3
"""Cross-tabulate the census bucket against the online-LRA admission probe.

The question this answers: of the rows the OFFLINE dense engine binds, how many
were REFUSED by the online engine's admission screen (a bound we set, and the
one a memory limit moves) versus tried by it and failed (a capability we lack)?
Those two have completely different follow-ups and one give-up string covers
both.
"""
import sys
from collections import Counter

rows = []
with open(sys.argv[1]) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

und = [r for r in rows if r["bucket"] != "DECIDED"]
print(f"undecided={len(und)}\n")

short = {
    "ABORT/oom": "ABORT (dense matrix over the unseen 8 GiB)",
    "Timeout/ResourceLimit": "CLOCK in the offline dense engine",
    "Timeout/Incomplete": "online LRA model did not replay",
    "Watchdog/-": "watchdog, worker never returned",
    "Incomplete/-": "int<->real coercion relaxation",
    "SILENT": "silent unknown",
    "Timeout/Timeout": "online LRA driver timeout",
}
c = Counter((short.get(r["bucket"], r["bucket"]), r["online_probe"]) for r in und)
print(f"{'n':>4}  {'bucket':<44} online_probe")
for (b, p), n in c.most_common():
    print(f"{n:>4}  {b:<44} {p}")

print("\n-- the admission question, over the 74 offline-dense rows --")
off = [r for r in und if r["bucket"] in ("ABORT/oom", "Timeout/ResourceLimit")]
print(f"  offline-dense rows: {len(off)}")
print(f"  online_probe: {Counter(r['online_probe'] for r in off).most_common()}")
print("  NONE = the run died before the theory reported anything at all "
      "(no `; lazy-smt` line), which is every abort.")
