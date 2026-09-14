"""ADR-2035 -- the CEGAR round distribution, INCLUDING the rows that decide.

The brief asked for the distribution before any cap, and for what a cap would
cost on files that currently decide. The committed census cannot answer the
second half: `FunctionConsistencyStats` is wrapped into the give-up string only
on the `Unknown` exit, so a file that DECIDES leaves no round count behind at
all. `FCPROBE` (off by default, printed, never acted on) emits one line at every
one of the loop's three exits, so the denominator is the whole population rather
than the unknown half of it.

Reads the probe sweep's raw logs and reports, per exit kind, how many files
reached each `solve_rounds` value.

Usage: round-distribution.py <fcprobe-log>...
"""

import collections
import re
import sys

LINE = re.compile(
    r"FCPROBE exit=(\w+) solve_rounds=(\d+) lemmas_added=(\d+) violated_pairs=(\d+)"
)

rows = []
for path in sys.argv[1:]:
    current = path
    for line in open(path, errors="replace"):
        if line.startswith("##FILE "):
            current = line.split(None, 1)[1].strip()
            continue
        m = LINE.search(line)
        if m:
            rows.append(
                {
                    "file": current,
                    "exit": m.group(1),
                    "rounds": int(m.group(2)),
                    "lemmas": int(m.group(3)),
                    "violated": int(m.group(4)),
                }
            )

print(f"FCPROBE exit records: {len(rows)}")
print(f"distinct files:       {len(set(r['file'] for r in rows))}")
print()

# A file can run the loop more than once (the dispatch ladder re-enters it), so
# the per-FILE quantity that a round cap would act on is the DEEPEST loop the
# file ran, not the first or the last. Counting records instead of files would
# weight a file by how often it was re-entered.
deepest = {}
for r in rows:
    prev = deepest.get(r["file"])
    if prev is None or r["rounds"] > prev["rounds"]:
        deepest[r["file"]] = r

print("=== deepest CEGAR loop per file, by how that loop exited ===")
print(f"{'exit':<10} {'rounds':>7}  files")
tally = collections.Counter((r["exit"], r["rounds"]) for r in deepest.values())
for (exit_kind, rounds), n in sorted(tally.items()):
    print(f"{exit_kind:<10} {rounds:>7}  {n}")
print()

print("=== what a round cap would COST ===")
print("A cap at N truncates every loop that ran more than N rounds, and the")
print("loop's only truncation exit is `Unknown`. So a cap at N costs exactly")
print("the files whose DECIDING exit needed more than N rounds.")
decided = [r for r in deepest.values() if r["exit"] in ("unsat", "replay")]
print(f"files whose deepest loop DECIDED: {len(decided)}")
for cap in (1, 2, 3, 4):
    cost = [r for r in decided if r["rounds"] > cap]
    print(f"  cap={cap}: costs {len(cost)} decided file(s)")
    for r in sorted(cost, key=lambda x: -x["rounds"])[:10]:
        print(f"      rounds={r['rounds']} exit={r['exit']}  {r['file']}")
