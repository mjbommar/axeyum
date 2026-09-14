"""ADR-2035 GATE 0 -- summarize the ordered probe.

Answers, per arm and per instrument:

  * how many files cross the pre-SAT skeleton boundary AT ALL;
  * how many cross at `site=preflight` (where the rescue is already SHIPPED)
    versus `site=solve` (where it is not) -- the distinction a census keyed on
    the give-up sentence cannot make, because that sentence names only the LAST
    site to refuse;
  * whether the rescue, when it ran, ever DECIDED.

A file that crosses at BOTH sites is reported separately and by name: for such a
file the "missing wiring" framing is wrong, and [ADR-2030] made exactly this
correction to [ADR-2020]'s `combined.rs:86` reading.

Usage: probe-summarize.py <label> <tsv>...
"""

import csv
import sys

label = sys.argv[1]
rows = []
for path in sys.argv[2:]:
    rows += list(csv.DictReader(open(path), delimiter="\t"))


def n(row, key):
    return int(row[key])


crossed = [r for r in rows if n(r, "preflight") + n(r, "solve") > 0]
only_solve = [r for r in crossed if n(r, "preflight") == 0]
only_pref = [r for r in crossed if n(r, "solve") == 0]
both = [r for r in crossed if n(r, "preflight") > 0 and n(r, "solve") > 0]
ran = [r for r in rows if n(r, "rescue_ran") > 0]
decided = [r for r in rows if n(r, "out_sat") + n(r, "out_unsat") > 0]

print(f"=== {label} ===")
print(f"files                                {len(rows)}")
print(f"crossed the boundary at all          {len(crossed)}")
print(f"  ...only at site=solve  (NO rescue) {len(only_solve)}")
print(f"  ...only at site=preflight (rescue) {len(only_pref)}")
print(f"  ...at BOTH sites                   {len(both)}")
print(f"total site=solve crossings           {sum(n(r, 'solve') for r in rows)}")
print(f"total site=preflight crossings       {sum(n(r, 'preflight') for r in rows)}")
print(f"files where the rescue RAN           {len(ran)}")
print(f"files where the rescue DECIDED       {len(decided)}")
print(
    f"  rescue outcomes: sat={sum(n(r, 'out_sat') for r in rows)} "
    f"unsat={sum(n(r, 'out_unsat') for r in rows)} "
    f"declined={sum(n(r, 'out_declined') for r in rows)} "
    f"unknown={sum(n(r, 'out_unknown') for r in rows)}"
)
verdicts = {}
for r in rows:
    verdicts[r["verdict"]] = verdicts.get(r["verdict"], 0) + 1
print(f"verdicts                             {dict(sorted(verdicts.items()))}")
if both:
    print("\nfiles crossing at BOTH sites (the 'missing wiring' framing is wrong for these):")
    for r in both:
        print(f"  preflight={r['preflight']:>5} solve={r['solve']:>6}  {r['file']}")
if decided:
    print("\nfiles where the rescue DECIDED:")
    for r in decided:
        print(
            f"  sat={r['out_sat']} unsat={r['out_unsat']} verdict={r['verdict']} "
            f"ms={r['ms']}  {r['file']}"
        )
print("\nper file (crossings | rescue):")
print(f"{'preflight':>9} {'solve':>7} {'ran':>5} {'verdict':>8} {'ms':>7}  file")
for r in sorted(rows, key=lambda x: -(n(x, "solve") + n(x, "preflight"))):
    print(
        f"{r['preflight']:>9} {r['solve']:>7} {r['rescue_ran']:>5} "
        f"{r['verdict']:>8} {r['ms']:>7}  {r['file']}"
    )
