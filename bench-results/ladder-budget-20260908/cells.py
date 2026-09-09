import os
import re
import sys

CAP = 4_000_000
path = sys.argv[1]
rows = []
for line in open(path, encoding="utf-8"):
    if line.startswith("#") or line.startswith("file\t"):
        continue
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 4:
        parts += [""] * (4 - len(parts))
    f, wall, verdict, cells = parts[0], int(parts[1]), parts[2], parts[3]
    calls = []
    for chunk in cells.split("|"):
        m = re.search(r"cells=(\d+) rows=(\d+) nvars=(\d+) outcome=(\S+) over_cap=(\w+)", chunk)
        if m:
            calls.append(
                (int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5) == "true")
            )
    rows.append((f, wall, verdict, calls))

with_calls = [r for r in rows if r[3]]
over = [r for r in with_calls if any(c[4] for c in r[3])]
print(f"files in sweep: {len(rows)}")
print(f"files reaching lra::simplex_fallback at all: {len(with_calls)}")
print(f"...of those, files where SOME call exceeds MAX_TABLEAU_CELLS ({CAP:,}): {len(over)}")
print()
print(f"{'file':52s} {'verdict':8s} {'wall':>7s} {'max cells':>14s} {'outcomes of the over-cap calls'}")
for f, wall, verdict, calls in sorted(over, key=lambda r: -max(c[0] for c in r[3])):
    big = [c for c in calls if c[4]]
    outs = ",".join(sorted({c[3] for c in big}))
    print(
        f"{os.path.basename(f)[:52]:52s} {verdict:8s} {wall:7d} "
        f"{max(c[0] for c in big):14,d} {outs} (n={len(big)} of {len(calls)})"
    )

print()
decided_over = [r for r in over if r[2] in ("sat", "unsat")]
print(f"over-cap files whose FINAL verdict is a decision: {len(decided_over)}")
for f, wall, verdict, calls in decided_over:
    big = [c for c in calls if c[4]]
    print(f"   {verdict:6s} {os.path.basename(f)}  outcomes={sorted({c[3] for c in big})}")

print()
producing = [
    (f, verdict, c)
    for f, wall, verdict, calls in over
    for c in calls
    if c[4] and c[3] in ("feasible", "infeasible")
]
print(
    f"over-cap CALLS that produced a candidate decision (feasible/infeasible): "
    f"{len(producing)}"
)
for f, verdict, c in producing:
    print(f"   cells={c[0]:,} outcome={c[3]} file_verdict={verdict} {os.path.basename(f)}")

print()
under = [
    c
    for _, _, _, calls in with_calls
    for c in calls
    if not c[4] and c[3] in ("feasible", "infeasible")
]
print(f"under-cap calls that produced a candidate decision: {len(under)}")
allcalls = [c for _, _, _, calls in with_calls for c in calls]
print(f"total fallback calls: {len(allcalls)}; largest tableau: {max(c[0] for c in allcalls):,} cells")
