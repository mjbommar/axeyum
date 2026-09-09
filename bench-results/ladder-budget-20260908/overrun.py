import sys
import os

BUDGET_MS = 24000


def load(path):
    rows = {}
    for line in open(path, encoding="utf-8"):
        if line.startswith("#") or line.startswith("file\t"):
            continue
        parts = line.rstrip("\n").split("\t")
        if len(parts) < 3:
            continue
        rows[parts[0]] = (int(parts[1]), parts[2], parts[3] if len(parts) > 3 else "")
    return rows


off_a = load(sys.argv[1])
off_b = load(sys.argv[2])
on = load(sys.argv[3])

print("Files DECIDED past the 24 s budget under `off`, and what `on` does with them:")
print(f"{'file':58s} {'off-a':>8s} {'off-b':>8s} {'on':>8s}  verdict")
n_fixed = 0
for f in sorted(off_a):
    wa, va, _ = off_a[f]
    wb, _, _ = off_b.get(f, (0, "", ""))
    wn, vn, rn = on.get(f, (0, "", ""))
    if va in ("sat", "unsat") and wa > BUDGET_MS:
        mark = ""
        if wn <= BUDGET_MS and vn == va:
            mark = "  <- now inside the budget"
            n_fixed += 1
        print(f"{os.path.basename(f):58s} {wa:8d} {wb:8d} {wn:8d}  {va}{mark}")
print(f"\n{n_fixed} file(s) moved from decided-past-the-budget to decided-inside-it.")

print("\nWall-clock movers over 1 s (off-a vs on), the 10 largest:")
movers = []
for f in off_a:
    if f in on:
        movers.append((on[f][0] - off_a[f][0], f))
movers.sort()
for delta, f in movers[:10]:
    print(f"  {delta:+7d} ms  {os.path.basename(f):55s} {off_a[f][1]} -> {on[f][1]}")
print("  ...")
for delta, f in movers[-5:]:
    print(f"  {delta:+7d} ms  {os.path.basename(f):55s} {off_a[f][1]} -> {on[f][1]}")

ca = sum(1 for f in off_a if off_a[f][0] > BUDGET_MS)
cb = sum(1 for f in off_b if off_b[f][0] > BUDGET_MS)
cn = sum(1 for f in on if on[f][0] > BUDGET_MS)
print(f"\nfiles whose whole run exceeded the 24 s budget: off-a {ca}, off-b {cb}, on {cn}")
