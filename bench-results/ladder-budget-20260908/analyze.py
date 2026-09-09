import sys
import os


def load(path):
    rows = {}
    for line in open(path, encoding="utf-8"):
        if line.startswith("#") or line.startswith("file\t"):
            continue
        parts = line.rstrip("\n").split("\t")
        if len(parts) < 3:
            continue
        f, wall, verdict = parts[0], int(parts[1]), parts[2]
        route = parts[3] if len(parts) > 3 else ""
        rows[f] = (wall, verdict, route)
    return rows


def decided(rows):
    return {f for f, (_, v, _) in rows.items() if v in ("sat", "unsat")}


arms = {}
for path in sys.argv[1:]:
    arms[os.path.basename(path).split("-QF")[0]] = load(path)

for name, rows in arms.items():
    d = decided(rows)
    sat = sum(1 for f, (_, v, _) in rows.items() if v == "sat")
    uns = sum(1 for f, (_, v, _) in rows.items() if v == "unsat")
    unk = len(rows) - len(d)
    tot = sum(w for w, _, _ in rows.values())
    print(f"{name:8s} n={len(rows)} decided={len(d)} sat={sat} unsat={uns} unknown={unk} wall={tot/1000:.0f}s")

names = list(arms)
for i, a in enumerate(names):
    for b in names[i + 1:]:
        da, db = decided(arms[a]), decided(arms[b])
        gained = sorted(db - da)
        lost = sorted(da - db)
        disagree = [
            f
            for f in arms[a]
            if f in arms[b]
            and arms[a][f][1] in ("sat", "unsat")
            and arms[b][f][1] in ("sat", "unsat")
            and arms[a][f][1] != arms[b][f][1]
        ]
        print(f"\n== {a} -> {b}: +{len(gained)} / -{len(lost)}, disagreements={len(disagree)}")
        for f in gained:
            print(f"   GAIN {os.path.basename(f):55s} {arms[a][f][1]}({arms[a][f][0]}ms) -> {arms[b][f][1]}({arms[b][f][0]}ms)")
        for f in lost:
            print(f"   LOSS {os.path.basename(f):55s} {arms[a][f][1]}({arms[a][f][0]}ms) -> {arms[b][f][1]}({arms[b][f][0]}ms)")
        for f in disagree:
            print(f"   DISAGREE {os.path.basename(f)}: {arms[a][f][1]} vs {arms[b][f][1]}")
