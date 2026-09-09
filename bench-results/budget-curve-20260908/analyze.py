#!/usr/bin/env python3
"""Budget-curve tables, including the load-matched 24 s repeat.

Input: <indir>/<DIV>-b<BUDGET>.tsv and <DIV>-b24r.tsv, the exact per-file
sidecars `scripts/parity-run.sh` wrote (file, axeyum, reference, declared).
Nothing is recomputed and no verdict is inferred; this only counts.
"""

import sys
import os
import collections

ARMS = ["6", "12", "24", "24r", "60"]
LABEL = {"6": "6 s", "12": "12 s", "24": "24 s", "24r": "24 s (repeat)", "60": "60 s"}


def read(path):
    rows = {}
    with open(path) as fh:
        fh.readline()
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3:
                rows[parts[0]] = (parts[1], parts[2])
    return rows


def counts(rows, idx):
    return sum(1 for v in rows.values() if v[idx] != "unsolved")


def main():
    indir = sys.argv[1]
    divisions = sys.argv[2:]
    d = {}
    for div in divisions:
        d[div] = {}
        for a in ARMS:
            p = os.path.join(indir, f"{div}-b{a}.tsv")
            if os.path.exists(p):
                d[div][a] = read(p)

    print("### Table 1 — solved count versus budget, both solvers\n")
    print("| division | budget | axeyum | reference | ratio | both / axeyum-only / reference-only |")
    print("|---|---|---:|---:|---:|---|")
    for div in divisions:
        for a in ARMS:
            r = d[div].get(a)
            if not r:
                continue
            n = len(r)
            av, rv = counts(r, 0), counts(r, 1)
            both = sum(1 for v in r.values() if v[0] != "unsolved" and v[1] != "unsolved")
            ratio = f"{100.0*av/rv:.1f}%" if rv else "n/a"
            print(f"| {div} | {LABEL[a]} | {av}/{n} | {rv}/{n} | {ratio} | {both} / {av-both} / {rv-both} |")
    print()

    print("### Table 2 — increments: where each curve flattens\n")
    print("| division | solver | 6→12 | 12→24 | 24→60 | 24(repeat)→60 |")
    print("|---|---|---:|---:|---:|---:|")
    for div in divisions:
        for idx, name in ((0, "axeyum"), (1, "reference")):
            c = {a: counts(r, idx) for a, r in d[div].items()}
            def dl(x, y):
                return f"+{c[y]-c[x]}" if x in c and y in c else "—"
            print(f"| {div} | {name} | {dl('6','12')} | {dl('12','24')} | {dl('24','60')} | {dl('24r','60')} |")
    print()

    print("### Table 3 — the contention noise floor: 24 s versus 24 s repeat\n")
    print("Same list, same binary, same host, same day; only the neighbours differ.")
    print("`moved` counts files whose verdict changed in EITHER direction.\n")
    print("| division | solver | 24 s | 24 s repeat | delta | files that moved |")
    print("|---|---|---:|---:|---:|---:|")
    for div in divisions:
        if "24" not in d[div] or "24r" not in d[div]:
            continue
        a24, a24r = d[div]["24"], d[div]["24r"]
        for idx, name in ((0, "axeyum"), (1, "reference")):
            c1, c2 = counts(a24, idx), counts(a24r, idx)
            moved = sum(1 for f in a24
                        if f in a24r
                        and (a24[f][idx] == "unsolved") != (a24r[f][idx] == "unsolved"))
            print(f"| {div} | {name} | {c1} | {c2} | {c2-c1:+d} | {moved} |")
    print()

    print("### Table 4 — time-bound versus capability-bound losses\n")
    print("A LOSS is a file the reference decides and we do not, at the 24 s")
    print("baseline. The baseline is the 24 s REPEAT where one exists, because it")
    print("is load-matched to the 60 s pass.\n")
    print("| division | baseline used | losses | time-bound (we decide it at 60 s) | capability-bound (we still miss at 60 s) |")
    print("|---|---|---:|---:|---:|")
    detail = {}
    for div in divisions:
        base_key = "24r" if "24r" in d[div] else "24"
        if base_key not in d[div] or "60" not in d[div]:
            print(f"| {div} | (missing sidecar) | | | |")
            continue
        base, r60 = d[div][base_key], d[div]["60"]
        losses = [f for f, v in base.items() if v[0] == "unsolved" and v[1] != "unsolved"]
        tb = [f for f in losses if f in r60 and r60[f][0] != "unsolved"]
        cb = [f for f in losses if f not in tb]
        detail[div] = (base_key, losses, tb, cb)
        print(f"| {div} | {LABEL[base_key]} | {len(losses)} | {len(tb)} | {len(cb)} |")
    print()

    print("### Table 5 — flips: decided at a shorter budget, lost at a longer one\n")
    print("| division | solver | 24 s → 60 s |")
    print("|---|---|---:|")
    for div in divisions:
        base_key = "24r" if "24r" in d[div] else "24"
        if base_key not in d[div] or "60" not in d[div]:
            continue
        base, r60 = d[div][base_key], d[div]["60"]
        for idx, name in ((0, "axeyum"), (1, "reference")):
            flips = sum(1 for f, v in base.items()
                        if v[idx] != "unsolved" and f in r60 and r60[f][idx] == "unsolved")
            print(f"| {div} | {name} | {flips} |")
    print()

    print("### Table 6 — capability-bound losses by benchmark family\n")
    for div in divisions:
        if div not in detail:
            continue
        _, _, _, cb = detail[div]
        print(f"**{div} — {len(cb)} files**\n")
        print("| family | files |")
        print("|---|---:|")
        for fam, c in collections.Counter(f.split("/")[-2] for f in cb).most_common():
            print(f"| `{fam}` | {c} |")
        print()

    # Machine-readable dump for the committed artifact.
    with open(os.path.join(indir, "classification.tsv"), "w") as out:
        out.write("division\tbaseline\tclass\tfile\n")
        for div in divisions:
            if div not in detail:
                continue
            bk, _, tb, cb = detail[div]
            for f in sorted(tb):
                out.write(f"{div}\t{bk}\ttime-bound\t{f}\n")
            for f in sorted(cb):
                out.write(f"{div}\t{bk}\tcapability-bound\t{f}\n")


if __name__ == "__main__":
    main()
