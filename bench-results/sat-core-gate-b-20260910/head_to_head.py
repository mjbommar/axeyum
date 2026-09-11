#!/usr/bin/env python3
"""On the files BOTH engines decide, which is faster and by how much?

The decided-count is a threshold statistic: it says nothing about the files on
either side of the threshold. This is the complementary view -- per-file wall
time on the intersection -- because "we decide 5 fewer files" and "we are 3x
slower on the ones we share" are different claims about how big the gap is.
"""
import os
import sys

ART = ("/home/mjbommar/projects/personal/axeyum/.claude/worktrees/"
       "agent-a7dcb8ed25e519347/bench-results/sat-core-gate-b-20260910")


def read(path, verdict_col, wall_col):
    out = {}
    if not os.path.exists(path):
        return out
    lines = open(path, encoding="utf-8").read().splitlines()
    hdr = lines[0].split("\t")
    vi, wi = hdr.index(verdict_col), hdr.index(wall_col)
    for line in lines[1:]:
        if not line.strip():
            continue
        c = line.split("\t")
        if c[vi] in ("sat", "unsat"):
            out[c[0]] = float(c[wi])
    return out


for fam in ("p4dfa", "noetzli"):
    nat = read(f"{ART}/native-{fam}.tsv", "native_verdict", "native_ms")
    for eng in ("cadical", "kissat"):
        ext = read(f"{ART}/{eng}-{fam}.tsv", "verdict", "wall_ms")
        shared = sorted(set(nat) & set(ext))
        if not shared:
            continue
        print(f"\n### {fam}: native vs {eng}, {len(shared)} files both decide")
        faster = slower = 0
        ratios = []
        for name in shared:
            r = nat[name] / ext[name] if ext[name] > 0 else float("inf")
            ratios.append(r)
            if r < 1:
                faster += 1
            else:
                slower += 1
            print(f"  {nat[name]:10.1f} ms native  {ext[name]:10.1f} ms {eng}"
                  f"   ratio {r:6.2f}x  {name}")
        ratios.sort()
        mid = len(ratios) // 2
        median = ratios[mid] if len(ratios) % 2 else (ratios[mid - 1] + ratios[mid]) / 2
        print(f"  -> native faster on {faster} of {len(shared)}, "
              f"slower on {slower}; median ratio {median:.2f}x "
              f"(>1 means native is slower)")
sys.exit(0)
