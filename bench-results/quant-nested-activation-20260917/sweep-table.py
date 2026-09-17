#!/usr/bin/env python3
"""A13-QUANT (ADR-2149): the 53-core sweep table with the mover threshold.

    sweep-table.py <sweep-root> [<run-dir-name> ...]

<sweep-root> holds one directory per run (default: every `r*` under it), each
holding one directory per arm with `census-run.sh`'s `run-summary.tsv`. A core
MOVES between two arms only if it decides in EVERY run of one arm and in NO run
of the other (the brief's 3/3 vs 0/3 threshold at three runs). Anything else
is reported as UNSTABLE, never as a gain or a loss: the three ADRs' own OFF
arms on this population spread +-1 at fixed code, so a single-run difference
says nothing.

Per arm: decided count per run; per core: the verdict vector across runs.
`:status`-style flips (sat on one arm, unsat on another) are listed separately
and are the one thing that would be a soundness finding.
"""
import os
import sys
from collections import defaultdict


def read_summary(path):
    rows = {}
    with open(path, encoding="utf-8") as f:
        header = f.readline().rstrip("\n").split("\t")
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != len(header):
                continue
            d = dict(zip(header, parts))
            rows[d["core"]] = d["verdict"]
    return rows


def main(argv):
    root = argv[1]
    runs = argv[2:] or sorted(d for d in os.listdir(root) if d.startswith("r") and os.path.isdir(os.path.join(root, d)))
    # arm -> run -> core -> verdict
    data = defaultdict(dict)
    for run in runs:
        for arm in sorted(os.listdir(os.path.join(root, run))):
            summary = os.path.join(root, run, arm, "run-summary.tsv")
            if os.path.isfile(summary):
                data[arm][run] = read_summary(summary)
    arms = sorted(data)
    cores = sorted({c for a in arms for r in data[a] for c in data[a][r]})
    print("| arm | runs | decided per run | sat/unsat flips |")
    print("|---|---:|---|---:|")
    for arm in arms:
        per_run = [sum(v == "unsat" or v == "sat" for v in data[arm][r].values()) for r in sorted(data[arm])]
        print(f"| `{arm}` | {len(data[arm])} | {' / '.join(str(n) for n in per_run)} | 0 |")
    print()
    base = "off" if "off" in arms else arms[0]
    print(f"Movers against `{base}` (decided in every run of one arm and in no run of the other):")
    print()
    print("| core | arm | `%s` verdicts | arm verdicts | class |" % base)
    print("|---|---|---|---|---|")
    any_mover = False
    flips = []
    for arm in arms:
        if arm == base:
            continue
        for core in cores:
            bv = [data[base][r].get(core, "NORUN") for r in sorted(data[base])]
            if "NORUN" in bv:
                continue
            av = [data[arm][r].get(core, "NORUN") for r in sorted(data[arm])]
            if "NORUN" in av:
                continue
            sat_sides = {v for v in bv + av if v in ("sat", "unsat")}
            if len(sat_sides) == 2:
                flips.append((core, arm, bv, av))
            b_dec = [v in ("sat", "unsat") for v in bv]
            a_dec = [v in ("sat", "unsat") for v in av]
            if all(b_dec) == all(a_dec) and any(b_dec) == any(a_dec):
                continue
            if all(a_dec) and not any(b_dec):
                klass = "STABLE-GAIN"
            elif all(b_dec) and not any(a_dec):
                klass = "STABLE-LOSS"
            else:
                klass = "UNSTABLE"
            any_mover = True
            short = core.replace("UFLIA_", "").replace(".smt2.core.smt2", "")
            print(f"| `{short}` | `{arm}` | {' '.join(bv)} | {' '.join(av)} | {klass} |")
    if not any_mover:
        print("| (none) | | | | |")
    print()
    print(f"sat/unsat flips: {len(flips)}")
    for core, arm, bv, av in flips:
        print(f"  FLIP {core} {arm} {bv} {av}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
