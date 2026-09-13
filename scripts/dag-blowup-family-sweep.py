#!/usr/bin/env python3
"""Sweep each ADR-1940 repro family upward in depth and report the growth RATIO.

A ratio near 2.0 is a live unmemoised DAG walker: the cost is the number of
root-to-leaf paths and each level doubles it. A ratio near 1.0 is flat.

The ratio, not the absolute time, is the signal — which is what makes this
usable on a shared box. A doubling family is doubling at load 2 and at load 20.
Absolute seconds from a loaded run are NOT comparable to a quiet one; the
`DOUBLING` flag is.

    python3 scripts/dag-blowup-repro-family.py /tmp/fam
    python3 scripts/dag-blowup-family-sweep.py --dir /tmp/fam \\
        --binary target/release/examples/smtcomp_cli --core 6

Then `perf record -g -- <binary> /tmp/fam/<family>.<deepest>.smt2` on every
family flagged DOUBLING; the top symbol is the walker to memoise.
"""
import argparse
import os
import re
import subprocess
import time


def run(binary, path, budget_ms, core):
    cmd = []
    if core:
        cmd += ["taskset", "-c", core]
    cmd += [binary, path, "--timeout-ms", str(budget_ms)]
    t0 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    wall = time.time() - t0
    verdict = "none"
    for line in (p.stdout + p.stderr).splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            verdict = s
    return verdict, wall


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True, help="directory written by dag-blowup-repro-family.py")
    ap.add_argument("--binary", required=True)
    ap.add_argument("--core", default="", help="taskset core, e.g. 6")
    ap.add_argument("--budget-ms", type=int, default=10000)
    ap.add_argument("--stop-s", type=float, default=3.0,
                    help="stop climbing a family once one file exceeds this")
    ap.add_argument("--only", default="", help="comma-separated family names")
    args = ap.parse_args()

    fams = sorted({f.rsplit(".", 2)[0] for f in os.listdir(args.dir) if f.endswith(".smt2")})
    if args.only:
        want = set(args.only.split(","))
        fams = [f for f in fams if f in want]

    print(f"{'family':<16} {'last depths (s)':<46} {'ratio':<7} verdicts")
    doubling = []
    for fam in fams:
        depths = sorted(int(re.search(r"\.(\d+)\.smt2$", f).group(1))
                        for f in os.listdir(args.dir) if f.startswith(fam + "."))
        times, verdicts, used = [], [], []
        for d in depths:
            v, w = run(args.binary, os.path.join(args.dir, f"{fam}.{d:02d}.smt2"),
                       args.budget_ms, args.core)
            times.append(w)
            verdicts.append(v)
            used.append(d)
            if w > args.stop_s:
                break
        shown = " ".join(f"d{d}={t:.2f}" for d, t in list(zip(used, times))[-4:])
        # Only compare two points that are both well above timer noise.
        ratio = times[-1] / times[-2] if len(times) >= 3 and times[-2] > 0.02 else float("nan")
        flag = ""
        if ratio == ratio and ratio > 1.6:
            flag = "  <-- DOUBLING"
            doubling.append(fam)
        print(f"{fam:<16} {shown:<46} {ratio:<7.2f} "
              f"{'/'.join(sorted(set(verdicts)))}{flag}")
    print()
    if doubling:
        print("DOUBLING families (each names a live unmemoised walker): "
              + ", ".join(doubling))
    else:
        print("no family doubled")


if __name__ == "__main__":
    main()
