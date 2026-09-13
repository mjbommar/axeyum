#!/usr/bin/env python3
"""The QF_NIA winnable population, AFTER ADR-1937, split by polarity.

The brief for this lane sizes the sat half at "64 of ~110 winnable".  That
number is read off a board snapshot taken BEFORE ADR-1937 landed.  ADR-1937 was
a model-construction fix, so the files it harvested are exactly the sat ones --
which means the stale number overstates this lane's own target, and by an
amount nobody had computed.  This script computes it.

Ground truth per file: the benchmark's declared `(set-info :status ...)` when it
declares one, otherwise the board's z3/cvc5 verdict.  Both are recorded so a
reader can see which authority spoke.
"""
import collections
import csv
import os
import re
import subprocess

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
D = os.path.join(ROOT, "bench-results/qf-nia-dispatch-20260912")
BOARD = os.path.join(ROOT, "bench-results/session-20260911-smtlib/head-to-head/QF_NIA.tsv")
OUT = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913")
STATUS = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def main():
    win = [l.strip() for l in open(os.path.join(D, "winnable-110.txt")) if l.strip()]
    ab = {r["file"]: r for r in csv.DictReader(
        open(os.path.join(D, "ab-division-200.tsv")), delimiter="\t")}
    board = {r["file"]: r for r in csv.DictReader(open(BOARD), delimiter="\t")}

    rows = []
    for p in win:
        b = board[os.path.basename(p)]
        m = STATUS.search(open(p, errors="replace").read())
        decl = m.group(1) if m else "none"
        truth = decl if decl in ("sat", "unsat") else next(
            (o for o in (b["z3"], b["cvc5"]) if o in ("sat", "unsat")), "none")
        rows.append((p, ab[p]["b_verdict"], truth, decl, b["z3"], b["cvc5"]))

    print("=== all 110 winnable: ADR-1937 armed verdict x ground truth ===")
    c = collections.Counter((v, t) for _, v, t, _, _, _ in rows)
    for (v, t), n in sorted(c.items()):
        print(f"  armed={v:8s} truth={t:6s}  {n}")

    rem = [r for r in rows if r[1] not in ("sat", "unsat")]
    ct = collections.Counter(t for _, _, t, _, _, _ in rem)
    tot = sum(ct.values())
    print(f"\n=== remaining winnable after ADR-1937: {len(rem)} ===")
    print(f"  sat {ct['sat']}  unsat {ct['unsat']}  none {ct['none']}")
    print(f"  sat share {100 * ct['sat'] / tot:.0f}%  (the stale board says 65% of 110)")

    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "remaining-winnable.tsv"), "w") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["file", "truth", "declared", "z3", "cvc5"])
        for p, _, t, d, z, cc in rem:
            w.writerow([p, t, d, z, cc])
    with open(os.path.join(OUT, "remaining-winnable.txt"), "w") as f:
        for p, _, _, _, _, _ in rem:
            f.write(p + "\n")
    print(f"\nwrote {OUT}/remaining-winnable.{{tsv,txt}}")


if __name__ == "__main__":
    main()
