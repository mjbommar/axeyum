"""Score an interleaved A/B run directory (<arm>.<n>.{out,meta}).

PAR-2 follows the protocol: a file decided within the 24 s budget scores its
wall; anything else (unknown, timeout, overshoot past the budget) scores 2x24 s.
An overshoot IS a loss under a 24 s protocol, so it is scored as one.
"""

import os
import sys

BUDGET_MS = 24000


def load(rundir, arm, n):
    meta = dict(
        l.split("\t", 1)
        for l in open(os.path.join(rundir, "%s.%d.meta" % (arm, n))).read().splitlines()
        if "\t" in l
    )
    out = open(os.path.join(rundir, "%s.%d.out" % (arm, n)), errors="replace").read().splitlines()
    verdict = out[0].split()[0] if out else "<none>"
    return verdict, int(meta["wall_ms"]), meta["path"]


def main(rundir, listfile, *arms):
    paths = [l.strip() for l in open(listfile) if l.strip()]
    per = {a: [] for a in arms}
    for i, p in enumerate(paths, 1):
        for a in arms:
            try:
                per[a].append(load(rundir, a, i))
            except OSError:
                per[a].append(("<missing>", 0, p))
    n = len(paths)
    print("files: %d   arms: %s\n" % (n, ", ".join(arms)))
    print("%-10s %8s %8s %10s %10s" % ("arm", "decided", "unknown", "PAR-2 (s)", "wall (s)"))
    for a in arms:
        dec = sum(1 for v, w, _ in per[a] if v in ("sat", "unsat") and w <= BUDGET_MS)
        unk = n - dec
        par2 = sum(
            w if (v in ("sat", "unsat") and w <= BUDGET_MS) else 2 * BUDGET_MS
            for v, w, _ in per[a]
        )
        wall = sum(w for _, w, _ in per[a])
        print("%-10s %8d %8d %10.1f %10.1f" % (a, dec, unk, par2 / 1000, wall / 1000))

    base = arms[0]
    for a in arms[1:]:
        flips = [
            (os.path.basename(p), per[base][i][0], per[a][i][0])
            for i, (v, w, p) in enumerate(per[a])
            if per[base][i][0] != v
        ]
        print("\n== verdict changes %s -> %s: %d" % (base, a, len(flips)))
        for f, b, x in flips:
            print("   %-46s %s -> %s" % (f[:46], b, x))
        contra = [
            (os.path.basename(p), per[base][i][0], v)
            for i, (v, w, p) in enumerate(per[a])
            if per[base][i][0] in ("sat", "unsat") and v in ("sat", "unsat") and per[base][i][0] != v
        ]
        print("   contradictory verdicts (sat vs unsat): %d" % len(contra))

    print("\n== per-file wall (ms)")
    print("%-46s %s" % ("file", "  ".join("%10s" % a for a in arms)))
    for i, p in enumerate(paths):
        print(
            "%-46s %s"
            % (
                os.path.basename(p)[:46],
                "  ".join("%10s" % ("%s/%d" % (per[a][i][0][:5], per[a][i][1])) for a in arms),
            )
        )


main(*sys.argv[1:])
