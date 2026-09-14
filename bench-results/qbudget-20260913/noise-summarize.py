#!/usr/bin/env python3
"""The noise floor: three independent BASE-arm readings of one whole division.

Prints the per-run division total, the peak-to-trough BAND, and -- the number
that actually matters -- how many individual FILES disagree with themselves
across the three runs. A division total can be stable while a dozen files churn
underneath it, and it is the per-file churn that decides whether a +2 net is a
result.

The three runs are NOT interchangeable with the three arms of an A/B: these are
all the SAME arm. That is the point. Any spread here is the machine, not the
lever.

EXITS NON-ZERO if a run is short of the pinned list, because a missing row makes
every total below it a measurement of a smaller set.

Usage: noise-summarize.py <run1.tsv> <run2.tsv> <run3.tsv> ...
"""

import collections
import sys

DECIDED = ("sat", "unsat")


def rows(path):
    with open(path, encoding="utf-8") as handle:
        header = handle.readline().rstrip("\n").split("\t")
        out = {}
        for line in handle:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != len(header):
                continue
            r = dict(zip(header, parts))
            out[r["file"]] = r
        return out


def main(argv):
    if len(argv) < 3:
        print(__doc__)
        return 2
    runs = [(p, rows(p)) for p in argv[1:]]
    sizes = {len(r) for _, r in runs}
    if len(sizes) != 1:
        print(f"ABORT: runs cover different file counts {sorted(sizes)}")
        return 3
    n = sizes.pop()

    totals = []
    for path, r in runs:
        t = sum(1 for row in r.values() if row["base"] in DECIDED)
        totals.append(t)
        print(f"  {path}: n={n}  decided={t}")

    band = max(totals) - min(totals)
    print(f"\n  division totals: {totals}")
    print(f"  NOISE BAND (peak to trough over {len(runs)} base-arm runs): {band} file(s)")

    # Per-file churn: the number that a stable total can hide.
    files = set(runs[0][1])
    churn = []
    for f in sorted(files):
        verdicts = [r[f]["base"] if f in r else "MISSING" for _, r in runs]
        decided = [v in DECIDED for v in verdicts]
        if len(set(decided)) > 1:
            churn.append((f, verdicts))
    print(f"  FILES THAT DISAGREE WITH THEMSELVES across the runs: {len(churn)}")
    for f, v in churn[:25]:
        print(f"    {f}  {v}")
    if len(churn) > 25:
        print(f"    ... and {len(churn) - 25} more")

    # A sat<->unsat flip between runs of the SAME arm would be a soundness event,
    # not noise, so it is separated out and it sets the exit status.
    bad = 0
    for f in sorted(files):
        vs = {r[f]["base"] for _, r in runs if f in r} & set(DECIDED)
        if len(vs) > 1:
            print(f"    SAT<->UNSAT BETWEEN RUNS OF ONE ARM: {f} {sorted(vs)}")
            bad += 1
    if bad:
        print(f"\nFAIL: {bad} file(s) flipped sat<->unsat between runs of the SAME arm")
        return 1
    print("\nOK: no sat<->unsat flip between runs of the same arm")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
