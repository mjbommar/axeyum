#!/usr/bin/env python3
"""Which z3 nonlinear class is LOAD-BEARING on the QF_NIA files we miss.

ADR-2112. Reads `z3-ablate-classes.sh`'s output and reports, per disabled
class, how many files z3 stops deciding.

The denominator is measured IN THIS SWEEP, not inherited: only files the
`base` arm decided here are scored, so a file that was ambient-slow in the
baseline is excluded from every class rather than counted as a loss for all of
them. The count of what that excluded is printed.

A class is load-bearing on a file when `base` decides it and the arm without
that class does not. The reverse also happens -- disabling a class can make z3
FASTER, because the portfolio stops spending time on it -- and those are
reported too, as gains, rather than dropped for being inconvenient.

usage: analyse-ablation.py <ablate.tsv>...
"""

import collections
import statistics
import sys

DECIDED = {"sat", "unsat"}


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2

    rows: list[tuple[str, str, str, int]] = []
    for path in argv[1:]:
        with open(path) as handle:
            next(handle, None)
            for line in handle:
                f = line.rstrip("\n").split("\t")
                if len(f) >= 5 and f[1] != "arm":
                    rows.append((f[0], f[1], f[2], int(f[3]) if f[3].isdigit() else -1))
    if not rows:
        print("no rows: an empty ablation is not a result", file=sys.stderr)
        return 1

    by: dict[tuple[str, str], tuple[str, int]] = {}
    for path, arm, verdict, ms in rows:
        by[(path, arm)] = (verdict, ms)
    files = sorted({p for p, _, _, _ in rows})
    arms = [a for a in dict.fromkeys(arm for _, arm, _, _ in rows)]

    print(f"files {len(files)}   arms {len(arms)}   rows {len(rows)}")

    # Coverage first: an arm that did not see every file is not comparable.
    print("\n=== coverage ===")
    for arm in arms:
        seen = sum(1 for f in files if (f, arm) in by)
        print(f"  {arm:<18} {seen:>3} of {len(files)}")

    base_decided = [
        f for f in files if (f, "base") in by and by[(f, "base")][0] in DECIDED
    ]
    skipped = len(files) - len(base_decided)
    print(f"\nbaseline decided {len(base_decided)} of {len(files)}")
    if skipped:
        print(f"  {skipped} file(s) the BASELINE did not decide in this sweep are")
        print("  excluded from every class below, not scored as a loss for all of them")

    base_ms = [by[(f, "base")][1] for f in base_decided if by[(f, "base")][1] >= 0]
    if base_ms:
        print(f"  baseline median {statistics.median(base_ms):.0f} ms")

    print("\n=== LOAD-BEARING: files the baseline decides and the arm does NOT ===")
    table: list[tuple[int, int, str]] = []
    for arm in arms:
        if arm == "base":
            continue
        lost = [
            f
            for f in base_decided
            if (f, arm) in by and by[(f, arm)][0] not in DECIDED
        ]
        gained_ms = [
            by[(f, "base")][1] - by[(f, arm)][1]
            for f in base_decided
            if (f, arm) in by and by[(f, arm)][0] in DECIDED and by[(f, arm)][1] >= 0
        ]
        speed = (
            f"median {statistics.median(gained_ms):+.0f} ms on what it still decides"
            if gained_ms
            else ""
        )
        table.append((len(lost), len(base_decided), arm))
        pct = 100.0 * len(lost) / len(base_decided) if base_decided else 0.0
        print(f"  {arm:<18} {len(lost):>3} of {len(base_decided)} ({pct:5.1f} %)   {speed}")

    print("\n=== ranked, which class costs the most files when removed ===")
    for lost, total, arm in sorted(table, reverse=True):
        print(f"  {lost:>3} of {total}   {arm}")

    # Overlap: is one class's contribution a subset of another's?
    print("\n=== do two classes cover the same files? (|A and B| / |A or B|) ===")
    lost_sets = {
        arm: {
            f
            for f in base_decided
            if (f, arm) in by and by[(f, arm)][0] not in DECIDED
        }
        for _, _, arm in table
    }
    names = [a for a in lost_sets if lost_sets[a]]
    for i, a in enumerate(names):
        for b in names[i + 1 :]:
            inter = lost_sets[a] & lost_sets[b]
            union = lost_sets[a] | lost_sets[b]
            if inter:
                print(
                    f"  {a} & {b}: {len(inter)} shared of {len(union)} "
                    f"({100.0 * len(inter) / len(union):.0f} %)"
                )

    print("\n=== files NO single class removal breaks (the portfolio is redundant) ===")
    any_break = set().union(*lost_sets.values()) if lost_sets else set()
    robust = [f for f in base_decided if f not in any_break]
    print(f"  {len(robust)} of {len(base_decided)} decided under every single-class removal")

    # The distribution is the point, not the total: a file broken by ONE class
    # has a single point of failure z3 depends on; a file broken by none is
    # decided by at least two independent routes, and no single capability we
    # could build would be what closes it.
    print("\n=== per file: how many of the classes, removed SINGLY, break it ===")
    depth: collections.Counter[int] = collections.Counter()
    for name in base_decided:
        depth[sum(1 for s in lost_sets.values() if name in s)] += 1
    for count in sorted(depth):
        label = "none — decided by a redundant portfolio" if count == 0 else f"{count} class(es)"
        print(f"  {depth[count]:>3} files broken by {label}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
