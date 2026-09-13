"""Summarize the ADR-1935 A/B: gains, losses, flips, wall delta, per division.

Reads the merged per-division TSVs written by `ab-shard.sh`.  Every row carries
both arms' verdict, wall time and give-up reason for ONE file, measured back to
back on the same pinned core pair, so the difference is per file rather than a
difference of two aggregates.

Usage: python3 analyze.py <dir-with-*.tsv>
"""

import collections
import glob
import os
import sys


def rows(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        head = fh.readline()
        assert head.startswith("file\t"), path
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 8:
                continue
            yield dict(
                zip(
                    (
                        "file",
                        "base",
                        "base_s",
                        "base_giveup",
                        "new",
                        "new_s",
                        "new_giveup",
                        "status",
                    ),
                    parts,
                )
            )


def main(root):
    divs = collections.defaultdict(list)
    # Accepts both the per-shard files the runner writes (`<div>.s<k>.tsv`) and
    # the merged per-division files committed here (`<div>.tsv`).
    paths = sorted(glob.glob(os.path.join(root, "*.s*.tsv")))
    if not paths:
        paths = sorted(glob.glob(os.path.join(root, "*.tsv")))
    for p in paths:
        div = os.path.basename(p).split(".")[0]
        divs[div].extend(rows(p))

    print(
        f"{'division':<12}{'n':>5}{'base':>7}{'new':>6}{'delta':>7}"
        f"{'gain':>6}{'loss':>6}{'flip':>6}{'base_s':>9}{'new_s':>9}"
    )
    disagreements = []
    for div in ("AUFDTLIRA", "UFDTLIRA", "UFDT", "QF_DT", "UF"):
        rs = divs.get(div)
        if not rs:
            continue
        dec = lambda v: v in ("sat", "unsat")
        base = sum(dec(r["base"]) for r in rs)
        new = sum(dec(r["new"]) for r in rs)
        gain = sum(1 for r in rs if not dec(r["base"]) and dec(r["new"]))
        loss = sum(1 for r in rs if dec(r["base"]) and not dec(r["new"]))
        flip = sum(
            1
            for r in rs
            if dec(r["base"]) and dec(r["new"]) and r["base"] != r["new"]
        )
        bs = sum(float(r["base_s"]) for r in rs)
        ns = sum(float(r["new_s"]) for r in rs)
        print(
            f"{div:<12}{len(rs):>5}{base:>7}{new:>6}{new - base:>+7}"
            f"{gain:>6}{loss:>6}{flip:>6}{bs:>9.1f}{ns:>9.1f}"
        )
        for r in rs:
            for arm in ("base", "new"):
                if dec(r[arm]) and r["status"] in ("sat", "unsat") and r[arm] != r["status"]:
                    disagreements.append((div, arm, r["file"], r[arm], r["status"]))

    print()
    print(f"declared-:status disagreements: {len(disagreements)}")
    for d in disagreements:
        print("  DISAGREE", d)

    print()
    print("newly decided files (gains):")
    for div in ("AUFDTLIRA", "UFDTLIRA", "UFDT", "QF_DT", "UF"):
        for r in divs.get(div, []):
            if r["base"] not in ("sat", "unsat") and r["new"] in ("sat", "unsat"):
                print(f"  GAIN {div} {r['new']} status={r['status']} {r['file']}")
    print()
    print("lost files (regressions):")
    for div in ("AUFDTLIRA", "UFDTLIRA", "UFDT", "QF_DT", "UF"):
        for r in divs.get(div, []):
            if r["base"] in ("sat", "unsat") and r["new"] not in ("sat", "unsat"):
                print(
                    f"  LOSS {div} base={r['base']} status={r['status']} "
                    f"new_giveup={r['new_giveup'][:90]} {r['file']}"
                )

    print()
    print("kill / abort rows (either arm):")
    kills = collections.Counter()
    for div, rs in divs.items():
        for r in rs:
            for arm in ("base", "new"):
                g = r[f"{arm}_giveup"]
                if g in ("WRAPPER-KILLED", "RC134-ABORT", "SIGKILL"):
                    kills[(div, arm, g)] += 1
    for k, v in sorted(kills.items()):
        print("  ", k, v)
    if not kills:
        print("   none")

    print()
    print("top NEW give-up reasons on the three target divisions:")
    c = collections.Counter()
    for div in ("AUFDTLIRA", "UFDTLIRA", "UFDT"):
        for r in divs.get(div, []):
            if r["new"] in ("sat", "unsat"):
                continue
            c[r["new_giveup"][:120]] += 1
    for k, v in c.most_common(10):
        print(f"  {v:4d}  {k}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
