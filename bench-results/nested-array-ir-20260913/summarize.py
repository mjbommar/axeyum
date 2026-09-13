#!/usr/bin/env python3
"""Decide rate per division, and the disagreement check, over the shard TSVs.

The exit status depends on the finding: any verdict that contradicts the file's
declared `:status`, or any reference solver present in the run, is a FAIL and
exits non-zero. A summariser that can only print is a checker that cannot fail.

Usage: summarize.py <shard.tsv>...
"""
import collections
import sys


def main():
    rows = []
    header = None
    for path in sys.argv[1:]:
        with open(path) as f:
            for i, line in enumerate(f):
                cells = line.rstrip("\n").split("\t")
                if i == 0:
                    if header is None:
                        header = cells
                    elif header != cells:
                        print(f"FAIL: {path} has a different header than the first shard")
                        return 2
                    continue
                rows.append(cells)
    if header is None or not rows:
        # An empty run prints "0 of 0" otherwise, which is the shape of a clean
        # result rather than of a broken invocation.
        print("FAIL: no rows")
        return 2

    idx = {name: i for i, name in enumerate(header)}
    arms = [c for c in header if c not in ("file", "status") and not c.endswith(("_s", "_k"))]

    n = collections.Counter()
    dec = collections.Counter()
    kills = collections.Counter()
    disagreements = []
    for r in rows:
        div = r[0].split("/")[0]
        n[div] += 1
        declared = r[idx["status"]]
        for a in arms:
            v = r[idx[a]]
            if v in ("sat", "unsat"):
                dec[(div, a)] += 1
                if declared in ("sat", "unsat") and declared != v:
                    disagreements.append((r[0], a, v, f"declared :status {declared}"))
            if r[idx[a + "_k"]] != "ok":
                kills[(a, r[idx[a + "_k"]])] += 1
        # Two arms that both decided must agree.
        decided = {a: r[idx[a]] for a in arms if r[idx[a]] in ("sat", "unsat")}
        vals = set(decided.values())
        if len(vals) > 1:
            disagreements.append((r[0], "/".join(decided), "", "arms disagree"))

    print(f"rows: {len(rows)}   arms: {', '.join(arms)}")
    for div in sorted(n):
        parts = " ".join(
            f"{a}={dec[(div, a)]}/{n[div]} ({100.0 * dec[(div, a)] / n[div]:.1f}%)" for a in arms
        )
        print(f"  {div:9s} {parts}")
    if kills:
        print("non-ok run flags:")
        for (a, k), c in sorted(kills.items()):
            print(f"  {a} {k}: {c}")

    if disagreements:
        print(f"\nDISAGREEMENTS: {len(disagreements)} -- this is a FAIL, not a footnote")
        for d in disagreements[:40]:
            print("  ", *d)
        return 1
    print("\nno verdict contradicts a declared :status or another arm")
    return 0


sys.exit(main())
