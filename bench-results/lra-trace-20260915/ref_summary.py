#!/usr/bin/env python3
"""Summarise the reference trace: z3 solver 6 vs solver 2 vs cvc5, on OUR 93.

The question this answers is narrower than "who decides more", and the narrower
question is the one that sizes the work: of the files WE lose, how many does
each reference decide **under our own envelope**, and does z3's answer depend on
which arithmetic theory it builds?

`smt.arith.solver` 6 is `theory_lra` over `lp::lar_solver` (the `QF_LRA`
default) and 2 is `theory_mi_arith`, the classic simplex
(`src/params/theory_arith_params.h:25-32`). Both are Dutertre-de Moura by name,
as ours is, so:

  * a file BOTH decide is not being decided by `lar_solver`'s data structures;
  * a file only 6 decides is;
  * a file NEITHER decides is not winnable at this budget by z3 at all, and
    counting it in our gap overstates what is reachable.

That last bucket is the one a "gap" number silently assumes away, so it is
printed first and with its own denominator.

Usage:  ref_summary.py <ref.*.tsv>... [--buckets <buckets-93.tsv>]
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    ap.add_argument("tsvs", nargs="+")
    ap.add_argument("--buckets", help="bucket_census.py output, to cross-tabulate")
    args = ap.parse_args(argv[1:])

    rows: list[dict[str, str]] = []
    malformed: list[str] = []
    for p in args.tsvs:
        lines = Path(p).read_text().splitlines()
        head = lines[0].split("\t")
        for ln in lines[1:]:
            if not ln:
                continue
            cells = ln.split("\t")
            if len(cells) != len(head):
                malformed.append(f"{p}: {ln[:100]}")
                continue
            rows.append(dict(zip(head, cells, strict=True)))

    n = len(rows)
    print(f"population: {n} rows we do NOT decide  (malformed: {len(malformed)})")
    for m in malformed:
        print(f"  MALFORMED  {m}")
    if not n:
        return 1

    d6 = {r["file"] for r in rows if r["z3s6"] in DECIDED}
    d2 = {r["file"] for r in rows if r["z3s2"] in DECIDED}
    dc = {r["file"] for r in rows if r["cvc5"] in DECIDED}
    allf = {r["file"] for r in rows}

    print()
    print(f"  z3 solver=6 (theory_lra, the QF_LRA default) decides  {len(d6):3d}/{n}")
    print(f"  z3 solver=2 (theory_mi_arith, classic simplex) decides {len(d2):3d}/{n}")
    print(f"  cvc5 1.3.4                                    decides {len(dc):3d}/{n}")
    print()
    print(f"  decided by BOTH z3 arms                 {len(d6 & d2):3d}")
    print(f"  decided ONLY by solver=6 (lar_solver)   {len(d6 - d2):3d}")
    print(f"  decided ONLY by solver=2 (classic)      {len(d2 - d6):3d}")
    print(f"  decided by SOME reference               {len(d6 | d2 | dc):3d}")
    print(f"  **decided by NO reference at 24 s**     {len(allf - (d6 | d2 | dc)):3d}")
    print("     ^ not winnable at this budget by these references; counting it in")
    print("       a 'gap' overstates what is reachable.")

    # z3's own verdict distribution, so a `timeout` is not read as `unknown`.
    print()
    for col in ("z3s6", "z3s2", "cvc5"):
        hist: dict[str, int] = {}
        for r in rows:
            hist[r[col]] = hist.get(r[col], 0) + 1
        print(f"  {col:<6} {dict(sorted(hist.items()))}")

    if args.buckets:
        lines = Path(args.buckets).read_text().splitlines()
        bh = lines[0].split("\t")
        bucket = {}
        for ln in lines[1:]:
            if ln:
                r = dict(zip(bh, ln.split("\t"), strict=True))
                bucket[r["file"]] = r["bucket"]
        print()
        print("  OUR bucket x decided by some reference")
        print(f"  {'bucket':<34}{'n':>5}{'ref decides':>13}{'nobody':>8}")
        print("  " + "-" * 60)
        agg: dict[str, list[int]] = {}
        for r in rows:
            b = bucket.get(r["file"], "UNKNOWN")
            a = agg.setdefault(b, [0, 0])
            a[0] += 1
            if r["file"] in (d6 | d2 | dc):
                a[1] += 1
        for b, (tot, dec) in sorted(agg.items(), key=lambda kv: -kv[1][0]):
            print(f"  {b:<34}{tot:>5}{dec:>13}{tot - dec:>8}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
