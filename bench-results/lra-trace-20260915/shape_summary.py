#!/usr/bin/env python3
"""Summarise one or two `shape_census.py` TSVs side by side.

Two populations rather than one on purpose.  A median over the undecided rows
alone answers "how big are the files we lose", which nobody disputes; the
question that decides where to look is "does SIZE separate the two halves, or
does something else", and only a paired summary can answer it.  So the decided
population is carried as a CONTROL in the same table, and a column where the
two medians are close is evidence AGAINST that column being the cause.

Usage:  shape_summary.py <undecided.tsv> [<decided.tsv>]
"""

from __future__ import annotations

import statistics
import sys
from pathlib import Path

NUMERIC = [
    "bytes",
    "vars",
    "asserts",
    "atoms",
    "equalities",
    "eq_bool_hint",
    "strict",
    "muls",
    "rational_lits",
    "max_numeral_digits",
    "max_denominator_digits",
]


def load(path: Path) -> list[dict[str, str]]:
    lines = path.read_text().splitlines()
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"), strict=True)) for ln in lines[1:] if ln]


def stats(rows: list[dict[str, str]], col: str) -> tuple[int, int, int]:
    vals = sorted(int(r[col]) for r in rows)
    if not vals:
        return (0, 0, 0)
    return (int(statistics.median(vals)), vals[0], vals[-1])


def main(argv: list[str]) -> int:
    if len(argv) not in (2, 3):
        sys.stderr.write(__doc__ or "")
        return 2
    a = load(Path(argv[1]))
    b = load(Path(argv[2])) if len(argv) == 3 else []
    print(f"population A (undecided): {len(a)} rows")
    if b:
        print(f"population B (decided, CONTROL): {len(b)} rows")
    print()
    hdr = f"{'column':<26}{'A median':>12}{'A min':>10}{'A max':>12}"
    if b:
        hdr += f"{'B median':>12}{'B min':>10}{'B max':>12}{'A/B med':>10}"
    print(hdr)
    print("-" * len(hdr))
    for col in NUMERIC:
        am, amin, amax = stats(a, col)
        line = f"{col:<26}{am:>12,}{amin:>10,}{amax:>12,}"
        if b:
            bm, bmin, bmax = stats(b, col)
            ratio = f"{am / bm:.2f}x" if bm else "n/a"
            line += f"{bm:>12,}{bmin:>10,}{bmax:>12,}{ratio:>10}"
        print(line)
    print()
    for name, rows in (("A undecided", a), ("B decided", b)):
        if not rows:
            continue
        st: dict[str, int] = {}
        for r in rows:
            st[r["status"]] = st.get(r["status"], 0) + 1
        lg: dict[str, int] = {}
        for r in rows:
            lg[r["logic"]] = lg.get(r["logic"], 0) + 1
        pure_eq = sum(1 for r in rows if float(r["eq_share"]) >= 0.5)
        no_mul = sum(1 for r in rows if int(r["muls"]) == 0)
        big_coef = sum(1 for r in rows if int(r["max_numeral_digits"]) > 18)
        big_den = sum(1 for r in rows if int(r["max_denominator_digits"]) > 18)
        print(f"{name}: :status {dict(sorted(st.items()))}")
        print(f"{name}: logic   {dict(sorted(lg.items()))}")
        print(
            f"{name}: eq_share>=0.5 {pure_eq}/{len(rows)}  "
            f"no-multiplication {no_mul}/{len(rows)}  "
            f"numeral>18 digits {big_coef}/{len(rows)}  "
            f"denominator>18 digits {big_den}/{len(rows)}"
        )
        print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
