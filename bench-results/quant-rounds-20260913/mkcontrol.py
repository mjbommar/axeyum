#!/usr/bin/env python3
"""The COST control: files we already DECIDE in the same quantified divisions.

A round cap converts a slow `unknown` into a fast one.  Raising it runs the
opposite risk, and ADR-1945 measured exactly that failure: 33 of 35 non-gainers
became clock-bound, and two files went from a 0.5 s verdict to a 25 s watchdog.
So the control must be work we currently get RIGHT and FAST.

This lane's brief named QF_UFLIA, QF_UFLRA, NRA and QF_DT.  Three of those four
are quantifier-FREE, so the e-matching instantiation loop cannot run on them at
all -- `summarize.py control` prints the measured hit rate and it is 0.  A
control that never reaches the code under test cannot detect a change to it,
which is the hole ADR-1945's lane found in its own control (`ufbv_online` fired
on 0 of 400).

The non-vacuous control is the DECIDED rows of the same six quantified
divisions the population came from: same corpus families, same ladder, same
loop -- and a verdict to lose.

Writes pop/decided-<DIV>.txt and pop/decided-ALL.txt.
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
BOARD = HERE.parent / "six-divisions-headtohead-20260912"
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVISIONS = ["LRA", "AUFLIA", "BV", "NRA", "UFLIA", "QF_AUFLIA"]


def main() -> int:
    out = HERE / "pop"
    out.mkdir(exist_ok=True)
    allrows: list[str] = []
    for div in DIVISIONS:
        tsv = BOARD / f"{div}.tsv"
        if not tsv.exists():
            print(f"ABORT: {tsv} missing", file=sys.stderr)
            return 2
        lines = tsv.read_text().splitlines()
        head = lines[0].split("\t")
        fi, ai = head.index("file"), head.index("axeyum")
        rows = [
            CORPUS + c[fi]
            for c in (ln.split("\t") for ln in lines[1:] if ln.strip())
            if c[ai] in ("sat", "unsat")
        ]
        (out / f"decided-{div}.txt").write_text("".join(r + "\n" for r in rows))
        allrows.extend(rows)
        print(f"{div:10s} {len(rows):4d}")
    (out / "decided-ALL.txt").write_text("".join(r + "\n" for r in allrows))
    print(f"{'TOTAL':10s} {len(allrows):4d}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
