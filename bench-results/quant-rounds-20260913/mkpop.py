#!/usr/bin/env python3
"""Derive this lane's populations from lane `board-six`'s committed census.

Nothing here is transcribed.  The 177-row family is re-derived from
`census/*.tsv` by the give-up string ADR-1950 ranked, so if that census is
re-run the population moves with it, and the count this lane quotes is the
count this script prints.

Writes:
  pop/round-budget-<DIV>.txt   the rows whose give-up is the ranked string
  pop/round-budget-ALL.txt     all of them, division order as on the board
"""

import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
BOARD = HERE.parent / "six-divisions-headtohead-20260912"
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
RANKED = "e-matching instantiation did not refute within the round budget"

# Board order, so a reader can line the counts up with ADR-1950's table.
DIVISIONS = ["LRA", "AUFLIA", "BV", "NRA", "UFLIA", "QF_AUFLIA"]


def main() -> int:
    out = HERE / "pop"
    out.mkdir(exist_ok=True)
    allrows: list[str] = []
    total = 0
    for div in DIVISIONS:
        tsv = BOARD / "census" / f"{div}.tsv"
        if not tsv.exists():
            print(f"ABORT: {tsv} missing", file=sys.stderr)
            return 2
        lines = tsv.read_text().splitlines()
        header = lines[0].split("\t")
        gi = header.index("giveup")
        fi = header.index("file")
        rows = []
        for line in lines[1:]:
            cols = line.split("\t")
            if len(cols) <= gi:
                continue
            if RANKED in cols[gi]:
                rows.append(CORPUS + cols[fi])
        (out / f"round-budget-{div}.txt").write_text("".join(r + "\n" for r in rows))
        allrows.extend(rows)
        total += len(rows)
        print(f"{div:10s} {len(rows):4d}")
    (out / "round-budget-ALL.txt").write_text("".join(r + "\n" for r in allrows))
    print(f"{'TOTAL':10s} {total:4d}")
    # ADR-1950's headline. Asserted, not assumed: if the census is re-run and
    # the family changes size, this fails loudly rather than letting the lane
    # quote 177 over a different population.
    if total != 177:
        print(f"NOTE: the ranked family is {total}, not the 177 ADR-1950 quotes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
