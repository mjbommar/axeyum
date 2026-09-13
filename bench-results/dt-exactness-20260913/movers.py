#!/usr/bin/env python3
"""Write the MOVED rows of an A/B out for re-checking, and the gains out for
reference verification.

Two files, because they answer different questions and [ADR-1976] says so:

  <div>.movers.txt   every row where the two arms differ IN EITHER DIRECTION --
                     gains AND losses. A report that re-checks only its gains
                     is re-checking the half it wants to keep.
  <div>.gains.txt    the gains alone, for `verify-new-verdicts.sh`, which is
                     strong evidence for an `unsat` and weak for a `sat`.

Usage: movers.py <ab-dir> <div> [<div> ...]
"""

import csv
import pathlib
import sys

DECIDED = ("sat", "unsat")


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print("usage: movers.py <ab-dir> <div> [<div> ...]", file=sys.stderr)
        return 2
    ab = pathlib.Path(argv[1])
    for div in argv[2:]:
        src = ab / f"{div}.tsv"
        if not src.exists():
            print(f"{div}: DID NOT RUN ({src} missing)")
            return 3
        rows = list(csv.DictReader(open(src), delimiter="\t"))
        movers = [r for r in rows
                  if (r["base"] in DECIDED) != (r["arm"] in DECIDED)
                  or (r["base"] in DECIDED and r["arm"] in DECIDED
                      and r["base"] != r["arm"])]
        gains = [r for r in rows if r["base"] not in DECIDED and r["arm"] in DECIDED]
        losses = [r for r in rows if r["base"] in DECIDED and r["arm"] not in DECIDED]
        with open(ab / f"{div}.movers.txt", "w") as fh:
            for r in movers:
                fh.write(f"{r['file']}\t{r['base']}\t{r['arm']}\n")
        with open(ab / f"{div}.gains.txt", "w") as fh:
            for r in gains:
                fh.write(f"{r['file']}\t{r['arm']}\n")
        print(f"{div}: n={len(rows)} movers={len(movers)} "
              f"gains={len(gains)} losses={len(losses)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
