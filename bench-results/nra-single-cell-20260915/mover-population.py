#!/usr/bin/env python3
"""Where do the A/B movers sit in the nested populations?

Lane NRA-SINGLE-CELL, ADR-2121.

Four nested sets, and a claim about the route's reach is only meaningful against
a named one:

  83  ADR-2110's undecided QF_NRA files on the 2026-09-15 board
  45  of those, decided by z3's CAD arm and NOT by its linearization arm
  24  of those, inside this slice's declared bounds
  12  of those, actually conjunctive after `let` expansion

A mover outside the 45 is the route reaching past the population that motivated
it. A mover outside the 24 means the ceiling was not a forecast. Both are worth
saying, and neither can be said without this join -- which is why it is a script
and not a sentence.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def read_set(path: Path) -> set[str]:
    return {ln.strip() for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip()}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default="bench-results/nra-single-cell-20260915")
    ap.add_argument("--trace-root", default="bench-results/nra-trace-20260915")
    ap.add_argument("--movers", default="movers-qfnra.txt")
    args = ap.parse_args()

    root = Path(args.root)
    movers = [
        ln.split("\t")[1]
        for ln in (root / args.movers).read_text(encoding="utf-8").splitlines()
        if ln
    ]
    sizing = (root / "sizing-45.tsv").read_text(encoding="utf-8").splitlines()
    in45 = {ln.split("\t")[0] for ln in sizing[1:] if ln}
    in24 = read_set(root / "inbounds-24.txt")
    in12 = read_set(root / "conjunctive-12.txt")
    in83 = read_set(Path(args.trace_root) / "undecided-83.txt")

    # Controls on the populations themselves, so a mislabelled file cannot pass
    # silently: each set must be the size its name claims, and nested.
    for name, s, want in (("83", in83, 83), ("45", in45, 45), ("24", in24, 24), ("12", in12, 12)):
        if len(s) != want:
            print(f"CONTROL FAILED: the '{name}' set has {len(s)} members")
            return 1
    if not (in12 <= in24 <= in45 <= in83):
        print("CONTROL FAILED: the populations are not nested")
        return 1
    print("control: 83 / 45 / 24 / 12, nested\n")

    print(f"{'mover':62s} {'83':>3s} {'45':>3s} {'24':>3s} {'12':>3s}")
    for m in movers:
        print(
            f"{m.split('/')[-1][:62]:62s} "
            f"{int(m in in83):3d} {int(m in in45):3d} {int(m in in24):3d} {int(m in in12):3d}"
        )
    print(
        f"\nof {len(movers)} movers: "
        f"{sum(m in in83 for m in movers)} in the 83, "
        f"{sum(m in in45 for m in movers)} in the 45, "
        f"{sum(m in in24 for m in movers)} in the 24, "
        f"{sum(m in in12 for m in movers)} in the 12"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
