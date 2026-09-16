#!/usr/bin/env python3
"""Draw the `QF_ABV` CONTROL list — 200 files, seeded, reproducible.

`QF_ABV` is the control division for ADR-2135: it is a datatype-free SMT-LIB
logic, so `register_datatype` is never reached and `field_is_opaque` can never
fire. A move here would not be a capability, it would be evidence the lever
changed something it has no business touching.

There is no pinned `QF_ABV` list under
`/nas3/data/axeyum/harness/route-ownership/ablists/` (it holds nine divisions,
none of them `QF_ABV`), so this is a FRESH seeded draw rather than a pinned
list, and this docstring is where that is said instead of it being quietly
implied by a file of paths.

The seed is a constant in this source, and the drawn list is committed beside
it, so the draw is reproducible and cannot be re-rolled after a result.
Candidates are enumerated in sorted order before sampling, so the draw does not
depend on directory iteration order.

Usage (run on a host that can see the corpus, e.g. s7):
    python3 draw-qfabv-control.py > ab-QF_ABV.paths
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

#: The corpus root the harness runs against.
CORPUS = Path("/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental")

#: **The seed.** A constant in the source, not a command-line default.
SEED = 21350916

N = 200


def main() -> int:
    root = CORPUS / "QF_ABV"
    if not root.is_dir():
        sys.stderr.write(f"ABORT: {root} is not a directory\n")
        return 2
    candidates = sorted(str(p) for p in root.rglob("*.smt2"))
    if len(candidates) < N:
        sys.stderr.write(f"ABORT: only {len(candidates)} candidates, need {N}\n")
        return 3
    sys.stderr.write(f"pool={len(candidates)} seed={SEED} n={N}\n")
    drawn = random.Random(SEED).sample(candidates, N)
    for path in sorted(drawn):
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
