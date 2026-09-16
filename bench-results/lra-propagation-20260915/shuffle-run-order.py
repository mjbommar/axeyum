#!/usr/bin/env python3
"""Fix the RUN ORDER of an A/B list so that any prefix is a random subsample.

# Why this exists

The A/B lists are in path order. `QF_LRA-heldout.txt` comes out of ADR-2106's
`draw-heldout.py` sorted; the pinned list comes out of the committed board in an
order that is also family-clustered at the head. Either way the first *k* rows
of a run are **one or two benchmark FAMILIES**, not a sample of the division.

That matters because a sweep at 24 s per arm on two pinned core pairs does not
always finish 200 files, and a partial run then has to be reported. A prefix of
a path-ordered list cannot show an effect that is not uniform over path order --
reporting one as "n of 200 so far, net +0" publishes a null that the data cannot
support. (This repository has done exactly that twice.)

Shuffling the ORDER changes nothing about WHICH files are in the population: the
set is byte-identical, and for the held-out draw that set is the preregistered
one. It only makes a truncated run a uniform random subsample of it.

# The seed

`SEED` is a constant in this source, not a command-line default, so the order
cannot be re-rolled quietly after a result. Changing it is a diff.

Usage:  shuffle-run-order.py <list.txt> [...]
        (rewrites each file in place, and prints the set digest before/after
        so "same set, different order" is checked rather than asserted)
"""

from __future__ import annotations

import hashlib
import random
import sys
from pathlib import Path

#: A constant in the source. See the module docstring.
SEED = 20260915


def digest(rows: list[str]) -> str:
    """Order-INDEPENDENT digest of the set, so a reorder is provably not an edit."""
    return hashlib.sha256("\n".join(sorted(rows)).encode()).hexdigest()[:16]


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        sys.stderr.write(__doc__ or "")
        return 2
    for name in argv[1:]:
        path = Path(name)
        rows = [r for r in path.read_text().splitlines() if r.strip()]
        before = digest(rows)
        # A per-file seed derived from the constant and the file's own name, so
        # two lists do not get the same permutation by accident.
        rng = random.Random(f"{SEED}:{path.name}")
        shuffled = list(rows)
        rng.shuffle(shuffled)
        after = digest(shuffled)
        if before != after:
            raise SystemExit(f"ABORT: {path} set changed: {before} -> {after}")
        path.write_text("".join(f"{r}\n" for r in shuffled))
        moved = sum(1 for a, b in zip(rows, shuffled, strict=True) if a != b)
        print(f"{path.name}: {len(rows)} rows, set digest {before} unchanged, {moved} positions moved")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
