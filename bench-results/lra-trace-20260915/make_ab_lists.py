#!/usr/bin/env python3
"""Build the A/B population: every file of the six LINEAR-ARITHMETIC divisions.

Why all six and not just the treatment division: the simplex ADR-2111 changed is
SHARED. `QF_LRA` is where the change was aimed, `QF_LIA`/`QF_UFLRA`/`QF_UFLIA`
reach the same `Tableau` through other front ends, and `QF_IDL`/`QF_RDL` are
decided by `dl_online` FIRST -- so they are the arm where a regression would
show up as a route that stopped declining in time, not as a slower simplex. A
treatment-only A/B cannot tell a gain from a reshuffle.

Output is ABSOLUTE paths, which is what `ab-run.sh` consumes (it strips the
corpus root itself). Shards are cut round-robin over the CONCATENATED list, not
per division, so a slow division cannot land entirely on one core pair and be
read as that pair being slow.

Usage:  make_ab_lists.py <board-dir> <corpus-root> <out-dir> <shards>
"""

from __future__ import annotations

import sys
from pathlib import Path

DIVISIONS = ["QF_LRA", "QF_LIA", "QF_UFLRA", "QF_UFLIA", "QF_IDL", "QF_RDL"]


def main(argv: list[str]) -> int:
    if len(argv) != 5:
        sys.stderr.write(__doc__ or "")
        return 2
    board, corpus, out, shards = Path(argv[1]), argv[2], Path(argv[3]), int(argv[4])
    out.mkdir(parents=True, exist_ok=True)
    rows: list[str] = []
    for d in DIVISIONS:
        p = board / f"{d}.tsv"
        lines = p.read_text().splitlines()
        n = 0
        for ln in lines[1:]:
            if not ln:
                continue
            rel = ln.split("\t")[0]
            f = Path(corpus) / rel
            if not f.is_file():
                sys.stderr.write(f"MISSING\t{rel}\n")
                return 2
            rows.append(str(f))
            n += 1
        sys.stderr.write(f"{d}: {n} files\n")
    handles = [open(out / f"ab.{i:02d}.txt", "w") for i in range(shards)]
    try:
        for i, r in enumerate(rows):
            print(r, file=handles[i % shards])
    finally:
        for h in handles:
            h.close()
    sys.stderr.write(f"total {len(rows)} files over {shards} shards\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
