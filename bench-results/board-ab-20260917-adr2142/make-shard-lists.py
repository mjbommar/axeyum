#!/usr/bin/env python3
"""Build the four shard lists for the ADR-2142 board A/B.

The population is bench-results/parity-lists/<div>.txt for the 16 board
divisions (200 corpus paths each). Files are interleaved ACROSS divisions:
file i of division j (in board order) goes to shard (i + j) % 4, and each
shard's list is ordered by i then j. So each shard holds 800 files, 50 per
division, every division appears in every shard, and consecutive files in a
shard come from different divisions -- a partial read of any shard is a
sample of the board, not a prefix of one division. (The first draft used
g = i * 16 + j and g % 4, which -- 16 being a multiple of 4 -- gave each
shard exactly four divisions; the per-division count assertion below caught
it.)

Usage: make-shard-lists.py <repo-root> <out-dir>
"""

import hashlib
import sys
from pathlib import Path

DIVS = (
    "QF_ABV QF_BV QF_DT QF_FP QF_IDL QF_LIA QF_LRA QF_NIA "
    "QF_NRA QF_RDL QF_S QF_SLIA QF_UF QF_UFLIA QF_UFLRA UF"
).split()
SHARDS = 4


def main() -> int:
    root = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    lists = {}
    for d in DIVS:
        p = root / "bench-results" / "parity-lists" / f"{d}.txt"
        rows = [l.strip() for l in p.read_text().splitlines() if l.strip()]
        if len(rows) != 200:
            print(f"ABORT: {p} has {len(rows)} rows, expected 200")
            return 2
        if len(set(rows)) != 200:
            print(f"ABORT: {p} has duplicate rows")
            return 2
        digest = hashlib.sha256(p.read_bytes()).hexdigest()[:12]
        print(f"{d}\t200\tsha256={digest}")
        lists[d] = rows
    shards = [[] for _ in range(SHARDS)]
    for i in range(200):
        for j, d in enumerate(DIVS):
            shards[(i + j) % SHARDS].append(lists[d][i])
    for k, rows in enumerate(shards):
        (out / f"shard{k}.txt").write_text("\n".join(rows) + "\n")
        per_div = {d: sum(1 for r in rows if f"/{d}/" in r) for d in DIVS}
        assert all(v == 50 for v in per_div.values()), per_div
        print(f"shard{k}\t{len(rows)} files\t50 per division")
    return 0


if __name__ == "__main__":
    sys.exit(main())
