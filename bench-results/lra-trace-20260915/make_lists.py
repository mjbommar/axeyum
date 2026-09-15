#!/usr/bin/env python3
"""Emit a file list from the bucket table, selected by channel and optionally prose.

The prose filter exists because the TYPED decline name does not separate this
division at all: ADR-2111 measured all 36 `budget` rows carrying
`Budget::Other`, so selecting on the typed channel alone gives one bucket of 36
and selecting a *sub*-bucket means matching the producer's sentence. That is a
known-bad authority (three ADRs record what re-parsing prose costs), so the
match is a literal PREFIX rather than a pattern, the prefix is echoed on stderr,
and the row count is printed — a filter that silently matched nothing would
otherwise emit an empty list and every downstream measurement would be of the
empty set.

Usage:  make_lists.py <buckets.tsv> <channel> [prose-prefix] > list.txt
"""

from __future__ import annotations

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) not in (3, 4):
        sys.stderr.write(__doc__ or "")
        return 2
    lines = Path(argv[1]).read_text().splitlines()
    head = lines[0].split("\t")
    prefix = argv[3] if len(argv) == 4 else None
    n = 0
    for ln in lines[1:]:
        if not ln:
            continue
        row = dict(zip(head, ln.split("\t"), strict=True))
        if row["channel"] != argv[2]:
            continue
        if prefix is not None and not row["detail"].startswith(prefix):
            continue
        print(row["file"])
        n += 1
    where = f"channel={argv[2]}"
    if prefix is not None:
        where += f" and detail starting {prefix!r}"
    sys.stderr.write(f"make_lists: {n} rows with {where}\n")
    if not n:
        sys.stderr.write(
            "make_lists: ZERO rows matched -- emitting an empty list would make "
            "every downstream number a measurement of the empty set, so this is "
            "an error and not a result\n"
        )
    return 0 if n else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
