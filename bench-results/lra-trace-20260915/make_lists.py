#!/usr/bin/env python3
"""Emit a file list from the bucket table, selected by channel.

Usage:  make_lists.py <buckets.tsv> <channel> > list.txt
"""

from __future__ import annotations

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    lines = Path(argv[1]).read_text().splitlines()
    head = lines[0].split("\t")
    n = 0
    for ln in lines[1:]:
        if not ln:
            continue
        row = dict(zip(head, ln.split("\t"), strict=True))
        if row["channel"] == argv[2]:
            print(row["file"])
            n += 1
    sys.stderr.write(f"make_lists: {n} rows with channel={argv[2]}\n")
    return 0 if n else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
