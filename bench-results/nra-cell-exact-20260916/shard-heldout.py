#!/usr/bin/env python3
"""Stride the held-out list into four shards, the way the pinned lists are.

A STRIDE and not a block split, deliberately: the corpus lists are path-sorted,
so a block split puts one family entirely on one core and an A/B's per-core
timing frame stops being comparable across shards. The stride is also how
ADR-2121's committed `shard<N>-<div>.txt` files were made, so the two sweeps
share a frame.

Prints the shard sizes and refuses if they do not sum to the input, because a
silently dropped file is a shorter denominator reported as the same measurement.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list", required=True)
    ap.add_argument("--out-prefix", required=True)
    ap.add_argument("--shards", type=int, default=4)
    args = ap.parse_args()

    rows = [ln.strip() for ln in Path(args.list).read_text().splitlines() if ln.strip()]
    total = 0
    for i in range(args.shards):
        part = rows[i :: args.shards]
        out = Path(f"{args.out_prefix}{i}.txt")
        out.write_text("".join(f"{p}\n" for p in part), encoding="utf-8")
        print(f"shard{i}: {len(part)} -> {out}")
        total += len(part)
    if total != len(rows):
        print(f"ABORT: shards sum to {total}, input has {len(rows)}")
        return 1
    print(f"OK: {total} files across {args.shards} shards")
    return 0


if __name__ == "__main__":
    sys.exit(main())
