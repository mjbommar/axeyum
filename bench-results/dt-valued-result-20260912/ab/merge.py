#!/usr/bin/env python3
"""Merge the twelve A/B shards per division into one committed rows file.

Usage: merge.py <shard-dir> <out-dir>
"""

import os
import sys

DIVS = ["AUFDTLIRA", "UFDTLIRA", "UFDT", "QF_DT", "UF"]
HEAD = "file\tbase\tbase_s\tbase_giveup\tnew\tnew_s\tnew_giveup\tstatus\n"


def main() -> int:
    src, dst = sys.argv[1], sys.argv[2]
    os.makedirs(dst, exist_ok=True)
    for div in DIVS:
        seen = {}
        for k in range(12):
            p = os.path.join(src, f"{div}.s{k}.tsv")
            if not os.path.exists(p):
                print(f"MISSING {p}", file=sys.stderr)
                continue
            with open(p, encoding="utf-8", errors="replace") as fh:
                head = fh.readline()
                assert head == HEAD, (p, head)
                for line in fh:
                    parts = line.rstrip("\n").split("\t")
                    if len(parts) != 8:
                        continue
                    seen[parts[0]] = line
        out = os.path.join(dst, f"{div}.tsv")
        with open(out, "w", encoding="utf-8") as fh:
            fh.write(HEAD)
            for f in sorted(seen):
                fh.write(seen[f])
        print(f"{div}: {len(seen)} rows -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
