#!/usr/bin/env python3
"""Merge the twelve census shards per division into one committed rows file.

Strips the shared corpus prefix and collapses identical repeated `C` lines to a
count -- the datatype route is entered once per equality encoding and once per
dispatch rung, which repeats the same classification verbatim and would
otherwise make the committed rows tens of megabytes.

Usage: collect-census.py <shard-dir> <out-dir>
"""

import collections
import os
import sys

PREFIX = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVS = ["AUFDTLIRA", "UFDTLIRA", "UFDT"]


def main() -> int:
    src, dst = sys.argv[1], sys.argv[2]
    os.makedirs(dst, exist_ok=True)
    for div in DIVS:
        files = {}
        order = []
        for k in range(12):
            p = os.path.join(src, f"{div}.s{k}.tsv")
            if not os.path.exists(p):
                print(f"MISSING {p}", file=sys.stderr)
                continue
            for line in open(p):
                parts = line.rstrip("\n").split("\t")
                if parts[0] == "F":
                    path = parts[1].replace(PREFIX, "")
                    if path not in files:
                        order.append(path)
                        files[path] = {"F": None, "C": collections.Counter()}
                    files[path]["F"] = (parts[2], parts[3])
                elif parts[0] == "C":
                    path = parts[1].replace(PREFIX, "")
                    if path not in files:
                        order.append(path)
                        files[path] = {"F": None, "C": collections.Counter()}
                    files[path]["C"][parts[2]] += 1
        out = os.path.join(dst, f"{div}.tsv")
        with open(out, "w") as fh:
            fh.write(f"# corpus prefix stripped from every path: {PREFIX}\n")
            fh.write("# F\t<file>\t<verdict>\t<give-up detail>\n")
            fh.write("# C\t<file>\t<repeat count>\t<DTRES-CENSUS line>\n")
            for path in sorted(order):
                v, g = files[path]["F"] or ("unknown", "none")
                fh.write(f"F\t{path}\t{v}\t{g}\n")
                for line, n in sorted(files[path]["C"].items()):
                    fh.write(f"C\t{path}\t{n}\t{line}\n")
        print(f"{div}: {len(order)} files -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
