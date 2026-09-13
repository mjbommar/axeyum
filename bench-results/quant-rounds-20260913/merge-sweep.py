#!/usr/bin/env python3
"""Merge the AUFLIA sweep shards into one file, and ABORT on an incomplete set.

The AUFLIA sweep was three overlapping shards (one host had the whole list and
two more picked up its tail), so the merge must dedup by the row KEY and must
refuse to write a smaller denominator than the population — the same rule
`board-six`'s `merge-division.py` enforces, for the same reason: a shard that
died silently otherwise turns into a quietly narrower result.

Usage: merge-sweep.py <population-list> <out.tsv> <shard.tsv>...
"""

import pathlib
import sys

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"


def main(argv: list[str]) -> int:
    if len(argv) < 4:
        print(__doc__, file=sys.stderr)
        return 2
    want = [
        ln.removeprefix(CORPUS)
        for ln in pathlib.Path(argv[1]).read_text().splitlines()
        if ln.strip()
    ]
    out = pathlib.Path(argv[2])

    header: str | None = None
    rows: dict[str, str] = {}
    for shard in argv[3:]:
        p = pathlib.Path(shard)
        if not p.exists():
            print(f"ABORT: shard {shard} missing", file=sys.stderr)
            return 2
        lines = p.read_text().splitlines()
        if not lines:
            print(f"ABORT: shard {shard} is empty", file=sys.stderr)
            return 2
        if header is None:
            header = lines[0]
        elif lines[0] != header:
            print(f"ABORT: shard {shard} has a different header", file=sys.stderr)
            return 2
        for ln in lines[1:]:
            if ln.strip():
                # First writer wins; a duplicated row means two shards measured
                # the same file, which is fine and is reported.
                rows.setdefault(ln.split("\t")[0], ln)

    missing = [f for f in want if f not in rows]
    if missing:
        print(f"ABORT: {len(missing)} of {len(want)} population rows have no shard row:",
              file=sys.stderr)
        for f in missing[:5]:
            print(f"  {f}", file=sys.stderr)
        return 2

    assert header is not None
    out.write_text(header + "\n" + "".join(rows[f] + "\n" for f in want))
    print(f"merged {len(want)} rows from {len(argv) - 3} shards -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
