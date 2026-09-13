#!/usr/bin/env python3
"""Merge a division's census shards and ABORT unless they cover the pinned list
exactly.

Re-sharding, a re-launch, or a shard that died mid-list all shrink a denominator
silently.  The merge is the only place that can see the whole set, so the
coverage check lives here and its exit status depends on the finding.
"""

import sys
import csv
import pathlib


# A `qtrace` cell can exceed csv's 128 KiB default field limit -- one AUFLIA
# file emits a rung trail that long. The default raises `_csv.Error` and the
# merge ABORTS, which is loud and therefore fine; silently truncating would
# not be.
csv.field_size_limit(1 << 24)


def main(argv: list[str]) -> int:
    if len(argv) != 4:
        print("usage: merge-division.py <div> <pinned-list> <shard-dir>", file=sys.stderr)
        return 2
    div, pinned_path, shard_dir = argv[1], argv[2], pathlib.Path(argv[3])

    # The pinned lists hold ABSOLUTE paths; a census row key is the path
    # RELATIVE to the corpus root, because basenames collide across
    # directories in these corpora and the absolute form is not diffable.
    corpus = ("/nas3/data/axeyum/corpus/smtlib-2024/"
              "non-incremental/non-incremental/")
    pinned = [l.strip().removeprefix(corpus) for l in open(pinned_path) if l.strip()]
    shards = sorted(shard_dir.glob(f"{div}.shard*.tsv"))
    if not shards:
        print(f"ABORT {div}: no shards in {shard_dir}")
        return 3

    rows: dict[str, dict] = {}
    header = None
    dup = []
    for s in shards:
        with open(s) as fh:
            rd = csv.DictReader(fh, delimiter="\t")
            header = rd.fieldnames
            for r in rd:
                if r["file"] in rows:
                    dup.append(r["file"])
                rows[r["file"]] = r

    missing = [p for p in pinned if p not in rows]
    extra = [f for f in rows if f not in set(pinned)]
    print(f"{div}: {len(shards)} shards, {len(rows)} rows, pinned {len(pinned)}")
    if dup:
        print(f"ABORT {div}: {len(dup)} duplicate rows across shards, e.g. {dup[:3]}")
        return 4
    if missing:
        print(f"ABORT {div}: {len(missing)} pinned files have no row, e.g. {missing[:3]}")
        return 5
    if extra:
        print(f"ABORT {div}: {len(extra)} rows are not on the pinned list, e.g. {extra[:3]}")
        return 6

    out = shard_dir / f"{div}.tsv"
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=header, delimiter="\t", lineterminator="\n")
        w.writeheader()
        for p in pinned:  # pinned-list order, so the artifact is diffable
            w.writerow(rows[p])
    print(f"MERGE-OK {div} {len(pinned)} rows -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
