"""Merge one division's two shards back into pinned-list order, and emit the
winnable set (we `unknown`, a reference decides) for the census.

    python3 merge-division.py ALIA

The shards are NR%2 through the pinned list, so re-ordering by the pinned list
means the committed TSV does not encode the shard split.  It ABORTS if the two
shards together do not cover the pinned list exactly -- a short shard must not
silently become a smaller denominator.

FP's pinned list is `FP-fullspan.txt`; the harness tag is `FP`.  STEM holds
that one mapping.
"""

import pathlib
import sys

LANE = pathlib.Path(__file__).resolve().parent
OUT = pathlib.Path("/nas3/data/axeyum/harness/tier1-divisions/out")
LISTS = LANE.parent / "parity-lists"
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DECIDED = {"sat", "unsat"}
STEM = {"FP": "FP-fullspan"}


def main(div):
    pinned = [
        ln[len(CORPUS):]
        for ln in (LISTS / f"{STEM.get(div, div)}.txt").read_text().rstrip("\n").split("\n")
    ]
    # ANY number of shards, discovered rather than assumed.  Seven divisions
    # over three boxes does not divide and the divisions are not equally fast
    # (UFNIA ran ~1.7 min/file where AUFLIRA ran 0.1 s on most rows), so slow
    # ones get re-split across whatever cores are free.  Hardcoding s0/s1 here
    # would have silently merged 2 of 6 shards and produced a 33-row "200-file"
    # board -- the coverage assertion below is what makes the discovery safe.
    parts = sorted(OUT.glob(f"{div}.s*.tsv"))
    if not parts:
        print(f"ABORT {div}: no shard files ({OUT}/{div}.s*.tsv) -- board DID NOT RUN")
        return 2
    head, seen = None, {}
    for p in parts:
        lines = p.read_text().rstrip("\n").split("\n")
        head = lines[0]
        for ln in lines[1:]:
            key = ln.split("\t")[0]
            if key in seen:
                print(f"ABORT: duplicate row key {key}")
                return 2
            seen[key] = ln

    missing = [f for f in pinned if f not in seen]
    extra = [k for k in seen if k not in pinned]
    if missing or extra:
        print(f"INCOMPLETE {div}: have {len(seen)} of {len(pinned)}; "
              f"missing {len(missing)}, extra {len(extra)}")
        if extra:
            print(f"  ABORT: rows not in the pinned list: {extra[:3]}")
            return 2
        return 1

    (LANE / f"{div}.tsv").write_text(
        head + "\n" + "".join(seen[f] + "\n" for f in pinned)
    )

    cols = head.split("\t")
    win = []
    for f in pinned:
        r = dict(zip(cols, seen[f].split("\t")))
        if r["axeyum"] not in DECIDED and (
            r["z3"] in DECIDED or r["cvc5"] in DECIDED
        ):
            win.append(f)
    wd = LANE / "winnable"
    wd.mkdir(exist_ok=True)
    (wd / f"{div}.txt").write_text("".join(f"{CORPUS}{f}\n" for f in win))
    print(f"MERGED {div}: {len(pinned)} rows from {len(parts)} shard(s)"
          f" -> {div}.tsv; winnable {len(win)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
