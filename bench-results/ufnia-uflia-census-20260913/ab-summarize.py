"""Merge an interleaved A/B's shards and report gain / loss / flips.

Usage:  python3 ab-summarize.py <arm-dir> <div> [<div> ...]

The three numbers that matter and the order they must be read in:

  FLIP   a `sat` that became `unsat` or the reverse.  A soundness event.  It is
         printed FIRST and its presence sets a non-zero exit status, because a
         gain column is worth nothing beside one.
  LOSS   a file the base arm decides and the arm does not.  A scheduling change
         that reallocates a clock BUYS with somebody's time; a report that
         prints only the gain is describing half a measurement.
  GAIN   the reverse.

ABORTS unless the shards cover the pinned list exactly -- a shard that died
mid-list shrinks the denominator silently, and a per-file A/B's denominator is
what the whole comparison rests on.
"""

import collections
import csv
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
DECIDED = ("sat", "unsat")


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print("usage: ab-summarize.py <arm-dir> <div> [<div> ...]", file=sys.stderr)
        return 2
    arm_dir = pathlib.Path(argv[1])
    rc = 0
    for div in argv[2:]:
        shards = sorted(arm_dir.glob(f"{div}.shard*.tsv"))
        if not shards:
            print(f"== {div}: DID NOT RUN")
            rc = max(rc, 1)
            continue
        rows: dict[str, dict] = {}
        header = None
        for s in shards:
            with open(s) as fh:
                rd = csv.DictReader(fh, delimiter="\t")
                header = rd.fieldnames
                for r in rd:
                    rows[r["file"]] = r
        pinned = [
            l.strip().removeprefix(
                "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
            )
            for l in open(HERE.parent / "parity-lists" / f"{div}.txt")
            if l.strip()
        ]
        missing = [p for p in pinned if p not in rows]
        if missing:
            print(f"ABORT {div}: {len(missing)} pinned files have no A/B row,"
                  f" e.g. {missing[:2]}")
            return 3
        out = arm_dir / f"{div}.tsv"
        with open(out, "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=header, delimiter="\t", lineterminator="\n")
            w.writeheader()
            for p in pinned:
                w.writerow(rows[p])

        rs = [rows[p] for p in pinned]
        base = sum(r["base"] in DECIDED for r in rs)
        arm = sum(r["arm"] in DECIDED for r in rs)
        flips = [r for r in rs if r["base"] in DECIDED and r["arm"] in DECIDED
                 and r["base"] != r["arm"]]
        losses = [r for r in rs if r["base"] in DECIDED and r["arm"] not in DECIDED]
        gains = [r for r in rs if r["base"] not in DECIDED and r["arm"] in DECIDED]

        print(f"== {div}  n={len(rs)}   base {base}   arm {arm}   net {arm - base:+d}")
        print(f"   sat<->unsat FLIPS: {len(flips)}"
              + ("   <-- SOUNDNESS EVENT, read this before the gain column" if flips else ""))
        for r in flips:
            print(f"      !! {r['file']} base={r['base']} arm={r['arm']} status={r['status']}")
            rc = max(rc, 4)
        print(f"   LOSS (base decides, arm does not): {len(losses)}")
        for r in losses:
            print(f"      - {r['base']:5s} {r['base_ms']:>6s} ms  status={r['status']:7s}"
                  f" {r['file']}")
        print(f"   GAIN (arm decides, base does not): {len(gains)}")
        for r in gains:
            print(f"      + {r['arm']:5s} {r['arm_ms']:>6s} ms  status={r['status']:7s}"
                  f" {r['file']}")
        for name, key in (("base", "base_rc"), ("arm", "arm_rc")):
            bad = collections.Counter(r[key] for r in rs if r[key] != "0")
            print(f"   {name} non-zero rc: {dict(bad) if bad else 'none'}")
        # Arm order is alternated per file; if it mattered, the two halves would
        # disagree.  Printed so the reader can see it did not, rather than
        # taking the protocol's word for it.
        for first in ("base", "arm"):
            half = [r for r in rs if r["first"] == first]
            hb = sum(r["base"] in DECIDED for r in half)
            ha = sum(r["arm"] in DECIDED for r in half)
            print(f"   first={first:4s} n={len(half):3d}  base {hb:3d}  arm {ha:3d}")
        print()
    return rc


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
