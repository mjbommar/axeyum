#!/usr/bin/env python3
"""Read the ADR-2121 A/B shards and report what moved.

Lane NRA-SINGLE-CELL. Three things the raw shard files do not say on their own:

* a GAIN and a LOSS are not symmetric with a `none` (no verdict token at all):
  `none` is a run that produced nothing, `unknown` is one that reported it could
  not decide, and collapsing them reads an absent arm as a capability statement.
  They are counted apart here for the same reason ADR-2110's join counted them
  apart.
* a `sat` <-> `unsat` FLIP is not a gain or a loss, it is a soundness event, and
  it is reported on its own line so it cannot be netted away.
* the declared `:status` of each benchmark is an independent adjudicator, and a
  disagreement against it is reported with its DENOMINATOR -- "0 disagreements"
  over 4 comparable verdicts is not the same claim as over 234.

Exit status is non-zero on any flip or any `:status` disagreement, so this is a
check and not a printout.
"""

from __future__ import annotations

import argparse
import collections
import re
from pathlib import Path

DECIDED = ("sat", "unsat")
STATUS_RE = re.compile(rb"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def read_shards(root: Path, division: str, tag: str = "") -> list[dict[str, str]]:
    prefix = f"ab-{tag}-" if tag else "ab-"
    rows: list[dict[str, str]] = []
    for path in sorted(root.glob(f"{prefix}{division}-shard*.tsv")):
        lines = path.read_text(encoding="utf-8").splitlines()
        if not lines:
            continue
        header = lines[0].split("\t")
        for ln in lines[1:]:
            if ln:
                rows.append(dict(zip(header, ln.split("\t"), strict=False)))
    return rows


def declared_status(corpus_root: Path, rel: str) -> str | None:
    try:
        blob = (corpus_root / rel).read_bytes()
    except OSError:
        return None
    m = STATUS_RE.search(blob)
    if not m:
        return None
    s = m.group(1).decode()
    return s if s in DECIDED else None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    ap.add_argument("--divisions", nargs="+", required=True)
    ap.add_argument(
        "--corpus-root",
        default="/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental",
    )
    ap.add_argument("--movers", help="write the mover list here")
    ap.add_argument(
        "--tag",
        default="",
        help="arm tag in the shard filenames (`ab-<tag>-<division>-shard<N>.tsv`); empty for the original untagged sweep",
    )
    args = ap.parse_args()

    root = Path(args.root)
    corpus = Path(args.corpus_root)
    arm_label = args.tag or "single-cell"
    rc = 0
    movers: list[tuple[str, str, str, str]] = []

    for div in args.divisions:
        rows = read_shards(root, div, args.tag)
        if not rows:
            print(f"\n== {div}: NO SHARD ROWS -- the sweep did not run ==")
            rc = 1
            continue
        a_dec = sum(1 for r in rows if r["A"] in DECIDED)
        b_dec = sum(1 for r in rows if r["B"] in DECIDED)
        gains = [r for r in rows if r["A"] not in DECIDED and r["B"] in DECIDED]
        losses = [r for r in rows if r["A"] in DECIDED and r["B"] not in DECIDED]
        flips = [
            r
            for r in rows
            if r["A"] in DECIDED and r["B"] in DECIDED and r["A"] != r["B"]
        ]
        none_rows = sum(1 for r in rows if r["A"] == "none" or r["B"] == "none")

        print(f"\n== {div} ==")
        print(f"  rows                       {len(rows)}")
        print(f"  A (default)                {a_dec}")
        print(f"  B ({arm_label})".ljust(29) + f"{b_dec}")
        print(f"  net                        {b_dec - a_dec:+d}")
        print(f"  gains / losses / flips     {len(gains)} / {len(losses)} / {len(flips)}")
        print(f"  rows where an arm produced no verdict token   {none_rows}")

        comparable = 0
        disagree = []
        for r in rows:
            st = declared_status(corpus, r["file"])
            if st is None:
                continue
            for arm in ("A", "B"):
                if r[arm] in DECIDED:
                    comparable += 1
                    if r[arm] != st:
                        disagree.append((r["file"], arm, r[arm], st))
        print(f"  vs declared :status        {len(disagree)} disagreements over "
              f"{comparable} comparable verdicts")
        for f, arm, got, want in disagree:
            print(f"    DISAGREE {arm} said {got}, :status says {want}   {f}")
            rc = 1
        for r in flips:
            print(f"    FLIP A={r['A']} B={r['B']}   {r['file']}")
            rc = 1

        wall_a = sum(int(r["A_ms"]) for r in rows if r["A_ms"].isdigit())
        wall_b = sum(int(r["B_ms"]) for r in rows if r["B_ms"].isdigit())
        print(f"  wall clock                 A {wall_a / 1000:.0f} s, B {wall_b / 1000:.0f} s")

        for r in gains:
            print(f"    GAIN   A={r['A']} -> B={r['B']}   {r['file']}")
            movers.append((div, r["file"], r["A"], r["B"]))
        for r in losses:
            print(f"    LOSS   A={r['A']} -> B={r['B']}   {r['file']}")
            movers.append((div, r["file"], r["A"], r["B"]))

        # The control division must not move at all. Say so explicitly rather
        # than leaving a reader to infer it from a zero.
        if div == "qflra":
            verdict = "as expected" if not (gains or losses or flips) else "UNEXPECTED"
            print(f"  CONTROL: the linear division moved {len(gains) + len(losses)} "
                  f"rows -- {verdict}")
            if gains or losses or flips:
                rc = 1

    if args.movers:
        with open(args.movers, "w", encoding="utf-8") as fh:
            for div, f, a, b in movers:
                fh.write(f"{div}\t{f}\t{a}\t{b}\n")
        print(f"\nwrote {args.movers} ({len(movers)} movers)")

    counts = collections.Counter(d for d, _, _, _ in movers)
    print("\nmovers per division: " + (", ".join(f"{k}={v}" for k, v in sorted(counts.items())) or "none"))
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
