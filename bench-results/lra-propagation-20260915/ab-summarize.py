#!/usr/bin/env python3
"""Summarise an ADR-2122 A/B run: net, gains, losses, flips, aborts, soundness.

One row per division, plus the movers. Every number carries its own denominator
-- a division with no rows is reported as **did not run**, never as zero
movement, which is the distinction ADR-2111's own exposure arm had to make
explicitly after reporting four empty divisions.

Columns of the input TSV (from `ab-run.sh`):

    file  A  A_ms  A_rc  B  B_ms  B_rc  first  status

`A` and `B` are the verdicts (`sat` / `unsat` / `unknown` / `none`), `A_rc` and
`B_rc` the EXIT STATUSES, kept separate because ADR-2045 measured `losses=0` by
verdict with five new aborts underneath it.

Usage: ab-summarize.py [--movers-out FILE] <division>=<tsv> [...]

`--movers-out` writes the moved rows' corpus-relative paths, one per line, for
`recheck-movers.sh`. It is written even when EMPTY, so "no movers" is a file a
successor can see rather than an absence they have to infer.
"""

from __future__ import annotations

import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}


def load(path: Path) -> list[dict[str, str]]:
    lines = path.read_text().splitlines()
    if not lines:
        return []
    head = lines[0].split("\t")
    return [
        dict(zip(head, ln.split("\t"), strict=False)) for ln in lines[1:] if ln.strip()
    ]


def main(argv: list[str]) -> int:
    movers_out: Path | None = None
    args = list(argv[1:])
    if args and args[0] == "--movers-out":
        movers_out = Path(args[1])
        args = args[2:]
    if not args:
        sys.stderr.write(__doc__ or "")
        return 2
    argv = [argv[0], *args]

    print(
        f"{'division':12s} {'rows':>5s} {'A':>4s} {'B':>4s} {'net':>5s} "
        f"{'gain':>5s} {'LOSS':>5s} {'FLIP':>5s} {'A_rc!=0':>8s} {'B_rc!=0':>8s} "
        f"{'cmp':>5s} {'DIS':>4s}"
    )
    movers: list[str] = []
    dis_rows: list[str] = []
    totals = [0] * 10
    any_rows = False
    for spec in argv[1:]:
        div, _, p = spec.partition("=")
        path = Path(p)
        rows = load(path) if path.exists() else []
        if not rows:
            print(f"{div:12s} {0:>5d}   --   --    --    --    --    --       --       --    -- did not run")
            continue
        any_rows = True
        a_dec = sum(1 for r in rows if r["A"] in DECIDED)
        b_dec = sum(1 for r in rows if r["B"] in DECIDED)
        gain = [r for r in rows if r["A"] not in DECIDED and r["B"] in DECIDED]
        loss = [r for r in rows if r["A"] in DECIDED and r["B"] not in DECIDED]
        flip = [
            r
            for r in rows
            if r["A"] in DECIDED and r["B"] in DECIDED and r["A"] != r["B"]
        ]
        arc = sum(1 for r in rows if r["A_rc"] not in ("0",))
        brc = sum(1 for r in rows if r["B_rc"] not in ("0",))
        # Soundness against the file's own `:status`, over the rows where BOTH a
        # declared status and a decided verdict exist -- the comparable
        # denominator, printed beside the count rather than implied.
        cmp_rows = [
            r for r in rows if r["status"] in DECIDED and r["B"] in DECIDED
        ]
        dis = [r for r in cmp_rows if r["B"] != r["status"]]
        dis_rows += [f"{div}\t{r['file']}\tdeclared={r['status']}\tB={r['B']}" for r in dis]
        movers += [f"{div}\tGAIN\t{r['file']}\tA={r['A']}\tB={r['B']}" for r in gain]
        movers += [f"{div}\tLOSS\t{r['file']}\tA={r['A']}\tB={r['B']}" for r in loss]
        movers += [f"{div}\tFLIP\t{r['file']}\tA={r['A']}\tB={r['B']}" for r in flip]
        vals = [
            len(rows), a_dec, b_dec, b_dec - a_dec, len(gain), len(loss), len(flip),
            arc, brc, len(cmp_rows),
        ]
        totals = [t + v for t, v in zip(totals, vals, strict=True)]
        print(
            f"{div:12s} {len(rows):5d} {a_dec:4d} {b_dec:4d} {b_dec - a_dec:+5d} "
            f"{len(gain):5d} {len(loss):5d} {len(flip):5d} {arc:8d} {brc:8d} "
            f"{len(cmp_rows):5d} {len(dis):4d}"
        )
    if any_rows:
        print(
            f"{'TOTAL':12s} {totals[0]:5d} {totals[1]:4d} {totals[2]:4d} "
            f"{totals[3]:+5d} {totals[4]:5d} {totals[5]:5d} {totals[6]:5d} "
            f"{totals[7]:8d} {totals[8]:8d} {totals[9]:5d} {len(dis_rows):4d}"
        )
    if movers_out is not None:
        movers_out.write_text(
            "".join(f"{m.split(chr(9))[2]}\n" for m in movers)
        )
        print(f"mover paths -> {movers_out} ({len(movers)} rows)")
    print()
    if movers:
        print(f"MOVERS ({len(movers)}) -- each needs a 3x recheck before it counts:")
        for m in movers:
            print("  " + m)
    else:
        print(
            "MOVERS: 0. The 3x recheck therefore has a COMPARABLE DENOMINATOR OF 0 "
            "-- that is the absence of anything to re-check, not evidence of stability."
        )
    if dis_rows:
        print()
        print(f"SOUNDNESS DISAGREEMENTS ({len(dis_rows)}):")
        for d in dis_rows:
            print("  " + d)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
