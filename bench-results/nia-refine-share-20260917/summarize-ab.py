#!/usr/bin/env python3
"""Coverage, disagreements, `:status` contradictions and raw movers of one
ADR-2148 A/B directory (four `ab-<division>.tsv` from `ab-run-env.sh`).

Exit 1 on a short sweep, a sat/unsat disagreement between the arms, or a
decided verdict that contradicts the benchmark's own `(set-info :status)`;
those are the findings the sweep exists to surface, and a summary that prints
percentages over them is worse than none.

usage: summarize-ab.py <abdir> <listdir> [movers-out]
"""
from __future__ import annotations

import sys
from pathlib import Path

DECIDED = {"sat", "unsat"}
DIVS = [("QF_NIA", "ab-list-QF_NIA.txt"), ("QF_NRA", "ab-list-QF_NRA.txt"),
        ("UFNIA", "ab-list-UFNIA.txt"), ("QF_NIA-heldout", "heldout-QF_NIA.txt")]


def main() -> int:
    abdir, listdir = Path(sys.argv[1]), Path(sys.argv[2])
    movers_out = Path(sys.argv[3]) if len(sys.argv) > 3 else None
    bad = False
    movers: list[str] = []
    print(f"{'division':16} {'list':>5} {'rows':>5} {'A':>4} {'B':>4} {'dis':>4} {'status-contra':>13} gains losses")
    for div, lst in DIVS:
        expected = [l for l in (listdir / lst).read_text().split("\n") if l]
        tsv = abdir / f"ab-{div}.tsv"
        rows = [l.split("\t") for l in tsv.read_text().rstrip("\n").split("\n")][1:]
        a = sum(r[1] in DECIDED for r in rows)
        b = sum(r[4] in DECIDED for r in rows)
        dis = [r for r in rows if {r[1], r[4]} == DECIDED]
        contra = [r for r in rows for v in (r[1], r[4])
                  if v in DECIDED and r[8] in DECIDED and v != r[8]]
        gains = [r[0] for r in rows if r[1] not in DECIDED and r[4] in DECIDED]
        losses = [r[0] for r in rows if r[4] not in DECIDED and r[1] in DECIDED]
        errs = [r for r in rows if r[3] not in ("0", "124") or r[6] not in ("0", "124")]
        print(f"{div:16} {len(expected):5} {len(rows):5} {a:4} {b:4} {len(dis):4} {len(contra):13} "
              f"{len(gains)} {len(losses)}")
        for g in gains:
            print(f"   GAIN {g.split('/')[-1]}")
        for l in losses:
            print(f"   LOSS {l.split('/')[-1]}")
        for r in errs:
            print(f"   EXIT {r[0].split('/')[-1]} A_rc={r[3]} B_rc={r[6]}")
        if len(rows) != len(expected):
            print(f"   SHORT SWEEP: {len(rows)} of {len(expected)}")
            bad = True
        if dis:
            print("   DISAGREEMENT (soundness finding):", [r[0] for r in dis])
            bad = True
        if contra:
            print("   :status CONTRADICTION:", [r[0] for r in contra])
            bad = True
        movers.extend(gains + losses)
    if movers_out is not None:
        movers_out.write_text("".join(m + "\n" for m in movers))
        print(f"movers: {len(movers)} -> {movers_out}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
