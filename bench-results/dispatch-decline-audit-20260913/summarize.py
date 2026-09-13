#!/usr/bin/env python3
"""Summarise an ADR-1966 A/B run.

Refuses to treat a MALFORMED row as a datum. `ab-run.sh` writes the refusal
sentence into the row, and some of those sentences carry a character that
splits the record; a row whose verdict field is not one of sat/unsat/unknown
is a parse failure of this file, not a solver result, and silently reading it
as "moved" is how a measurement manufactures a finding. Malformed rows are
counted and listed so they can be re-run, never scored.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

VERDICTS = {"sat", "unsat", "unknown", ""}


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: summarize.py <ab.tsv>...", file=sys.stderr)
        return 2
    print(
        f"{'division':<18}{'n':>5}{'ok':>5}{'bad':>5}"
        f"{'base_dec':>10}{'fix_dec':>9}{'gain':>6}{'loss':>6}{'flip':>6}"
    )
    total_bad = 0
    for p in sys.argv[1:]:
        rows = list(csv.DictReader(open(p), delimiter="\t"))
        good, bad = [], []
        for r in rows:
            bv, fv = r.get("base_v"), r.get("fix_v")
            if bv in VERDICTS and fv in VERDICTS and bv is not None and fv is not None:
                good.append(r)
            else:
                bad.append(r)
        total_bad += len(bad)
        dec = lambda rs, k: sum(1 for r in rs if r[k] in ("sat", "unsat"))
        gain = [r for r in good if r["base_v"] not in ("sat", "unsat")
                and r["fix_v"] in ("sat", "unsat")]
        loss = [r for r in good if r["base_v"] in ("sat", "unsat")
                and r["fix_v"] not in ("sat", "unsat")]
        flip = [r for r in good if {r["base_v"], r["fix_v"]} == {"sat", "unsat"}]
        print(
            f"{Path(p).stem:<18}{len(rows):>5}{len(good):>5}{len(bad):>5}"
            f"{dec(good, 'base_v'):>10}{dec(good, 'fix_v'):>9}"
            f"{len(gain):>6}{len(loss):>6}{len(flip):>6}"
        )
        for r in flip:
            print(f"    SAT/UNSAT FLIP -- {r['file']}: {r['base_v']} -> {r['fix_v']}")
    if total_bad:
        print(f"\n{total_bad} malformed row(s) excluded from every column above; "
              f"they are NOT scored as unchanged.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
