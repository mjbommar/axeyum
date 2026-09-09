#!/usr/bin/env python3
"""Derive the 2026-09-08 loss lists from the sweep passes.

Two passes, not one. A 24 s budget is a WALL clock and this host carried other
lanes throughout (load 11-21 across the sweep), so a file that misses the
budget under contention may well decide on an idle box. A loss list built from
one contended pass over-counts losses, which is the same defect -- a lane
pointed at a file we can win -- as the staleness this whole exercise is about,
just arriving from the other direction.

So:

  * a file is on `<DIV>.txt` (the population a brief should cite) only if it was
    UNSOLVED IN EVERY PASS;
  * a file decided in some passes and not others goes to `<DIV>.flaky.txt` and
    is reported separately -- it is neither a clean win nor something to brief a
    lane at;
  * a file decided in every pass is RECOVERED against the 2026-09-05 census.

`<DIV>.census.tsv` carries every row with its per-pass verdicts, so any of the
three classes can be re-derived without re-running anything.

Usage: derive-lists.py [--set <dir>] [--passes sweep,confirm]
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SET_DIR = HERE.parent
OLD_SET = SET_DIR.parent / "parity-losses-20260905"
NRA_SET = SET_DIR.parent / "parity-losses-20260906"


def read_pass(path: Path) -> dict[str, dict]:
    rows: dict[str, dict] = {}
    if not path.exists():
        return rows
    with path.open() as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            rows[row["file"]] = row
    return rows


def old_list(div: str) -> list[str]:
    for base in (OLD_SET, NRA_SET):
        p = base / f"{div}.txt"
        if p.exists():
            return [ln for ln in p.read_text().splitlines() if ln.strip()]
    return []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--set", default=str(SET_DIR))
    ap.add_argument("--passes", default="sweep,confirm")
    args = ap.parse_args()
    root = Path(args.set)
    pass_names = [p for p in args.passes.split(",") if p]

    divisions = sorted(p.stem for p in (root / pass_names[0]).glob("*.tsv"))
    if not divisions:
        print(f"derive-lists: no pass-1 TSVs under {root / pass_names[0]}", file=sys.stderr)
        return 1

    print(f"{'division':<10} {'was':>5} {'still':>6} {'recovered':>10} {'flaky':>6}")
    total = [0, 0, 0, 0]
    for div in divisions:
        passes = {name: read_pass(root / name / f"{div}.tsv") for name in pass_names}
        present = [n for n in pass_names if passes[n]]
        files = old_list(div)
        if not files:
            print(f"{div:<10}   -- no 2026-09-05 population found, skipped")
            continue

        losses: list[str] = []
        flaky: list[str] = []
        recovered: list[str] = []
        census = []
        for f in files:
            verdicts = [passes[n].get(f, {}).get("verdict", "not-run") for n in present]
            decided = [v for v in verdicts if v in ("sat", "unsat")]
            unsolved = [v for v in verdicts if v == "unsolved"]
            missing = [v for v in verdicts if v == "not-run"]
            if missing and not decided:
                # A file no pass reached is NOT evidence of a loss. Recorded as
                # its own class rather than folded into either answer.
                cls = "not-run"
            elif decided and not unsolved:
                cls = "recovered"
                recovered.append(f)
            elif decided and unsolved:
                cls = "flaky"
                flaky.append(f)
            else:
                cls = "loss"
                losses.append(f)
            row = {"file": f, "division": div, "class": cls}
            for n in present:
                r = passes[n].get(f, {})
                row[f"{n}_verdict"] = r.get("verdict", "not-run")
                row[f"{n}_ms"] = r.get("wall_ms", "")
                row[f"{n}_over_budget"] = r.get("over_budget", "")
            row["declared"] = passes[present[0]].get(f, {}).get("declared", "")
            census.append(row)

        (root / f"{div}.txt").write_text("".join(f"{f}\n" for f in losses))
        if flaky:
            (root / f"{div}.flaky.txt").write_text("".join(f"{f}\n" for f in flaky))
        with (root / f"{div}.census.tsv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(census[0].keys()), delimiter="\t")
            w.writeheader()
            w.writerows(census)

        print(
            f"{div:<10} {len(files):5d} {len(losses):6d} {len(recovered):10d} {len(flaky):6d}"
        )
        total[0] += len(files)
        total[1] += len(losses)
        total[2] += len(recovered)
        total[3] += len(flaky)

    print(f"{'TOTAL':<10} {total[0]:5d} {total[1]:6d} {total[2]:10d} {total[3]:6d}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
