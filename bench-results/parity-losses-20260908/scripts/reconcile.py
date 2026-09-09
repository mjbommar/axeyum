#!/usr/bin/env python3
"""Reconcile the re-cut against `bench-results/PARITY.md`.

The re-cut has no reference (only z3 is installed on s4; these divisions score
against cvc5/bitwuzla/yices), so it cannot say by itself whether a complement
file that is now `unsolved` is a REGRESSION or one of the division's `neither`
files. The ledger can, at the count level:

    old-list survivors + complement-unsolved  ==  reference-only + neither

Where the two sides agree, the loss list is exactly the old-list survivors and
the complement's unsolved files are the `neither` set. Where they do not, the
residual is a count of files whose status changed since the ledger entry -- in
either direction -- and it is printed rather than absorbed.

The ledger row used is the newest NON-annotated entry for the division (a
`— SECOND REFERENCE` entry scores against a different solver and is not
comparable), together with the number of commits touching `crates/` between its
solver commit and HEAD. That last column is the one that says how much weight
the reconciliation can carry.
"""

from __future__ import annotations

import csv
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SET_DIR = HERE.parent
ROOT = SET_DIR.parent.parent
LEDGER = ROOT / "bench-results" / "PARITY.md"

ENTRY_RE = re.compile(r"^## ([A-Z][A-Z_0-9]*) — (\S+)(.*)$", re.M)


def ledger_rows() -> dict[str, dict]:
    text = LEDGER.read_text()
    out: dict[str, dict] = {}
    for m in ENTRY_RE.finditer(text):
        logic, ts, label = m.group(1), m.group(2), m.group(3).strip()
        if label:
            # `— SECOND REFERENCE (…)` scores a different solver; `— EVIDENCE
            # MODE` is a different front door. Neither is comparable here.
            continue
        body = text[m.end(): m.end() + 1600]

        def cell(name: str) -> str:
            mm = re.search(r"\|\s*" + re.escape(name) + r"\s*\|\s*([^|]+?)\s*\|", body)
            return mm.group(1).strip() if mm else ""

        bar = cell("both / axeyum-only / reference-only")
        parts = [p.strip() for p in bar.split("/")] if bar else []
        if len(parts) != 3:
            continue
        try:
            both, ours, theirs = (int(p) for p in parts)
        except ValueError:
            continue
        solved = cell("axeyum solved")
        try:
            total = int(solved.split("/")[1])
        except (IndexError, ValueError):
            continue
        out[logic] = {
            "ts": ts,
            "both": both,
            "ours": ours,
            "theirs": theirs,
            "total": total,
            "neither": total - both - ours - theirs,
            "commit": cell("solver commit").strip("`"),
        }
    return out


def behind(sha: str) -> str:
    if not sha:
        return "?"
    r = subprocess.run(
        ["git", "-C", str(ROOT), "rev-list", "--count", f"{sha}..HEAD", "--", "crates/"],
        capture_output=True, text=True, check=False,
    )
    return r.stdout.strip() if r.returncode == 0 else "unresolvable"


def unsolved_count(path: Path) -> tuple[int, int]:
    if not path.exists():
        return (-1, -1)
    n = u = 0
    with path.open() as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            n += 1
            if row["verdict"] == "unsolved":
                u += 1
    return n, u


def main() -> int:
    led = ledger_rows()
    divisions = sorted(p.stem for p in (SET_DIR / "sweep").glob("*.tsv"))
    print(
        f"{'division':<9} {'recut':>6} {'comp?':>6} {'recut+comp':>11} "
        f"{'ledger r-only+neither':>22} {'residual':>9}  ledger entry"
    )
    for div in divisions:
        loss_path = SET_DIR / f"{div}.txt"
        survivors = (
            sum(1 for ln in loss_path.read_text().splitlines() if ln.strip())
            if loss_path.exists()
            else -1
        )
        cn, cu = unsolved_count(SET_DIR / "comp" / f"{div}.tsv")
        row = led.get(div)
        if not row:
            print(f"{div:<9} {survivors:6d} {'--':>6} {'--':>11} {'no ledger entry':>22}")
            continue
        rhs = row["theirs"] + row["neither"]
        if cu < 0:
            print(
                f"{div:<9} {survivors:6d} {'not run':>6} {'--':>11} {rhs:22d} "
                f"{'--':>9}  {row['ts']} behind={behind(row['commit'])}"
            )
            continue
        lhs = survivors + cu
        print(
            f"{div:<9} {survivors:6d} {cu:6d} {lhs:11d} {rhs:22d} "
            f"{lhs - rhs:+9d}  {row['ts']} behind={behind(row['commit'])}"
        )
    print()
    print("residual > 0: we decide fewer files than the ledger entry implies")
    print("residual < 0: we decide more (the usual case -- the tree moved since)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
