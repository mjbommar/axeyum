#!/usr/bin/env python3
"""Derive the atom-screen ladder table (2x, 4x, 16x, "off") from the passes
`run-ladder.sh` actually executes -- `shipped` (every file) and one
higher-multiplier "open" arm (run only on files the shipped pass refused via
the admission screen, plus a spot-check subset of files it did not refuse).

# Why a derivation and not five raw sweeps

`AXEYUM_LRA_ATOM_SCREEN` gates exactly one boolean in
`crates/axeyum-solver/src/lra_theory.rs::check_qf_lra_online_cdclt`:
`atom_terms.len() > admitted_atoms`, where
`admitted_atoms = (budget_bytes / BYTES_PER_ADMITTED_ATOM) * multiplier`.
Nothing downstream reads the multiplier or `admitted_atoms` again --
`CdcltLraTheory::new` is built from the actual atom list and `budget_bytes`,
not from the screen's allowance. So for a FIXED file, execution is a step
function of the multiplier: refused (and therefore bit-identical to the
shipped arm) for every multiplier below the file's own threshold
`ceil(atoms / admitted_at_1)`, and bit-identical to the measured "open" run
for every multiplier at or above it. This script reads that atom count
straight from the ledger's `decline_details` column (the admission screen's
own refusal message), computes each file's threshold, and for each requested
ladder level looks up whichever of the two measured passes sits on the
correct side of that threshold. Nothing here runs untested code or
extrapolates a number that was not measured.

Usage:
  derive_ladder.py --ledger PATH/lra-atom-screen-20260916.tsv \
      --rss-dir PATH/rss --open-mult 65536 --levels 2,4,16,off \
      --admitted-at-1 1024
"""
from __future__ import annotations

import argparse
import csv
import math
import re
import sys
from pathlib import Path

ADMIT_RE = re.compile(r"admission screen: (\d+) atoms exceeds the (\d+) a")


def read_ledger_tsv(path: Path):
    with path.open(newline="", encoding="utf-8") as fh:
        r = csv.DictReader(fh, delimiter="\t")
        return list(r)


def peak_rss_kb(rss_path: Path):
    if not rss_path.exists():
        return ""
    text = rss_path.read_text(errors="replace")
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
    return int(m.group(1)) if m else ""


def atom_threshold(row: dict, admitted_at_1: int) -> int:
    """1 if never refused by the admission screen (identical at every
    multiplier); otherwise ceil(atoms / admitted_at_1)."""
    details = row.get("decline_details", "") or ""
    names = row.get("decline_reasons", "") or ""
    if "admission" not in names and "admission" not in details:
        return 1
    for chunk in details.split("|"):
        m = ADMIT_RE.search(chunk)
        if m:
            atoms = int(m.group(1))
            return math.ceil(atoms / admitted_at_1)
    return 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--rss-dir", required=True, type=Path)
    ap.add_argument("--open-mult", required=True, type=int)
    ap.add_argument("--levels", default="2,4,16,off")
    ap.add_argument("--admitted-at-1", type=int, default=1024)
    args = ap.parse_args()

    rows = read_ledger_tsv(args.ledger)
    by_arm_file: dict[tuple[str, str], dict] = {}
    for row in rows:
        by_arm_file[(row["arm"], row["corpus_path"])] = row

    open_arm = str(args.open_mult)
    levels = []
    for tok in args.levels.split(","):
        levels.append(("off", 1 << 30) if tok == "off" else (tok, int(tok)))

    shipped_files = sorted({f for (a, f) in by_arm_file if a == "shipped"})

    w = csv.writer(sys.stdout, delimiter="\t")
    w.writerow(
        [
            "level",
            "file",
            "threshold_mult",
            "admitted_at_level",
            "source_arm",
            "verdict",
            "ms",
            "exit_status",
            "peak_rss_kb",
            "decided_by",
        ]
    )

    for f in shipped_files:
        shipped_row = by_arm_file[("shipped", f)]
        threshold = atom_threshold(shipped_row, args.admitted_at_1)
        slug = f.replace("/", "_")
        for label, mult in levels:
            admitted = mult >= threshold
            if admitted and threshold > 1:
                src_row = by_arm_file.get((open_arm, f))
                src_arm = open_arm
                if src_row is None:
                    # Not yet measured at the open arm (not in the candidate
                    # or spot-check set); skip rather than guess.
                    continue
            else:
                src_row = shipped_row
                src_arm = "shipped"
            rss_path = args.rss_dir / f"{src_arm}__{slug}.rss"
            w.writerow(
                [
                    label,
                    f,
                    threshold,
                    admitted,
                    src_arm,
                    src_row.get("verdict", ""),
                    src_row.get("elapsed_ms", ""),
                    src_row.get("exit_status", ""),
                    peak_rss_kb(rss_path),
                    src_row.get("decided_by", ""),
                ]
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
