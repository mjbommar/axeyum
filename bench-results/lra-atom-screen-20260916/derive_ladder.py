#!/usr/bin/env python3
"""Derive the atom-screen ladder table (2x, 4x, 16x, "off") from the passes
`run-ladder.sh` actually executes -- `shipped` (every file) and one
higher-multiplier "open" arm (run only on files the shipped pass's admission
screen refused, plus a spot-check subset of files it did not refuse).

# Why a derivation and not five raw sweeps

`AXEYUM_LRA_ATOM_SCREEN` gates exactly one boolean in
`crates/axeyum-solver/src/lra_theory.rs::check_qf_lra_online_cdclt`:
`atom_terms.len() > admitted_atoms`. Nothing downstream reads the multiplier
or `admitted_atoms` again, so for a FIXED file execution is a step function
of the multiplier: refused (bit-identical to shipped) below the file's own
threshold `ceil(atoms / admitted_at_1)`, bit-identical to the measured
"open" run at or above it. `find_candidates.py` recovers each refused
file's exact atom count from the `; lazy-smt reading=... atoms=N
online_probe=admission-screen` diagnostic line in its `shipped` capture
(the admission screen's own refusal STRING is not surfaced anywhere in the
trail -- see that script's docstring); this script combines that threshold
with the measured verdict/time/exit-status/RSS from whichever of the two
passes sits on the correct side of it, for every requested ladder level.
Nothing here runs untested code or extrapolates a number that was not
measured.

Usage:
  derive_ladder.py --ledger PATH/lra-atom-screen-20260916.tsv \
      --candidates PATH/candidates.tsv --rss-dir PATH/rss \
      --open-mult 65536 --levels 2,4,16,off
"""
from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


def read_ledger_tsv(path: Path):
    with path.open(newline="", encoding="utf-8") as fh:
        r = csv.DictReader(fh, delimiter="\t")
        return list(r)


def read_candidates(path: Path) -> dict[str, int]:
    out: dict[str, int] = {}
    with path.open(newline="", encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#") or line.startswith("file\t"):
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 3:
                continue
            out[parts[0]] = int(parts[2])
    return out


def peak_rss_kb(rss_path: Path):
    if not rss_path.exists():
        return ""
    text = rss_path.read_text(errors="replace")
    m = re.search(r"Maximum resident set size \(kbytes\): (\d+)", text)
    return int(m.group(1)) if m else ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", required=True, type=Path)
    ap.add_argument("--candidates", required=True, type=Path, help="find_candidates.py output")
    ap.add_argument("--rss-dir", required=True, type=Path)
    ap.add_argument("--open-mult", required=True, type=int)
    ap.add_argument("--levels", default="2,4,16,off")
    args = ap.parse_args()

    rows = read_ledger_tsv(args.ledger)
    by_arm_file: dict[tuple[str, str], dict] = {}
    for row in rows:
        by_arm_file[(row["arm"], row["corpus_path"])] = row

    thresholds = read_candidates(args.candidates)

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
        threshold = thresholds.get(f, 1)
        slug = f.replace("/", "_")
        for label, mult in levels:
            admitted = mult >= threshold
            if admitted and threshold > 1:
                src_row = by_arm_file.get((open_arm, f))
                src_arm = open_arm
                if src_row is None:
                    continue  # not measured at the open arm; skip, don't guess
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
