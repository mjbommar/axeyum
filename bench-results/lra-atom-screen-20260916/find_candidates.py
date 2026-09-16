#!/usr/bin/env python3
"""List every `shipped`-arm file whose `--trace` capture shows
`online_probe=admission-screen` -- the online CDCL(T) admission screen
actually refused it on atom count -- with its exact atom count (from the
SAME diagnostic line's `atoms=` field, which is the offline lazy-SMT loop's
own count of the identical `collect_lra_atoms` population the online screen
tested) and the multiplier that would admit it
(`ceil(atoms / admitted_at_1)`).

# Why capture files and not the ledger TSV

The admission screen's own refusal detail (the "N atoms exceeds M ..."
string in `lra_theory.rs`) is attached to the *online CDCL(T)* attempt's
`UnknownReason`, but that attempt is not a separate entry in the route
trail this corpus's files go through -- QF_LRA is dispatched under the
`nra` route's own umbrella, and what lands in `decline_details` for `nra`
is whatever the OFFLINE fallback loop declined with (Fourier-Motzkin's
budget message), not the online screen's. Confirmed empirically: zero of
the first captures contain the literal string "admission screen" anywhere.
What IS reliable is the `; lazy-smt reading=... atoms=N ...
online_probe=X` diagnostic line -- printed whenever the offline loop ran at
all, which (per `OnlineProbe`'s own doc) is every variant except `Took`.

Usage: find_candidates.py --captures DIR [--want FILE_LIST] [--admitted-at-1 1024]
"""
from __future__ import annotations

import argparse
import csv
import math
import re
import sys
from pathlib import Path

# A watchdog-killed run prefixes every diagnostic line with "; partial "
# (see the "; partial at=..." line printed alongside it) instead of "; " --
# same fields, same schema, just not a total reading. Both forms must match
# or a watchdog-killed admission-screen refusal silently drops out of the
# candidate list, which undercounts exactly the rows most likely to be
# memory- or time-constrained. Found by a discrepancy: grep -l for the
# literal string matched 8 QF_UFLRA captures, the anchored regex only 4.
LAZY_SMT_LINE = re.compile(r"^; (?:partial )?lazy-smt reading=\S+.*$", re.MULTILINE)
ATOMS_RE = re.compile(r"(?<![\w])atoms=(\d+)")
PROBE_RE = re.compile(r"online_probe=(\S+)")
READING_RE = re.compile(r"reading=(\S+)")


def file_from_capture_name(name: str, arm: str) -> str | None:
    prefix = f"{arm}__"
    if not name.startswith(prefix) or not name.endswith(".out"):
        return None
    slug = name[len(prefix) : -len(".out")]
    return slug  # caller maps slug -> rel path via the population list


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--captures", required=True, type=Path)
    ap.add_argument("--arm", default="shipped")
    ap.add_argument("--want", type=Path, help="population list (rel paths); used to map slug->file")
    ap.add_argument("--admitted-at-1", type=int, default=1024)
    args = ap.parse_args()

    slug_to_rel = {}
    if args.want:
        for ln in args.want.read_text().splitlines():
            ln = ln.strip()
            if ln:
                slug_to_rel[ln.replace("/", "_")] = ln

    n_total = 0
    n_admission = 0
    n_other_probe = 0
    n_not_reached = 0
    out = csv.writer(sys.stdout, delimiter="\t")
    out.writerow(["file", "atoms", "threshold_mult", "online_probe", "reading"])

    for cap in sorted(args.captures.glob(f"{args.arm}__*.out")):
        slug = file_from_capture_name(cap.name, args.arm)
        if slug is None:
            continue
        rel = slug_to_rel.get(slug, slug)
        n_total += 1
        text = cap.read_text(errors="replace")
        m_line = LAZY_SMT_LINE.search(text)
        if not m_line:
            n_not_reached += 1
            continue
        line = m_line.group(0)
        m_reading = READING_RE.search(line)
        m_probe = PROBE_RE.search(line)
        m_atoms = ATOMS_RE.search(line)
        reading = m_reading.group(1) if m_reading else "?"
        probe = m_probe.group(1) if m_probe else "?"
        if reading != "measured":
            n_not_reached += 1
            continue
        if probe != "admission-screen":
            n_other_probe += 1
            continue
        if not m_atoms:
            print(f"WARN: {rel}: reading=measured probe=admission-screen but no atoms= found", file=sys.stderr)
            continue
        atoms = int(m_atoms.group(1))
        thr = math.ceil(atoms / args.admitted_at_1)
        out.writerow([rel, atoms, thr, probe, reading])
        n_admission += 1

    print(
        f"# total_captures={n_total} admission_screen={n_admission} "
        f"other_probe_offline_reached={n_other_probe} not_reached_offline={n_not_reached}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
