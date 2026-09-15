#!/usr/bin/env python3
"""Summarise `bucket_census.py`'s per-row table into the tables the ADR prints.

Three sections, each with its own DENOMINATOR stated on the line, because the
three populations are nested and averaging across them is how ADR-2045's own
"34 of 34" became ADR-2055's "26 of 34":

  1. buckets over all 93 rows;
  2. the failing ALLOCATION SIZE over the abort rows -- the number that
     distinguishes "asked for 10 GiB" from "asked for 1 MB while already at the
     ceiling", which are different bugs with different fixes;
  3. the online CDCL(T) engine's own counters over ONLY the rows that reached
     it. A row with no `; theory-layer` line contributes nothing here rather
     than a zero, and the count of such rows is printed beside the table.

Usage:  bucket_summary.py <buckets.tsv> [--shapes <shapes.tsv>]
"""

from __future__ import annotations

import argparse
import statistics
import sys
from pathlib import Path

RATIOS = [
    ("bound_scan_atoms", "theory_propagations", "atom scans per propagation"),
    ("decisions", "theory_propagations", "SAT decisions per propagation"),
    ("final_check_core_literals", "theory_conflicts", "literals per conflict core"),
    ("simplex_pivots", "theory_conflicts", "pivots per conflict"),
    ("fill_nnz_sum", "fill_samples", "tableau nonzeros (mean)"),
]

ONLINE = [
    "decisions",
    "theory_conflicts",
    "theory_propagations",
    "bound_scan_calls",
    "bound_scan_atoms",
    "simplex_pivots",
    "simplex_rows",
    "simplex_columns",
    "final_check_core_literals",
    "boolean_propagate_ms",
    "theory_propagate_ms",
    "theory_final_check_ms",
]


def load(path: Path) -> list[dict[str, str]]:
    lines = path.read_text().splitlines()
    head = lines[0].split("\t")
    return [dict(zip(head, ln.split("\t"), strict=True)) for ln in lines[1:] if ln]


def med(vals: list[int]) -> str:
    return f"{int(statistics.median(vals)):,}" if vals else "n/a"


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    ap.add_argument("buckets")
    ap.add_argument("--shapes")
    args = ap.parse_args(argv[1:])
    rows = load(Path(args.buckets))
    total = len(rows)
    print(f"population: {total} undecided QF_LRA rows\n")

    print("-- 1. bucket, by the channel that answered --")
    counts: dict[tuple[str, str], int] = {}
    for r in rows:
        counts[(r["channel"], r["bucket"])] = counts.get((r["channel"], r["bucket"]), 0) + 1
    for (ch, bk), n in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:3d}/{total}  {ch:<9} {bk}")

    print("\n-- 1b. the same rows by the producer's PROSE, which is all 36 of")
    print("       `budget/other` carry: the typed name types nothing here --")
    proses: dict[str, int] = {}
    for r in rows:
        if r["channel"] != "trail":
            continue
        d = r["detail"].split("(")[0].strip()
        proses[f"{r['bucket']} | {d[:88]}"] = proses.get(f"{r['bucket']} | {d[:88]}", 0) + 1
    for k, n in sorted(proses.items(), key=lambda kv: -kv[1]):
        print(f"  {n:3d}  {k}")

    aborts = [r for r in rows if r["channel"] == "abort" and r["alloc_bytes"] != "n/a"]
    print(f"\n-- 2. the FAILING allocation, over {len(aborts)} abort rows --")
    if aborts:
        sizes = sorted(int(r["alloc_bytes"]) for r in aborts)
        print(f"  median {sizes[len(sizes) // 2]:,} B   min {sizes[0]:,} B   max {sizes[-1]:,} B")
        print("  Read this against the 8 GiB `ulimit -v` the harness enforces: a")
        print("  request this small failing means the process was ALREADY at the")
        print("  ceiling and this was the straw, not the load. The cumulative")
        print("  holder is the tableau ([ADR-2055], median 10.53 GiB on these rows).")

    online = [r for r in rows if r["decisions"] != "n/a"]
    print(f"\n-- 3. the online CDCL(T) engine, over the {len(online)}/{total} rows that reached it --")
    print(f"     ({total - len(online)} rows contribute NOTHING here, not a zero)")
    if online:
        for k in ONLINE:
            vals = [int(r[k]) for r in online if r[k] != "n/a"]
            print(f"  {k:<28} median {med(vals):>16}   n={len(vals)}")
        print()
        for num, den, label in RATIOS:
            pairs = [
                (int(r[num]), int(r[den]))
                for r in online
                if r[num] != "n/a" and r[den] != "n/a" and int(r[den]) > 0
            ]
            if not pairs:
                print(f"  {label:<34} n/a (denominator zero on every row)")
                continue
            ratios = sorted(a / b for a, b in pairs)
            print(
                f"  {label:<34} median {ratios[len(ratios) // 2]:>14,.1f}   n={len(pairs)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
