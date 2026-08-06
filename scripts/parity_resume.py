#!/usr/bin/env python3
"""Validate and canonicalize parity-run resume rows.

New sidecars identify a benchmark by its exact committed-list path.  Older
sidecars used basenames; those remain readable only when the basename names one
and only one benchmark in the current list.  Ambiguity and population drift are
hard errors because reusing the wrong verdict would corrupt the parity ledger.
"""

from __future__ import annotations

import argparse
import csv
import sys
from collections import Counter
from pathlib import Path


class ResumeError(ValueError):
    """The sidecar cannot be mapped safely onto the committed population."""


def read_population(path: Path) -> list[str]:
    files = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    duplicates = sorted(file for file, count in Counter(files).items() if count > 1)
    if duplicates:
        raise ResumeError(f"benchmark list contains duplicate path: {duplicates[0]}")
    return files


def canonical_resume_rows(list_path: Path, sidecar_path: Path) -> list[tuple[str, str, str, str]]:
    population = read_population(list_path)
    population_set = set(population)
    by_basename: dict[str, list[str]] = {}
    for file in population:
        by_basename.setdefault(Path(file).name, []).append(file)

    with sidecar_path.open(newline="") as handle:
        rows = list(csv.reader(handle, delimiter="\t"))
    if not rows or not rows[0] or rows[0][0] != "file":
        raise ResumeError("sidecar is missing its file header")

    result: list[tuple[str, str, str, str]] = []
    seen: set[str] = set()
    for line_number, row in enumerate(rows[1:], start=2):
        if not row or not any(row):
            continue
        if len(row) < 4:
            raise ResumeError(f"sidecar line {line_number} has fewer than four fields")
        identity = row[0]
        if identity in population_set:
            canonical = identity
        else:
            candidates = by_basename.get(identity, [])
            if len(candidates) > 1:
                raise ResumeError(
                    f"legacy basename is ambiguous at sidecar line {line_number}: "
                    f"{identity} names {len(candidates)} benchmarks; restart without PARITY_RESUME"
                )
            if not candidates:
                raise ResumeError(
                    f"sidecar line {line_number} is outside the committed population: {identity}"
                )
            canonical = candidates[0]
        if canonical in seen:
            raise ResumeError(f"duplicate sidecar identity at line {line_number}: {canonical}")
        seen.add(canonical)
        result.append((canonical, row[1], row[2], row[3]))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("benchmark_list", type=Path)
    parser.add_argument("sidecar", type=Path)
    args = parser.parse_args()
    try:
        rows = canonical_resume_rows(args.benchmark_list, args.sidecar)
    except (OSError, ResumeError) as error:
        print(f"FAIL: unsafe parity resume: {error}", file=sys.stderr)
        return 2
    writer = csv.writer(sys.stdout, delimiter="\t", lineterminator="\n")
    writer.writerows(rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
