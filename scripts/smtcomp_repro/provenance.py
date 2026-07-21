#!/usr/bin/env python3
"""Build a deterministic source-family and exact-content inventory.

The SMT-COMP execution artifact records absolute benchmark paths because it is
also a reproduction log.  This companion removes the machine prefix, hashes
the exact SMT-LIB bytes, and reports source-family skew and exact duplicates.
It does not attempt semantic or near-duplicate detection.

Usage:
    python3 scripts/smtcomp_repro/provenance.py RAW.json --out PROVENANCE.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


SCHEMA = "axeyum.smtcomp-provenance.v1"


def normalize_id(path: str, marker: str = "non-incremental/") -> str:
    if marker not in path:
        raise ValueError(f"benchmark path lacks {marker!r}: {path}")
    return path.split(marker, 1)[1]


def source_family(benchmark_id: str) -> str:
    parts = benchmark_id.split("/")
    if len(parts) < 3:
        raise ValueError(f"benchmark id lacks a source family: {benchmark_id}")
    # p4dfa has meaningful named subfamilies below its release directory;
    # flattened cvc5/Bitwuzla regression packs stop at the pack directory.
    depth = 3 if parts[1].startswith("20221214-") and len(parts) >= 4 else 2
    return "/".join(parts[:depth])


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
            size += len(chunk)
    return digest.hexdigest(), size


def classify(result: dict) -> str:
    reported = result.get("reported_status")
    expected = result.get("expected_status")
    if reported is None:
        return "no_answer"
    if reported == "unknown":
        return "declined"
    if expected is None or reported == expected:
        return "decided_correct"
    return "wrong"


def build(raw: dict, marker: str = "non-incremental/") -> dict:
    benchmarks = []
    by_digest: dict[str, list[str]] = defaultdict(list)
    families: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))

    for path, by_solver in sorted(raw.items()):
        if not by_solver:
            raise ValueError(f"benchmark has no solver result: {path}")
        result = next(iter(by_solver.values()))
        benchmark_id = normalize_id(path, marker)
        family = source_family(benchmark_id)
        digest, size = sha256_file(Path(path))
        outcome_class = classify(result)
        by_digest[digest].append(benchmark_id)
        families[family]["files"] += 1
        families[family][outcome_class] += 1
        benchmarks.append(
            {
                "id": benchmark_id,
                "logic": result["logic"],
                "source_family": family,
                "sha256": digest,
                "bytes": size,
                "expected_status": result.get("expected_status"),
                "reported_status": result.get("reported_status"),
                "outcome_class": outcome_class,
            }
        )

    duplicate_groups = [ids for ids in by_digest.values() if len(ids) > 1]
    duplicate_groups.sort(key=lambda ids: (-len(ids), ids))
    family_rows = {}
    for family, counts in sorted(families.items()):
        family_rows[family] = {
            key: counts.get(key, 0)
            for key in ("files", "decided_correct", "declined", "no_answer", "wrong")
        }

    return {
        "schema": SCHEMA,
        "summary": {
            "files": len(benchmarks),
            "source_families": len(family_rows),
            "unique_content_sha256": len(by_digest),
            "exact_duplicate_groups": len(duplicate_groups),
            "exact_duplicate_excess": sum(len(group) - 1 for group in duplicate_groups),
        },
        "source_family_rows": family_rows,
        "exact_duplicate_groups": duplicate_groups,
        "benchmarks": benchmarks,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw", type=Path)
    parser.add_argument("--marker", default="non-incremental/")
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()

    with args.raw.open(encoding="utf-8") as handle:
        report = build(json.load(handle), args.marker)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as handle:
        json.dump(report, handle, indent=2, sort_keys=True)
        handle.write("\n")
    summary = report["summary"]
    print(
        "PROVENANCE|"
        + "|".join(f"{key}={value}" for key, value in summary.items())
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
