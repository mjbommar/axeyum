#!/usr/bin/env python3
"""Measure exact native proposition matches for the visible open census."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RANKING = ROOT / "artifacts/autogenesis/open-lemma-candidate-ranking-v1.json"
POPULATION = ROOT / "artifacts/autogenesis/open-fixed-palette-census-v1.json"
OUTPUT = ROOT / "artifacts/autogenesis/open-ranked-proposition-census-v1.json"
BINARY = ROOT / "target/debug/examples/proposition_compatibility_audit"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--binary", type=Path, default=BINARY)
    args = parser.parse_args()

    ranking = json.loads(RANKING.read_text())
    population = json.loads(POPULATION.read_text())
    held_out = set(ranking["excluded_held_out_fact_ids"])
    goals = {row["fact_id"]: row for row in ranking["goals"]}
    archive = Path(population["source"]["external_capsule_directory"])
    if not args.binary.is_file():
        raise SystemExit(f"audit binary is absent: {args.binary}")

    rows = []
    matches = []
    for source_row in population["outcomes"]:
        fact_id = source_row["fact_id"]
        if fact_id in held_out:
            raise SystemExit(f"held-out fact reached census: {fact_id}")
        goal = goals.get(fact_id)
        if goal is None:
            raise SystemExit(f"population fact absent from ranking: {fact_id}")
        capsule = archive / f"{fact_id.replace(':', '-')}.ndjson"
        candidates = [row["kernel_declaration_id"] for row in goal["candidates"]]
        completed = subprocess.run(
            [str(args.binary), str(capsule), source_row["target_definition"], *candidates],
            check=False,
            capture_output=True,
            text=True,
        )
        if completed.returncode:
            raise SystemExit(f"audit failed for {fact_id}: {completed.stderr.strip()}")
        result = json.loads(completed.stdout)
        compatible = [row["native_theorem"] for row in result["compatible"]]
        matches.extend({"fact_id": fact_id, "native_theorem": name} for name in compatible)
        rows.append(
            {
                "fact_id": fact_id,
                "partition": goal["partition"],
                "target_definition": source_row["target_definition"],
                "capsule_bytes": capsule.stat().st_size,
                "capsule_sha256": sha256(capsule),
                "candidate_count": result["candidate_count"],
                "compatible_native_theorems": compatible,
                "declined_count": len(result["declined"]),
            }
        )

    candidate_count = sum(row["candidate_count"] for row in rows)
    observation = {
        "schema_version": 1,
        "kind": "axeyum-open-ranked-proposition-census",
        "state": "diagnostic-only-no-ledger-or-admission-authority",
        "source": {
            "ranking_sha256": sha256(RANKING),
            "population_sha256": sha256(POPULATION),
            "external_capsule_directory": str(archive),
        },
        "census": {
            "goal_count": len(rows),
            "candidate_count": candidate_count,
            "compatible_pair_count": len(matches),
            "declined_pair_count": candidate_count - len(matches),
            "audit_error_count": 0,
            "held_out_access_count": 0,
        },
        "matches": matches,
        "outcomes": rows,
        "authority": "Exact compatibility is graph-reconciliation evidence only; it is not autonomous proof production, fact settlement, or theorem admission.",
        "limitations": "Candidates are the top 12 from the deterministic lexical/type/graph ranker and the native audit kernel currently builds the Int prelude (including Nat). Missing native declarations decline per candidate. The census says nothing about candidates outside the ranked window or other prelude families.",
    }
    rendered = json.dumps(observation, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            raise SystemExit(f"stale generated artifact: {OUTPUT.relative_to(ROOT)}")
    else:
        OUTPUT.write_text(rendered)
    print(
        f"AUTOGENESIS_RANKED_PROPOSITION_CENSUS_OK|goals={len(rows)}|"
        f"pairs={candidate_count}|matches={len(matches)}|held_out=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
