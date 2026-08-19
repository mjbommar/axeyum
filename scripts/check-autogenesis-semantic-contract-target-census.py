#!/usr/bin/env python3
"""Fail closed over the first real semantic-contract target census."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-semantic-contract-target-census-v1.json"
EXPECTED_POPULATION = {
    "pointwise_definition_identities": 15,
    "affected_rows": 50,
    "direct_equation_environment_eligible_rows": 0,
    "train_rows": 34,
    "development_rows": 16,
    "terminal_equality_rows": 38,
    "axiom_free_source_rows": 17,
    "single_missing_dependency_rows": 5,
    "single_missing_dependency_axiom_free_rows": 1,
}
EXPECTED_NARROWEST = {
    "artifact_file": "r018.ndjson",
    "fact_id": "F:ml430-int-gcd-div-5e01872f",
    "source_name": "Int.gcd",
    "source_content_sha256": "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655",
    "missing_dependency": "Nat.gcd",
    "source_value_nodes": 11,
    "source_axiom_footprint": 0,
    "source_occurrences": 2,
    "abstraction_count": 3,
    "terminal_relation": "Eq",
}


class TargetCensusError(RuntimeError):
    """The selection census is absent, mutable, stale, or overclaimed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()
    ).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise TargetCensusError(f"{path} is not an object")
    return value


def validate_observation(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise TargetCensusError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["development", "train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "contracts_generated": 0,
        "producer_invocations": 0,
        "ledger_writes": 0,
    }
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-semantic-contract-target-census"
        or observation.get("state")
        != "selection-diagnostic-no-contract-proof-or-ledger-credit"
        or observation.get("authority") != expected_authority
        or observation.get("population")
        != {
            "pointwise_definition_identities": 15,
            "affected_rows": 50,
            "direct_equation_environment_eligible_rows": 0,
        }
    ):
        raise TargetCensusError("observation authority or population changed")
    rows = observation.get("rows")
    if not isinstance(rows, list) or len(rows) != 50:
        raise TargetCensusError("target row population changed")
    identities = set()
    row_keys = set()
    partitions = Counter()
    relations = Counter()
    axiom_free = 0
    single_missing = 0
    single_missing_axiom_free = 0
    narrowest = []
    ordering = []
    for row in rows:
        if not isinstance(row, dict):
            raise TargetCensusError("target row is malformed")
        artifact = row.get("artifact_file")
        fact = row.get("fact_id")
        source = row.get("source_name")
        content = row.get("source_content_sha256")
        partition = row.get("partition")
        equation = row.get("equation_contract")
        if (
            not all(isinstance(item, str) and item for item in [artifact, fact, source, content])
            or len(content) != 64
            or partition not in {"train", "development"}
            or not isinstance(equation, dict)
        ):
            raise TargetCensusError("target row identity is malformed")
        row_key = (artifact, content)
        if row_key in row_keys:
            raise TargetCensusError("target row identity repeats")
        row_keys.add(row_key)
        identities.add((source, content))
        ordering.append(artifact)
        partitions[partition] += 1
        relation = row.get("terminal_relation")
        relations[relation] += 1
        footprint = row.get("source_axiom_footprint")
        missing = equation.get("missing_from_proof_free_slice")
        dependencies = equation.get("direct_nonrecursive_dependencies")
        if (
            not isinstance(footprint, list)
            or not isinstance(missing, list)
            or not missing
            or missing != sorted(set(missing))
            or not isinstance(dependencies, list)
            or equation.get("all_nonrecursive_dependencies_retained") is not False
        ):
            raise TargetCensusError("direct-equation eligibility changed")
        dependency_names = [item.get("name") for item in dependencies]
        if dependency_names != sorted(set(dependency_names)):
            raise TargetCensusError("direct dependency inventory is unordered")
        derived_missing = sorted(
            item["name"] for item in dependencies if item.get("retained") is False
        )
        if missing != derived_missing:
            raise TargetCensusError("missing dependency inventory is not derived")
        if not footprint:
            axiom_free += 1
        if len(missing) == 1:
            single_missing += 1
            if not footprint:
                single_missing_axiom_free += 1
                narrowest.append(row)
    if (
        ordering != sorted(ordering)
        or len(identities) != 15
        or partitions != {"train": 34, "development": 16}
        or relations["Eq"] != 38
        or axiom_free != 17
        or single_missing != 5
        or single_missing_axiom_free != 1
    ):
        raise TargetCensusError("derived selection totals changed")
    row = narrowest[0]
    observed_narrowest = {
        "artifact_file": row["artifact_file"],
        "fact_id": row["fact_id"],
        "source_name": row["source_name"],
        "source_content_sha256": row["source_content_sha256"],
        "missing_dependency": row["equation_contract"]["missing_from_proof_free_slice"][0],
        "source_value_nodes": row["source_value_nodes"],
        "source_axiom_footprint": len(row["source_axiom_footprint"]),
        "source_occurrences": row["source_occurrences"],
        "abstraction_count": row["abstraction_count"],
        "terminal_relation": row["terminal_relation"],
    }
    if observed_narrowest != EXPECTED_NARROWEST:
        raise TargetCensusError("narrowest residualization control changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-semantic-contract-target-census"
        or manifest.get("state")
        != "selection-diagnostic-no-contract-proof-or-ledger-credit"
        or manifest.get("population") != EXPECTED_POPULATION
        or manifest.get("narrowest_residualization_control") != EXPECTED_NARROWEST
    ):
        raise TargetCensusError("manifest contract changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise TargetCensusError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise TargetCensusError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise TargetCensusError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_SEMANTIC_CONTRACT_TARGET_CENSUS_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "identities=15|rows=50|eligible=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, TargetCensusError) as error:
        print(f"autogenesis-semantic-contract-target-census: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
