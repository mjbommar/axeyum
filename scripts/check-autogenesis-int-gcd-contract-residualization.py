#!/usr/bin/env python3
"""Verify the exact Int.gcd contract-body residualization control."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-int-gcd-contract-residualization-v1.json"
EXPECTED_RESULT = {
    "source": "Int.gcd",
    "source_content_sha256": "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655",
    "residual": "Nat.gcd",
    "retained": ["Int", "Int.natAbs"],
    "function_arity": 2,
    "contract_binders": 2,
    "source_witness_axioms": 0,
    "source_witness_direct_theorems": 0,
    "source_witness_transitive_theorems": 52,
    "specialization_verified": True,
    "receipt_eligible": False,
}


class ResidualizationError(RuntimeError):
    """The residualization control changed, weakened, or overclaimed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ResidualizationError(f"{path} is not an object")
    return value


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


def validate_observation(observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise ResidualizationError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "producer_target_attempts": 0,
        "contracts_admitted": 0,
        "ledger_writes": 0,
    }
    source = observation.get("source")
    residual = observation.get("residualization")
    witness = observation.get("source_witness")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-int-gcd-contract-residualization-control"
        or observation.get("state")
        != "mechanism-control-no-contract-proof-or-ledger-credit"
        or observation.get("authority") != expected_authority
        or not isinstance(source, dict)
        or not isinstance(residual, dict)
        or not isinstance(witness, dict)
    ):
        raise ResidualizationError("observation authority changed")
    if (
        source.get("artifact_file") != "r018.ndjson"
        or source.get("lean_version") != "4.30.0"
        or source.get("lean_githash") != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or source.get("definition") != "Int.gcd"
        or source.get("definition_content_sha256") != EXPECTED_RESULT["source_content_sha256"]
    ):
        raise ResidualizationError("source identity changed")
    if (
        residual.get("source_binder") != "Int.gcd"
        or residual.get("residual_binders") != ["Nat.gcd"]
        or residual.get("retained_direct_body_constants") != ["Int", "Int.natAbs"]
        or residual.get("function_arity") != 2
        or residual.get("contract_binders") != 2
        or residual.get("specialization_verified") is not True
        or not isinstance(residual.get("source_equation_sha256"), str)
        or len(residual["source_equation_sha256"]) != 64
        or not isinstance(residual.get("generalized_contract_sha256"), str)
        or len(residual["generalized_contract_sha256"]) != 64
    ):
        raise ResidualizationError("residualized contract changed")
    axioms = witness.get("axiom_footprint")
    direct = witness.get("direct_theorem_dependencies")
    transitive = witness.get("transitive_theorem_dependencies")
    if (
        witness.get("producer") != "bounded-pi-equality-reflexivity-v1"
        or witness.get("binders") != 2
        or witness.get("constructed_nodes") != 5
        or axioms != []
        or direct != []
        or not isinstance(transitive, list)
        or len(transitive) != 52
        or transitive != sorted(set(transitive))
        or "Nat.div_rec_lemma" not in transitive
    ):
        raise ResidualizationError("source witness assurance inventory changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-int-gcd-contract-residualization"
        or manifest.get("state")
        != "mechanism-control-no-contract-proof-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT
    ):
        raise ResidualizationError("manifest contract changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise ResidualizationError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise ResidualizationError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise ResidualizationError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_INT_GCD_CONTRACT_RESIDUALIZATION_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "residual=Nat.gcd|axioms=0|direct_theorems=0|transitive_theorems=52|"
            "receipt_eligible=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ResidualizationError) as error:
        print(f"autogenesis-int-gcd-contract-residualization: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
