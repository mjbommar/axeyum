#!/usr/bin/env python3
"""Verify the one-shot Int.gcd contract-to-theorem control."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-int-gcd-contract-theorem-control-v1.json"
EXPECTED_RESULT = {
    "target": "Int.gcd_def",
    "source": "Int.gcd",
    "source_contract_receipt_sha256": "ae7585751df713ac8fda6f611c3197b0917c9001dc8bda134e9a43416ce3ec82",
    "semantic_theorem_receipt_sha256": "2aaf51c928c786b8a72b635d8fb783b4dc1bbdde5ab9b7c18c8e79ca0213f9d7",
    "operation": "trace-contract-reflexivity-v1",
    "binders": 2,
    "constructed_nodes": 5,
    "producer_invocations": 1,
    "producer_retries": 0,
    "kernel_accepted": True,
    "theorem_axioms": 0,
    "direct_theorem_dependencies": 0,
    "diagnostic_transitive_theorem_dependencies": 52,
    "source_contract_receipts_consumed": 1,
    "semantic_theorem_receipts_issued": 1,
    "evaluation_credit": 0,
    "ledger_writes": 0,
}


class ContractTheoremControlError(RuntimeError):
    """The control changed, weakened, or claimed forbidden credit."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ContractTheoremControlError(f"{path} is not an object")
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
        raise ContractTheoremControlError("inner observation identity changed")
    authority = {
        "evaluation_credit": 0,
        "held_out_inspected": False,
        "ledger_writes": 0,
        "partitions_inspected": ["train"],
        "proof_bodies_inspected": False,
        "semantic_theorem_receipts_issued": 1,
        "source_contract_receipts_consumed": 1,
    }
    assurance = {
        "binders": 2,
        "constructed_nodes": 5,
        "dependency_inventory_is_diagnostic_only": True,
        "kernel_accepted": True,
        "producer_invocations": 1,
        "producer_operation": "trace-contract-reflexivity-v1",
        "producer_retries": 0,
        "source_contract_receipt_replayed": True,
        "theorem_axioms": 0,
        "theorem_receipt_reissued_exactly": True,
    }
    source = observation.get("source")
    receipt = observation.get("semantic_theorem_receipt")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-int-gcd-contract-theorem-control"
        or observation.get("state")
        != "calibration-theorem-receipt-issued-no-evaluation-or-ledger-credit"
        or observation.get("authority") != authority
        or observation.get("assurance") != assurance
        or observation.get("source_contract_receipt_sha256")
        != EXPECTED_RESULT["source_contract_receipt_sha256"]
        or not isinstance(source, dict)
        or not isinstance(receipt, dict)
    ):
        raise ContractTheoremControlError("observation authority changed")
    if source != {
        "artifact_file": "r018.ndjson",
        "definition": "Int.gcd",
        "definition_content_sha256": "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lean_version": "4.30.0",
        "stream_sha256": "dd6e6eed26c59e71c10289076002ac3c683309a82629accba4425919cab86e66",
    }:
        raise ContractTheoremControlError("source identity changed")
    receipt_unsigned = dict(receipt)
    receipt_claimed = receipt_unsigned.pop("receipt_sha256", None)
    if (
        receipt_claimed != EXPECTED_RESULT["semantic_theorem_receipt_sha256"]
        or receipt_claimed != canonical_digest(receipt_unsigned)
    ):
        raise ContractTheoremControlError("semantic theorem receipt identity changed")
    producer = receipt.get("producer")
    theorem = receipt.get("theorem")
    dependencies = receipt.get("diagnostic_dependencies")
    if (
        receipt.get("schema_version")
        != "axeyum-trace-backed-semantic-theorem-receipt-v1"
        or receipt.get("policy_version") != "int-gcd-contract-theorem-control-v1"
        or receipt.get("source_contract_receipt_sha256")
        != EXPECTED_RESULT["source_contract_receipt_sha256"]
        or receipt.get("source_equation_sha256")
        != "e35cf778d9183861ff48af24466e64d9654bc3e23c5c4bc3b0f9a57b850ecee5"
        or receipt.get("axiom_footprint") != []
        or producer
        != {
            "binders": 2,
            "constructed_nodes": 5,
            "max_binders": 2,
            "max_constructed_nodes": 5,
            "operation": "trace-contract-reflexivity-v1",
        }
        or theorem
        != {
            "content_sha256": "ab9c37a05eb002bbf0da98434207741fa782cfd62c75079c7afb637994e514e3",
            "name": "Axeyum.Autogenesis.IntGcdDef",
            "proof_sha256": "3061c58cd556fb259aaf153ff7c585307e6e44d8d7097ac8daee4780f0779f05",
            "type_sha256": "e35cf778d9183861ff48af24466e64d9654bc3e23c5c4bc3b0f9a57b850ecee5",
        }
        or not isinstance(dependencies, dict)
        or dependencies.get("direct_theorems") != []
    ):
        raise ContractTheoremControlError("semantic theorem contract changed")
    transitive = dependencies.get("transitive_theorems")
    if (
        not isinstance(transitive, list)
        or len(transitive) != 52
        or transitive != sorted(set(transitive))
    ):
        raise ContractTheoremControlError("diagnostic dependency inventory changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-int-gcd-contract-theorem-control"
        or manifest.get("state")
        != "calibration-theorem-receipt-issued-no-evaluation-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT
    ):
        raise ContractTheoremControlError("manifest contract changed")
    policy = manifest["frozen_policy"]
    if sha256(ROOT / policy["path"]) != policy["sha256"]:
        raise ContractTheoremControlError("frozen policy changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise ContractTheoremControlError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise ContractTheoremControlError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise ContractTheoremControlError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_INT_GCD_CONTRACT_THEOREM_CONTROL_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "target=Int.gcd_def|binders=2|nodes=5|invocations=1|axioms=0|"
            "theorem_receipts=1|evaluation=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ContractTheoremControlError,
    ) as error:
        print(f"autogenesis-int-gcd-contract-theorem-control: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
