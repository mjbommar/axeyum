#!/usr/bin/env python3
"""Verify the exact Int.gcd trace-backed source-contract receipt."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-int-gcd-trace-contract-receipt-v1.json"
EXPECTED_RESULT = {
    "source": "Int.gcd",
    "source_content_sha256": "1b4460e69780e5080a107bc178b77ffe064585b9712c5f7468a80c02cdee0655",
    "residual": ["Nat.gcd"],
    "retained": ["Int", "Int.natAbs"],
    "function_arity": 2,
    "contract_binders": 2,
    "selected_delta_steps": 1,
    "consulted_declarations": ["Int.gcd"],
    "source_axioms": 0,
    "witness_theorems_constructed": 0,
    "receipt_reissued_exactly": True,
    "source_contract_receipts_issued": 1,
    "semantic_theorem_receipts_issued": 0,
    "ledger_writes": 0,
}


class TraceContractReceiptError(RuntimeError):
    """The receipt control changed, weakened, or overclaimed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise TraceContractReceiptError(f"{path} is not an object")
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
        raise TraceContractReceiptError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "source_contract_receipts_issued": 1,
        "semantic_theorem_receipts_issued": 0,
        "producer_target_attempts": 0,
        "ledger_writes": 0,
    }
    source = observation.get("source")
    receipt = observation.get("receipt")
    assurance = observation.get("assurance")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-int-gcd-trace-contract-receipt-control"
        or observation.get("state")
        != "source-contract-receipt-issued-no-theorem-or-ledger-credit"
        or observation.get("authority") != expected_authority
        or not isinstance(source, dict)
        or not isinstance(receipt, dict)
        or not isinstance(assurance, dict)
    ):
        raise TraceContractReceiptError("observation authority changed")
    if (
        source.get("artifact_file") != "r018.ndjson"
        or source.get("lean_version") != "4.30.0"
        or source.get("lean_githash") != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or source.get("definition") != "Int.gcd"
        or source.get("definition_content_sha256")
        != EXPECTED_RESULT["source_content_sha256"]
    ):
        raise TraceContractReceiptError("source identity changed")
    source_receipt = receipt.get("source")
    contract = receipt.get("contract")
    delta = receipt.get("delta")
    residual = receipt.get("residual")
    retained = receipt.get("retained")
    if (
        receipt.get("schema_version")
        != "axeyum-trace-backed-source-contract-receipt-v1"
        or receipt.get("policy_version") != "mathlib-int-gcd-trace-backed-contract-v1"
        or not isinstance(receipt.get("receipt_sha256"), str)
        or len(receipt["receipt_sha256"]) != 64
        or not isinstance(source_receipt, dict)
        or not isinstance(contract, dict)
        or not isinstance(delta, dict)
        or not isinstance(residual, list)
        or not isinstance(retained, list)
    ):
        raise TraceContractReceiptError("receipt envelope changed")
    if (
        source_receipt.get("name") != "Int.gcd"
        or source_receipt.get("role") != "source"
        or source_receipt.get("binder_name") != "intGcd"
        or source_receipt.get("content_sha256")
        != EXPECTED_RESULT["source_content_sha256"]
        or source_receipt.get("level_sha256") != []
        or receipt.get("source_axiom_footprint") != []
    ):
        raise TraceContractReceiptError("receipt source changed")
    if (
        len(residual) != 1
        or residual[0].get("name") != "Nat.gcd"
        or residual[0].get("role") != "residual"
        or residual[0].get("binder_name") != "natGcd"
        or [item.get("name") for item in retained] != ["Int", "Int.natAbs"]
        or any(item.get("role") != "retained" for item in retained)
    ):
        raise TraceContractReceiptError("receipt instance partition changed")
    if (
        contract.get("function_arity") != 2
        or contract.get("binders") != 2
        or not isinstance(contract.get("source_equation_sha256"), str)
        or len(contract["source_equation_sha256"]) != 64
        or not isinstance(contract.get("generalized_sha256"), str)
        or len(contract["generalized_sha256"]) != 64
        or delta.get("rule") != "selected-transparent-definition-delta-v1"
        or delta.get("consulted_declarations") != ["Int.gcd"]
        or not isinstance(delta.get("before_sha256"), str)
        or len(delta["before_sha256"]) != 64
        or not isinstance(delta.get("after_sha256"), str)
        or len(delta["after_sha256"]) != 64
    ):
        raise TraceContractReceiptError("receipt contract or delta changed")
    if assurance != {
        "receipt_reissued_exactly": True,
        "source_axioms": 0,
        "selected_delta_steps": 1,
        "consulted_declarations": ["Int.gcd"],
        "residual_constants_left_opaque": ["Nat.gcd"],
        "witness_theorems_constructed": 0,
        "theorem_dependency_walks_for_delta": 0,
    }:
        raise TraceContractReceiptError("receipt assurance changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-int-gcd-trace-contract-receipt"
        or manifest.get("state")
        != "source-contract-receipt-issued-no-theorem-or-ledger-credit"
        or manifest.get("result") != EXPECTED_RESULT
    ):
        raise TraceContractReceiptError("manifest contract changed")
    tooling = manifest["tooling_file"]
    result = subprocess.run(
        ["git", "show", f"{manifest['tooling_commit']}:{tooling['path']}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode or hashlib.sha256(result.stdout).hexdigest() != tooling["sha256"]:
        raise TraceContractReceiptError("tooling identity changed")
    archive = manifest["observation_archive"]
    root = pathlib.Path(archive["root"])
    path = root / archive["file"]
    if (
        sha256(path) != archive["file_sha256"]
        or path.stat().st_size != archive["bytes"]
        or stat.S_IMODE(path.stat().st_mode) != 0o444
        or stat.S_IMODE(root.stat().st_mode) != 0o555
    ):
        raise TraceContractReceiptError("external observation changed or is mutable")
    observation = load(path)
    if observation.get("observation_sha256") != archive["observation_sha256"]:
        raise TraceContractReceiptError("external semantic identity changed")
    validate_observation(observation)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_INT_GCD_TRACE_CONTRACT_RECEIPT_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "source=Int.gcd|residual=Nat.gcd|source_axioms=0|"
            "contract_receipts=1|theorem_receipts=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        TraceContractReceiptError,
    ) as error:
        print(f"autogenesis-int-gcd-trace-contract-receipt: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
