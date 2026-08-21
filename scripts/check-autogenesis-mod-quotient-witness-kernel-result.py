#!/usr/bin/env python3
"""Verify the twice-reconstructed, axiom-free pointwise quotient witness."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mod-quotient-witness-kernel-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mod-quotient-witness-kernel-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/eb061c9bf-mod-quotient-witness-v4-v1/manifest.json")
PLAN_SHA256 = "fe0a275c11442318044fdf4bb71be9befeab7c85ac2bfa89c9c3684364ffb2f2"
MANIFEST_SHA256 = "63d81f827241a829fdf8b70616646c23f1519f7b615ac2b9e0ebce2b0c5913a8"
AUDIT_SHA256 = "e184dbccb7643f0f2435c5a6920e7c956baf9d8ff0cc1b47e058b8e90402744d"
DECLARATION_SHA256 = "6da60d36575a3aebdfd99ed4f01a5532ef925487e50d48a5d4f4210cf65e0a55"
EXECUTION = {"source_copies": 2, "compiler_invocations": 2, "successful_compilations": 2, "exporter_invocations": 1, "importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 6, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
DEPENDENCIES = ["Axeyum.Autogenesis.divModGoReconstruct", "Eq.symm", "Nat.lt_succ_self", "Nat.mod.eq_1", "Nat.mod.eq_2", "Nat.mul_zero", "Nat.zero_add", "congrArg", "dif_pos", "if_neg", "if_pos"]


class ModQuotientWitnessResultError(RuntimeError):
    """The accepted theorem, evidence identity, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ModQuotientWitnessResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-mod-quotient-witness-kernel-result", "reconstructed-twice-empty-footprint"):
        raise ModQuotientWitnessResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/mod-quotient-witness-kernel-plan-v1.json", "sha256": PLAN_SHA256, "commit": "b9ee73f791807ad20ea75f1895dba42b4887feaa"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise ModQuotientWitnessResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise ModQuotientWitnessResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise ModQuotientWitnessResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise ModQuotientWitnessResultError("execution counts changed")
    theorem = result.get("theorem")
    if not isinstance(theorem, dict):
        raise ModQuotientWitnessResultError("theorem record is missing")
    expected_theorem = {
        "name": "Axeyum.Autogenesis.modQuotientWitnessV4",
        "contract": "forall m n, 0 < m -> exists q, m * q + Nat.mod n m = n",
        "declaration_sha256": DECLARATION_SHA256,
        "audit_sha256": AUDIT_SHA256,
        "fresh_reconstructions": 2,
        "audits_byte_identical": True,
        "axiom_footprint": [],
        "direct_theorem_dependencies": DEPENDENCIES,
        "forbidden_dependencies_present": [],
    }
    if theorem != expected_theorem or manifest.get("theorem", {}).get("axiom_footprint") != [] or manifest.get("theorem", {}).get("direct_theorem_dependencies") != DEPENDENCIES:
        raise ModQuotientWitnessResultError("theorem measurement changed")
    pack = MANIFEST.parent
    audits = [pack / "audit-1.json", pack / "audit-2.json"]
    if any(sha256(path) != AUDIT_SHA256 for path in audits):
        raise ModQuotientWitnessResultError("fresh audits are not byte-identical")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise ModQuotientWitnessResultError("cleanup changed")
    next_boundary = {"quotient_witness_accepted": True, "required_next_increment": "preregister and reconstruct an explicit balanced Bezout Euclidean update over the existing four-Nat carrier without binder rewriting, function equality, public quotient, or ring normalization", "reuse_as_balanced_bezout_credit": False}
    if result.get("next_boundary") != next_boundary:
        raise ModQuotientWitnessResultError("next boundary changed")
    authority = {"quotient_witness_credit": 1, "balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise ModQuotientWitnessResultError("authority changed")
    if result.get("verification") != "python3 scripts/check-autogenesis-mod-quotient-witness-kernel-result.py":
        raise ModQuotientWitnessResultError("verification changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_MOD_QUOTIENT_WITNESS_RESULT_OK|compilations=2|exports=1|imports=2|empty=2/2|baseline=3|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ModQuotientWitnessResultError) as error:
        print(f"autogenesis-mod-quotient-witness-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
