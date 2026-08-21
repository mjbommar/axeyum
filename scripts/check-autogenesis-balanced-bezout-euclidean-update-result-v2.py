#!/usr/bin/env python3
"""Verify the accepted parameterized balanced-Bezout Euclidean update V2."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v2.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/0ffd2dbc9-balanced-bezout-euclidean-update-v2-v1/manifest.json")
PLAN_SHA256 = "80f51dd208a8617d9529e16e1e7ffa87828775af1a7bc580a52252b4cd58cb87"
MANIFEST_SHA256 = "0b06492d3c6c6a633f67ccdf88e54dc7a6a50dbc5e5c326143cf4d1a5859a949"
AUDIT_SHA256 = "7d59fe1659af3c96c39f5c51080495aeda6f39972a646b2172bb73104afa6c3b"
DEPENDENCIES = ["Eq.symm", "Eq.trans", "Nat.add_assoc", "Nat.left_distrib", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2.0.Axeyum.Autogenesis.rotateFourthThenSwapV2", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2.0.Axeyum.Autogenesis.rotateLastFiveV2", "congrArg"]
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}


class BalancedBezoutEuclideanUpdateResultV2Error(RuntimeError):
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
        raise BalancedBezoutEuclideanUpdateResultV2Error(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (2, "axeyum-autogenesis-balanced-bezout-euclidean-update-result", "parameterized-update-reconstructed-twice-empty-footprint"):
        raise BalancedBezoutEuclideanUpdateResultV2Error("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v2.json", "sha256": PLAN_SHA256, "commit": "7664c937ad815b94ec41505ab0b68fa3c5db92b1"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise BalancedBezoutEuclideanUpdateResultV2Error("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise BalancedBezoutEuclideanUpdateResultV2Error("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise BalancedBezoutEuclideanUpdateResultV2Error("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutEuclideanUpdateResultV2Error("execution counts changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.balancedBezoutEuclideanUpdateV2" or theorem.get("declaration_sha256") != "3301a38265badc4cffa6d56c953fa3a5af99b37fc7fecce3cdf053110a536e8b" or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES or theorem.get("forbidden_dependencies_present") != [] or theorem.get("audit_sha256") != AUDIT_SHA256 or theorem.get("fresh_reconstructions") != 2 or theorem.get("audits_byte_identical") is not True or theorem.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise BalancedBezoutEuclideanUpdateResultV2Error("theorem measurement changed")
    for name in ("Nat.mul_assoc", "Nat.right_distrib", "propext", "funext"):
        if name in theorem.get("direct_theorem_dependencies", []):
            raise BalancedBezoutEuclideanUpdateResultV2Error(f"forbidden dependency present: {name}")
    for audit in (MANIFEST.parent / "audit-1.json", MANIFEST.parent / "audit-2.json"):
        if sha256(audit) != AUDIT_SHA256:
            raise BalancedBezoutEuclideanUpdateResultV2Error("fresh audits differ")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise BalancedBezoutEuclideanUpdateResultV2Error("cleanup changed")
    boundary = {"euclidean_update_accepted": True, "required_next_increment": "preregister identity-gated composition of the two injected leaf contracts from clean native or target-owned theorems", "leaf_composition_completed": False, "generic_gcd_submission_authorized": False}
    if result.get("next_boundary") != boundary or manifest.get("next_boundary") != boundary:
        raise BalancedBezoutEuclideanUpdateResultV2Error("next boundary changed")
    authority = {"euclidean_update_credit": 1, "leaf_composition_credit": 0, "generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise BalancedBezoutEuclideanUpdateResultV2Error("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_EUCLIDEAN_UPDATE_RESULT_V2_OK|compilations=1|exports=1|imports=2|empty=2/2|leaf_composition=0|generic_gcd=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutEuclideanUpdateResultV2Error) as error:
        print(f"autogenesis-balanced-bezout-euclidean-update-result-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
