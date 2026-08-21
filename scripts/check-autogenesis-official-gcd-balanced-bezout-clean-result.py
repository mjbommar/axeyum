#!/usr/bin/env python3
"""Verify the accepted generic official-gcd balanced-Bezout theorem."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-clean-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-clean-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/13038b3ff-official-gcd-balanced-bezout-clean-v1/manifest.json")
PLAN_SHA256 = "78c8bec030c38ca8ce10f32c735ef78c9699ccceedf63d98b2e6915575c1b58b"
MANIFEST_SHA256 = "e8d360d5b84d174e87b64e0d901ed28a7c626c98d85dd5d3c9067e959619527c"
AUDIT_SHA256 = "bd9aeb3b9e7146dd4e12da257eeaf95d98e95aeeba78dcd24030bc213887a95c"
DEPENDENCIES = ["Axeyum.Autogenesis.balancedBezoutEuclideanUpdateClosedV1", "Axeyum.Autogenesis.modQuotientWitnessV4", "Eq.symm", "Eq.trans", "Nat.gcd.induction", "Nat.not_lt_zero", "Nat.zero_add", "Nat.zero_lt_succ", "congrArg"]
EXECUTION = {"source_copies": 6, "compiler_invocations": 6, "successful_compilations": 6, "exporter_invocations": 1, "importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}


class OfficialGcdBalancedBezoutCleanResultError(RuntimeError):
    """The theorem, evidence, cleanup, or bounded authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutCleanResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-clean-result", "generic-gcd-balanced-bezout-reconstructed-twice-empty-footprint"):
        raise OfficialGcdBalancedBezoutCleanResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-clean-plan-v1.json", "sha256": PLAN_SHA256, "commit": "99ea0b1e7f039d7959d617080d6aed96f015cf14"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdBalancedBezoutCleanResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdBalancedBezoutCleanResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdBalancedBezoutCleanResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdBalancedBezoutCleanResultError("execution changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1" or theorem.get("declaration_sha256") != "feb1c3e41dd2f745261002b3876ddab750db5777226956ddbb07d805b4abc9ec" or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES or theorem.get("audit_sha256") != AUDIT_SHA256 or theorem.get("fresh_reconstructions") != 2 or theorem.get("audits_byte_identical") is not True:
        raise OfficialGcdBalancedBezoutCleanResultError("theorem measurement changed")
    for path in (MANIFEST.parent / "audit-1.json", MANIFEST.parent / "audit-2.json"):
        if sha256(path) != AUDIT_SHA256:
            raise OfficialGcdBalancedBezoutCleanResultError("fresh audits differ")
    cleanup = {"exact_temporary_paths_removed": 18, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
    if result.get("cleanup") != cleanup or manifest.get("cleanup") != cleanup:
        raise OfficialGcdBalancedBezoutCleanResultError("cleanup changed")
    boundary = {"generic_theorem_accepted": True, "required_next_increment": "preregister closed specialization to accepted gcdZeroLeft and gcdSucc leaves", "gcd_leaf_specialization_completed": False, "cancellation_authorized": False}
    if result.get("next_boundary") != boundary or manifest.get("next_boundary") != boundary:
        raise OfficialGcdBalancedBezoutCleanResultError("next boundary changed")
    authority = {"generic_balanced_bezout_credit": 1, "gcd_leaf_specialization_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise OfficialGcdBalancedBezoutCleanResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_CLEAN_RESULT_OK|compilations=6|exports=1|imports=2|empty=2/2|gcd_leaf_specialization=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutCleanResultError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-clean-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
