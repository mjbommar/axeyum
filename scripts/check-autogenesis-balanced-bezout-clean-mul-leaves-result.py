#!/usr/bin/env python3
"""Verify the accepted target-owned clean multiplication leaves."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-clean-mul-leaves-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-clean-mul-leaves-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/616fe5d01-balanced-bezout-clean-mul-leaves-v1/manifest.json")
PLAN_SHA256 = "6183d4a1c3089b7f080e42d5d0b6944b2de30eb87cb3410f70e3dc2332fb7a0b"
MANIFEST_SHA256 = "434b9490f1b317d037f5b9cad0799e09620b320650cdede4c34f02a045d1d61b"
AUDIT_SHA256 = "ef1aadf35c8c91a0dc0ef2d82abcd22639a800396cc619630a82a072043f117a"
THEOREMS = [
    {"name": "Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "contract": "forall a b c : Nat, a*b*c = a*(b*c)", "declaration_sha256": "3e1ef3dc51f2702b9b457e5621457542c07757b30a57cede7db9e5b7273f7c00", "axiom_footprint": [], "direct_theorem_dependencies": ["Eq.symm", "Eq.trans", "Nat.left_distrib", "congrArg"]},
    {"name": "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1", "contract": "forall a b c : Nat, (a+b)*c = a*c+b*c", "declaration_sha256": "7d41f955bf36b0825b925ec0d1d31b0df7551c0b413b0ed6cca4fcef1d833f05", "axiom_footprint": [], "direct_theorem_dependencies": ["Eq.trans", "_private.AxeyumAutogenesisBalancedBezoutCleanMulLeavesV1.0.Axeyum.Autogenesis.swapMiddleFourV1", "congrArg"]},
]
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}


class BalancedBezoutCleanMulLeavesResultError(RuntimeError):
    """The two accepted leaves, evidence, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutCleanMulLeavesResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-clean-mul-leaves-result", "two-target-owned-leaves-reconstructed-twice-empty-footprint"):
        raise BalancedBezoutCleanMulLeavesResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/balanced-bezout-clean-mul-leaves-plan-v1.json", "sha256": PLAN_SHA256, "commit": "5c66b82074dd57a34609894f338bda9ec408d78b"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise BalancedBezoutCleanMulLeavesResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise BalancedBezoutCleanMulLeavesResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise BalancedBezoutCleanMulLeavesResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutCleanMulLeavesResultError("execution changed")
    if result.get("theorems") != THEOREMS:
        raise BalancedBezoutCleanMulLeavesResultError("theorem measurements changed")
    manifest_theorems = manifest.get("theorems", [])
    for expected, observed in zip(THEOREMS, manifest_theorems, strict=True):
        if {key: expected[key] for key in ("name", "declaration_sha256", "axiom_footprint", "direct_theorem_dependencies")} != observed:
            raise BalancedBezoutCleanMulLeavesResultError("manifest theorem differs")
    audit = {"sha256": AUDIT_SHA256, "fresh_reconstructions_per_target": 2, "audits_byte_identical": True, "all_roots_empty": True, "forbidden_dependencies_present": [], "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}}
    if result.get("audit") != audit or manifest.get("audit") != audit:
        raise BalancedBezoutCleanMulLeavesResultError("audit contract changed")
    for path in (MANIFEST.parent / "audit-1.json", MANIFEST.parent / "audit-2.json"):
        if sha256(path) != AUDIT_SHA256:
            raise BalancedBezoutCleanMulLeavesResultError("fresh audits differ")
    cleanup = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
    if result.get("cleanup") != cleanup or manifest.get("cleanup") != cleanup:
        raise BalancedBezoutCleanMulLeavesResultError("cleanup changed")
    boundary = {"clean_leaf_credit": 2, "required_next_increment": "preregister a closed wrapper applying the accepted V2 update to these exact leaves", "euclidean_update_composition_completed": False, "generic_gcd_submission_authorized": False}
    if result.get("next_boundary") != boundary or manifest.get("next_boundary") != boundary:
        raise BalancedBezoutCleanMulLeavesResultError("next boundary changed")
    authority = {"clean_leaf_credit": 2, "euclidean_update_composition_credit": 0, "generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise BalancedBezoutCleanMulLeavesResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_CLEAN_MUL_LEAVES_RESULT_OK|targets=2|imports=2|empty=4/4|update_composition=0|generic_gcd=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutCleanMulLeavesResultError) as error:
        print(f"autogenesis-balanced-bezout-clean-mul-leaves-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
