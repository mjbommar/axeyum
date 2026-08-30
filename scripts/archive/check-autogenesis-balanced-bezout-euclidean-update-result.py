#!/usr/bin/env python3
"""Verify the explicit balanced-Bezout update's first-import decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/5a2d0d397-balanced-bezout-euclidean-update-v1/manifest.json")
PLAN_SHA256 = "e098fcedfd78866bf33cae386bf69ea14f698a582bcd1c1a51b5b9140d6f0adb"
MANIFEST_SHA256 = "20c86d1f3bf95b69cb2484e847393f126680f9453406713a0c080e1a8208126c"
AUDIT_SHA256 = "b2f52dd054994c21e193e4f0611f4f0cdf8d88f1c8757fc1b6764ac6d8c7557c"
DEPENDENCIES = ["Eq.symm", "Eq.trans", "Nat.add_assoc", "Nat.left_distrib", "Nat.mul_assoc", "Nat.right_distrib", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateFourthThenSwapV1", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateLastFiveV1", "congrArg"]
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 1, "proof_bearing_stream_reads": 1, "second_import_forbidden_by_first_gate": True, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}


class BalancedBezoutEuclideanUpdateResultError(RuntimeError):
    """The measured decline, evidence identity, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutEuclideanUpdateResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-result", "compiled-exported-first-import-propext-second-import-forbidden"):
        raise BalancedBezoutEuclideanUpdateResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v1.json", "sha256": PLAN_SHA256, "commit": "8dc795c1a857599bd83c37ba71c399f1500c3ff4"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise BalancedBezoutEuclideanUpdateResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise BalancedBezoutEuclideanUpdateResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise BalancedBezoutEuclideanUpdateResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutEuclideanUpdateResultError("execution counts changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.balancedBezoutEuclideanUpdateV1" or theorem.get("declaration_sha256") != "6c4cabffc2b519de087c3b31efd85d8b5b76239b4a4c87687d2224af865fe0c5" or theorem.get("axiom_footprint") != ["propext"] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES or theorem.get("first_audit_sha256") != AUDIT_SHA256 or theorem.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise BalancedBezoutEuclideanUpdateResultError("theorem measurement changed")
    if manifest.get("theorem") != theorem:
        raise BalancedBezoutEuclideanUpdateResultError("manifest theorem differs")
    if sha256(MANIFEST.parent / "audit-1.json") != AUDIT_SHA256:
        raise BalancedBezoutEuclideanUpdateResultError("first audit identity changed")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise BalancedBezoutEuclideanUpdateResultError("cleanup changed")
    boundary = {"euclidean_update_accepted": False, "required_next_increment": "preregister one dependency-local footprint audit over the exact nine direct theorem dependencies from the first audit before changing source", "reuse_compilation_as_theorem_credit": False}
    if result.get("next_boundary") != boundary or manifest.get("next_boundary") != boundary:
        raise BalancedBezoutEuclideanUpdateResultError("next boundary changed")
    authority = {"euclidean_update_credit": 0, "generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise BalancedBezoutEuclideanUpdateResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_EUCLIDEAN_UPDATE_DECLINE_OK|compilations=1|exports=1|imports=1/2|footprint=propext|baseline=3|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutEuclideanUpdateResultError) as error:
        print(f"autogenesis-balanced-bezout-euclidean-update-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
