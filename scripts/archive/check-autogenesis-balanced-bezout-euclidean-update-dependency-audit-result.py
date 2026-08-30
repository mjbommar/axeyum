#!/usr/bin/env python3
"""Verify the exact two-carrier balanced-Bezout dependency audit result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-dependency-audit-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/029ce6f91-balanced-bezout-update-dependency-audit-v1/manifest.json")
AUDIT = MANIFEST.parent / "audit.json"
PLAN_SHA256 = "6d4f77ee296d4cc68bdc78fc49268768505c532c25cd3f66d50bfd4f4fe5b3a3"
MANIFEST_SHA256 = "00eb7464ef7d32de7f9f76ddf940810e6850425272f06f98648b963ee79e0df6"
AUDIT_SHA256 = "a6d66271f3e17cece477056a3e5f904ab9353da6e1f18633533715271769ad51"
CARRIERS = ["Nat.mul_assoc", "Nat.right_distrib"]
CLEAN = ["Eq.symm", "Eq.trans", "Nat.add_assoc", "Nat.left_distrib", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateFourthThenSwapV1", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateLastFiveV1", "congrArg"]


class BalancedBezoutDependencyAuditResultError(RuntimeError):
    """The two-carrier classification, evidence, or zero-authority boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-dependency-audit-result", "nine-roots-classified-two-propext-carriers"):
        raise BalancedBezoutDependencyAuditResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/balanced-bezout-euclidean-update-dependency-audit-plan-v1.json", "sha256": PLAN_SHA256, "commit": "dc3070e68d07db4be69346fa1a8de2efa744c466"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise BalancedBezoutDependencyAuditResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or sha256(AUDIT) != AUDIT_SHA256 or result.get("evidence_pack") != expected_pack:
        raise BalancedBezoutDependencyAuditResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise BalancedBezoutDependencyAuditResultError("evidence pack is not sealed")
    audit = load(AUDIT)
    if audit.get("ordered_roots") != load(PLAN).get("ordered_roots") or audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise BalancedBezoutDependencyAuditResultError("audit population or rendering changed")
    rows = audit.get("rows", [])
    observed_carriers = [row.get("name") for row in rows if row.get("axiom_footprint") == ["propext"]]
    observed_clean = [row.get("name") for row in rows if row.get("axiom_footprint") == []]
    if observed_carriers != CARRIERS or observed_clean != CLEAN:
        raise BalancedBezoutDependencyAuditResultError("audit carrier classification changed")
    summary = result.get("summary", {})
    if summary.get("population") != 9 or summary.get("empty_footprint") != 7 or summary.get("propext_bearing") != 2 or summary.get("other_assumption_bearing") != 0 or summary.get("propext_carriers") != CARRIERS or summary.get("clean_roots") != CLEAN or summary.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise BalancedBezoutDependencyAuditResultError("result summary changed")
    carriers = result.get("carriers", [])
    if [row.get("name") for row in carriers] != CARRIERS or any(row.get("axiom_footprint") != ["propext"] for row in carriers):
        raise BalancedBezoutDependencyAuditResultError("carrier detail changed")
    boundary = {"required_replacements": CARRIERS, "v2_method": "inject exact clean leaf contracts as specialization parameters while retaining the V1 witness map, permutations, and equality chain", "unchanged_update_source_except_leaf_injection": True, "v2_compilation_authorized": False}
    if result.get("next_boundary") != boundary:
        raise BalancedBezoutDependencyAuditResultError("next boundary changed")
    authority = result.get("authority", {})
    if authority.get("dependency_classification_credit") != 1:
        raise BalancedBezoutDependencyAuditResultError("classification credit changed")
    for key in ("euclidean_update_credit", "generic_balanced_bezout_credit", "target_specialization_credit", "cancellation_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutDependencyAuditResultError(f"{key} must remain zero")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_DEPENDENCY_AUDIT_RESULT_OK|roots=9|empty=7|propext=2|carriers=Nat.mul_assoc,Nat.right_distrib|rendered=0|theorem_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutDependencyAuditResultError) as error:
        print(f"autogenesis-balanced-bezout-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
