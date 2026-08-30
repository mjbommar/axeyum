#!/usr/bin/env python3
"""Verify the frozen two-leaf-parameter balanced-Bezout V2 plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v2.json"
SOURCE = ROOT / "scripts/lean/autogenesis_balanced_bezout_euclidean_update_v2.lean"
V1 = ROOT / "scripts/lean/autogenesis_balanced_bezout_euclidean_update_v1.lean"
AUDIT_RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-dependency-audit-result-v1.json"
SOURCE_SHA256 = "a589b50e7743a4853f9c5eb5d0e970e6e5c40afb58bf7cd59f5a00e0094afd40"
V1_SHA256 = "4304249442dbae993df785e1c744c659d427782cdab58a67389591a9d3b8327f"
AUDIT_RESULT_SHA256 = "c29041f152abf8ff7b4d7431100bb387596b7e7522afbb9341bcb3bf44a21d11"
FORBIDDEN_SOURCE = ("rw [", "simp", "ring", "funext", "propext", "Nat.div", "Nat.mul_assoc", "Nat.right_distrib")


class BalancedBezoutEuclideanUpdatePlanV2Error(RuntimeError):
    """The exact leaf injection, frozen source, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutEuclideanUpdatePlanV2Error(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (2, "axeyum-autogenesis-balanced-bezout-euclidean-update-plan", "preregistered-two-clean-leaf-parameters-before-compilation-no-theorem-credit"):
        raise BalancedBezoutEuclideanUpdatePlanV2Error("plan identity changed")
    if sha256(SOURCE) != SOURCE_SHA256 or plan.get("inputs", {}).get("authored_source", {}).get("sha256") != SOURCE_SHA256:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("V2 source identity changed")
    if sha256(V1) != V1_SHA256 or plan.get("inputs", {}).get("v1_source", {}).get("sha256") != V1_SHA256:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("V1 source identity changed")
    if sha256(AUDIT_RESULT) != AUDIT_RESULT_SHA256 or plan.get("inputs", {}).get("dependency_audit_result", {}).get("sha256") != AUDIT_RESULT_SHA256:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("dependency audit identity changed")
    source = SOURCE.read_text()
    if any(token in source for token in FORBIDDEN_SOURCE):
        raise BalancedBezoutEuclideanUpdatePlanV2Error("forbidden tactic or dependency appears in V2 source")
    construction = plan.get("construction", {})
    if construction.get("replaced_dependencies") != ["Nat.mul_assoc", "Nat.right_distrib"] or construction.get("injected_leaf_contracts") != ["forall a b c : Nat, a*b*c = a*(b*c)", "forall a b c : Nat, (a+b)*c = a*c+b*c"]:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("exact leaf injection changed")
    if construction.get("witness_map") != {"new_mp": "np + q*mn", "new_mn": "nn + q*mp", "new_np": "mp", "new_nn": "mn"}:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("witness map changed")
    for key in ("public_quotient_used", "rewrite_under_binder_used", "ring_normalization_used", "tactic_simplification_used"):
        if construction.get(key) is not False:
            raise BalancedBezoutEuclideanUpdatePlanV2Error(f"{key} must remain false")
    budget = {"max_source_copies": 1, "max_source_compilations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_leaf_compositions": 0, "max_generic_gcd_submissions": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise BalancedBezoutEuclideanUpdatePlanV2Error("execution budget changed")
    authority = plan.get("authority", {})
    for key in ("generic_balanced_bezout_credit", "target_specialization_credit", "cancellation_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutEuclideanUpdatePlanV2Error(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_EUCLIDEAN_UPDATE_PLAN_V2_OK|leaf_params=2|compilations<=1|exports<=1|imports<=2|leaf_compositions=0|generic_gcd=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutEuclideanUpdatePlanV2Error) as error:
        print(f"autogenesis-balanced-bezout-euclidean-update-plan-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
