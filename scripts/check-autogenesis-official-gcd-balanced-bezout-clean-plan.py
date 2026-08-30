#!/usr/bin/env python3
"""Verify the frozen clean official-gcd balanced-Bezout induction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-clean-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_official_gcd_balanced_bezout_clean_v1.lean"
QUOTIENT = ROOT / "artifacts/autogenesis/mod-quotient-witness-kernel-result-v1.json"
CLOSED = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-closed-result-v1.json"
SOURCE_SHA256 = "496473531076f3770f6b853f4d986b261d93113da0a5a9ed6f8968feaf5cc8e5"
QUOTIENT_SHA256 = "1902254357d089a81485476b95ae5c7b76eaa0ebd10b280d1a95ee98b2160a80"
CLOSED_SHA256 = "c23a80590629a77a824506914a77dd17bfd419378682ee54fc2055a6a4393542"
REQUIRED = ["Axeyum.Autogenesis.modQuotientWitnessV4", "Axeyum.Autogenesis.balancedBezoutEuclideanUpdateClosedV1", "Nat.gcd.induction"]
FORBIDDEN_SOURCE = ("rw [", "simp", "ring", "funext", "propext", "Nat.div_eq", "Nat.mod_eq", "Nat.mul_assoc", "Nat.right_distrib")


class OfficialGcdBalancedBezoutCleanPlanError(RuntimeError):
    """The clean gcd induction source, inputs, budget, or zero-specialization authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutCleanPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-clean-plan", "preregistered-gcd-induction-with-two-explicit-gcd-leaves-before-compilation-no-theorem-credit"):
        raise OfficialGcdBalancedBezoutCleanPlanError("plan identity changed")
    if sha256(SOURCE) != SOURCE_SHA256 or plan.get("inputs", {}).get("authored_source", {}).get("sha256") != SOURCE_SHA256:
        raise OfficialGcdBalancedBezoutCleanPlanError("source identity changed")
    if sha256(QUOTIENT) != QUOTIENT_SHA256 or plan.get("inputs", {}).get("quotient_witness_result", {}).get("sha256") != QUOTIENT_SHA256:
        raise OfficialGcdBalancedBezoutCleanPlanError("quotient result changed")
    if sha256(CLOSED) != CLOSED_SHA256 or plan.get("inputs", {}).get("closed_update_result", {}).get("sha256") != CLOSED_SHA256:
        raise OfficialGcdBalancedBezoutCleanPlanError("closed update result changed")
    if any(token in SOURCE.read_text() for token in FORBIDDEN_SOURCE):
        raise OfficialGcdBalancedBezoutCleanPlanError("forbidden tactic or dependency appears in source")
    construction = plan.get("construction", {})
    if construction.get("required_direct_dependencies") != REQUIRED or construction.get("gcd_leaf_specialization_in_this_increment") is not False:
        raise OfficialGcdBalancedBezoutCleanPlanError("gcd induction boundary changed")
    budget = {"max_source_copies": 6, "max_source_compilations": 6, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_gcd_leaf_specializations": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdBalancedBezoutCleanPlanError("execution budget changed")
    authority = plan.get("authority", {})
    for key in ("target_specialization_credit", "cancellation_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise OfficialGcdBalancedBezoutCleanPlanError(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_CLEAN_PLAN_OK|modules=6|compilations<=6|exports<=1|imports<=2|gcd_leaf_specializations=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutCleanPlanError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-clean-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
