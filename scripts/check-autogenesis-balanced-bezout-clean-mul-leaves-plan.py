#!/usr/bin/env python3
"""Verify the frozen primitive-induction clean multiplication-leaf plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-clean-mul-leaves-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_balanced_bezout_clean_mul_leaves_v1.lean"
PREVIOUS = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-result-v2.json"
SOURCE_SHA256 = "2c925db23b545067f1842b5914bce79990f94e576ff093bd79717f2a978aad89"
PREVIOUS_SHA256 = "acf28ea301b77acd6844c5fbbdd2bc09bd277942d5e1d4685491babfcbed6e60"
FORBIDDEN_SOURCE = ("rw [", "simp", "ring", "funext", "propext", "Nat.div", "Nat.mul_assoc", "Nat.right_distrib")
TARGETS = ["Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1"]


class BalancedBezoutCleanMulLeavesPlanError(RuntimeError):
    """The exact two-leaf source, budget, or zero-composition authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutCleanMulLeavesPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-clean-mul-leaves-plan", "preregistered-primitive-induction-two-leaf-source-before-compilation-no-theorem-credit"):
        raise BalancedBezoutCleanMulLeavesPlanError("plan identity changed")
    if sha256(SOURCE) != SOURCE_SHA256 or plan.get("inputs", {}).get("authored_source", {}).get("sha256") != SOURCE_SHA256:
        raise BalancedBezoutCleanMulLeavesPlanError("source identity changed")
    if sha256(PREVIOUS) != PREVIOUS_SHA256 or plan.get("inputs", {}).get("accepted_parameterized_update", {}).get("sha256") != PREVIOUS_SHA256:
        raise BalancedBezoutCleanMulLeavesPlanError("accepted update identity changed")
    if any(token in SOURCE.read_text() for token in FORBIDDEN_SOURCE):
        raise BalancedBezoutCleanMulLeavesPlanError("forbidden tactic or dependency appears in source")
    if [target.get("name") for target in plan.get("construction", {}).get("targets", [])] != TARGETS:
        raise BalancedBezoutCleanMulLeavesPlanError("target population changed")
    for key in ("rewriting_tactic_used", "simplification_tactic_used", "ring_normalization_used", "public_division_used"):
        if plan.get("construction", {}).get(key) is not False:
            raise BalancedBezoutCleanMulLeavesPlanError(f"{key} must remain false")
    budget = {"max_source_copies": 1, "max_source_compilations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 2, "max_update_compositions": 0, "max_generic_gcd_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise BalancedBezoutCleanMulLeavesPlanError("execution budget changed")
    authority = plan.get("authority", {})
    for key in ("euclidean_update_composition_credit", "generic_balanced_bezout_credit", "target_specialization_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutCleanMulLeavesPlanError(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_CLEAN_MUL_LEAVES_PLAN_OK|targets=2|compilations<=1|exports<=1|imports<=2|update_compositions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutCleanMulLeavesPlanError) as error:
        print(f"autogenesis-balanced-bezout-clean-mul-leaves-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
