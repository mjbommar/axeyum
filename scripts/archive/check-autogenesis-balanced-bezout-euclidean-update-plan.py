#!/usr/bin/env python3
"""Verify the frozen explicit balanced-Bezout Euclidean update plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_balanced_bezout_euclidean_update_v1.lean"
PREVIOUS = ROOT / "artifacts/autogenesis/mod-quotient-witness-kernel-result-v1.json"
SOURCE_SHA256 = "4304249442dbae993df785e1c744c659d427782cdab58a67389591a9d3b8327f"
PREVIOUS_SHA256 = "1902254357d089a81485476b95ae5c7b76eaa0ebd10b280d1a95ee98b2160a80"
FORBIDDEN_SOURCE = ("rw [", "simp", "ring", "funext", "propext", "Nat.div")


class BalancedBezoutEuclideanUpdatePlanError(RuntimeError):
    """The frozen source, execution ceiling, or zero-authority boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutEuclideanUpdatePlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-plan", "preregistered-explicit-nat-equality-chain-before-compilation-no-theorem-credit"):
        raise BalancedBezoutEuclideanUpdatePlanError("plan identity changed")
    if sha256(SOURCE) != SOURCE_SHA256 or plan.get("inputs", {}).get("authored_source") != {"path": "scripts/lean/autogenesis_balanced_bezout_euclidean_update_v1.lean", "sha256": SOURCE_SHA256}:
        raise BalancedBezoutEuclideanUpdatePlanError("authored source identity changed")
    if sha256(PREVIOUS) != PREVIOUS_SHA256 or plan.get("inputs", {}).get("accepted_quotient_witness_result", {}).get("sha256") != PREVIOUS_SHA256:
        raise BalancedBezoutEuclideanUpdatePlanError("accepted predecessor identity changed")
    source = SOURCE.read_text()
    if any(token in source for token in FORBIDDEN_SOURCE):
        raise BalancedBezoutEuclideanUpdatePlanError("forbidden tactic or dependency appears in source")
    construction = plan.get("construction", {})
    if construction.get("witness_map") != {"new_mp": "np + q*mn", "new_mn": "nn + q*mp", "new_np": "mp", "new_nn": "mn"}:
        raise BalancedBezoutEuclideanUpdatePlanError("witness map changed")
    for key in ("public_quotient_used", "rewrite_under_binder_used", "ring_normalization_used", "tactic_simplification_used"):
        if construction.get(key) is not False:
            raise BalancedBezoutEuclideanUpdatePlanError(f"{key} must remain false")
    budget = plan.get("budget", {})
    expected_budget = {"max_source_copies": 1, "max_source_compilations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_generic_gcd_submissions": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if budget != expected_budget:
        raise BalancedBezoutEuclideanUpdatePlanError("execution budget changed")
    acceptance = plan.get("acceptance", {})
    if acceptance.get("fresh_kernel_imports_required") != 2 or acceptance.get("axiom_footprints_must_be_empty") is not True or acceptance.get("failed_compilation_or_first_import_ends_increment") is not True:
        raise BalancedBezoutEuclideanUpdatePlanError("acceptance gate changed")
    authority = plan.get("authority", {})
    for key in ("generic_balanced_bezout_credit", "target_specialization_credit", "cancellation_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutEuclideanUpdatePlanError(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_EUCLIDEAN_UPDATE_PLAN_OK|compilations<=1|exports<=1|imports<=2|retries=0|generic_gcd=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutEuclideanUpdatePlanError) as error:
        print(f"autogenesis-balanced-bezout-euclidean-update-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
