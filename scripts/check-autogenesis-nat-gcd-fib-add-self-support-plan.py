#!/usr/bin/env python3
"""Verify the preregistered support-first Nat.gcd_fib_add_self plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-support-plan-v1.json"


class PlanError(RuntimeError):
    """The fixed route, budget, evidence inputs, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-gcd-fib-add-self-support-plan"
        or plan.get("state")
        != "preregistered-support-first-no-execution-or-proof-credit"
        or plan.get("policy_version") != "nat-gcd-fib-add-self-support-first-v1"
    ):
        raise PlanError("plan identity changed")

    inputs = plan["inputs"]
    qualification = inputs["qualification"]
    if sha256(ROOT / qualification["path"]) != qualification["sha256"]:
        raise PlanError("qualification identity changed")
    target_fact = load(ROOT / inputs["target_fact"]["path"])
    premise_fact = load(ROOT / inputs["premise_fact"]["path"])
    target = plan["target"]
    target_status = target_fact.get("epistemic_status")
    target_evidence = target_fact.get("evidence")
    target_state_valid = (
        target_status == "open"
        and target_evidence == []
        and not any(
            key in target_fact for key in ("proof_route", "axiom_footprint")
        )
    ) or (
        target_status == "proved"
        and target_fact.get("proof_route") == "kernel-lean"
        and target_fact.get("axiom_footprint") == []
        and isinstance(target_evidence, list)
        and len(target_evidence) == 1
        and target_evidence[0].get("kind") == "kernel-term"
        and target_evidence[0].get("check_status") == "checked"
    )
    if (
        target["fact_id"] != "F:ml430-nat-gcd-fib-add-self-5a92d5e3"
        or target["source_name"] != "Nat.gcd_fib_add_self"
        or target["target_definition"] != "Axeyum.Autogenesis.Coverage.r091"
        or target["stream_sha256"]
        != "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2"
        or target_fact.get("formal", {}).get("statement") != target["statement"]
        or target_fact.get("depends_on") != target["ledger_premises"]
        or not target_state_valid
    ):
        raise PlanError("target identity or monotonic state changed")

    premise = inputs["premise_fact"]
    evidence = premise_fact.get("evidence")
    binding = evidence[0].get("checker_operation") if isinstance(evidence, list) and len(evidence) == 1 else None
    if (
        premise_fact.get("epistemic_status") != "proved"
        or premise_fact.get("proof_route") != "kernel-lean"
        or premise_fact.get("axiom_footprint") != []
        or not isinstance(binding, dict)
        or binding.get("receipt_sha256") != premise["receipt_sha256"]
        or binding.get("dependency_set_sha256") != premise["dependency_set_sha256"]
        or binding.get("execution_sha256") != premise["execution_sha256"]
    ):
        raise PlanError("settled premise evidence changed")

    fixed = plan["fixed_plan"]
    supports = fixed["support_order"]
    if (
        fixed.get("templates") != 1
        or [row.get("id") for row in supports]
        != [
            "fibonacci-successor-addition-v1",
            "coprime-factor-divisibility-cancellation-v1",
        ]
        or [row.get("fresh_reconstructions") for row in supports] != [2, 2]
        or [row.get("role") for row in supports]
        != ["reusable-library-support", "reusable-library-support"]
        or fixed.get("target_construction", {}).get("id")
        != "nat-gcd-fib-add-self-v1"
        or fixed.get("target_construction", {}).get("fresh_reconstructions") != 2
        or len(fixed.get("target_construction", {}).get("successor_steps", [])) != 5
    ):
        raise PlanError("fixed construction changed")

    if plan["budget"] != {
        "max_plan_templates": 1,
        "max_support_theorem_declarations": 2,
        "max_target_theorem_declarations": 1,
        "fresh_reconstructions_per_declaration": 2,
        "max_kernel_theorem_submissions": 6,
        "max_exact_source_target_submissions": 2,
        "max_executor_invocations": 1,
        "max_retries": 0,
    }:
        raise PlanError("budget changed")
    if plan["gates"] != {
        "support_before_target": True,
        "both_support_receipts_must_replay": True,
        "exact_target_type_must_match_r091": True,
        "direct_theorem_dependencies_must_be_enumerated": True,
        "complete_axiom_footprint_must_be_empty": True,
        "failed_or_partial_private_kernels_must_not_publish": True,
    }:
        raise PlanError("gates changed")
    if plan["selection_prestate"] != {
        "registered_operation_ids": [],
        "executor_invocations": 0,
        "kernel_theorem_submissions": 0,
        "exact_source_target_submissions": 0,
        "semantic_theorem_receipts": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("selection prestate changed")
    if plan["authority"] != {
        "partitions_allowed": ["train"],
        "held_out_allowed": False,
        "proof_bodies_allowed": False,
        "historical_target_outcomes_are_inputs": False,
        "unregistered_target_execution_allowed": False,
        "admission_allowed": False,
    }:
        raise PlanError("authority changed")
    return plan


def main() -> int:
    try:
        plan = validate()
        budget = plan["budget"]
        print(
            "AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_SUPPORT_PLAN_OK|"
            "supports=2|target=1|reconstructions=2|"
            f"kernel_submissions=0/{budget['max_kernel_theorem_submissions']}|"
            f"target_submissions=0/{budget['max_exact_source_target_submissions']}|"
            "executions=0/1|retries=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-support-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
