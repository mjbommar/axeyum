#!/usr/bin/env python3
"""Verify the preregistered constructive Euclidean bridge plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-euclidean-bridge-plan-v1.json"


class PlanError(RuntimeError):
    """The bridge route, evidence, budget, or authority changed."""


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
        != "axeyum-autogenesis-mathlib-nat-gcd-fib-add-self-euclidean-bridge-plan"
        or plan.get("state")
        != "preregistered-bridge-no-execution-or-target-credit"
        or plan.get("policy_version")
        != "nat-gcd-fib-add-self-euclidean-bridge-v1"
    ):
        raise PlanError("plan identity changed")

    inputs = plan["inputs"]
    support = inputs["support_result"]
    if sha256(ROOT / support["path"]) != support["sha256"]:
        raise PlanError("support result identity changed")
    target_fact = load(ROOT / inputs["target_fact"]["path"])
    target_status = target_fact.get("epistemic_status")
    if target_status == "open":
        target_state_valid = (
            sha256(ROOT / inputs["target_fact"]["path"])
            == inputs["target_fact"]["sha256_at_plan"]
            and target_fact.get("evidence") == []
            and not any(
                key in target_fact for key in ("proof_route", "axiom_footprint")
            )
        )
    else:
        evidence = target_fact.get("evidence")
        target_state_valid = (
            target_status == "proved"
            and target_fact.get("proof_route") == "kernel-lean"
            and target_fact.get("axiom_footprint") == []
            and isinstance(evidence, list)
            and len(evidence) == 1
            and evidence[0].get("kind") == "kernel-term"
            and evidence[0].get("check_status") == "checked"
        )
    if not target_state_valid:
        raise PlanError(
            "target fact is neither the frozen open target nor a checked closure"
        )

    for key in ("statement_inventory", "mod_equation_pack", "division_support_audit"):
        source = inputs[key]
        path = pathlib.Path(source["path"])
        if (
            source.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or sha256(path) != source["sha256"]
        ):
            raise PlanError(f"{key} changed or is mutable")

    target = plan["target"]
    if target != {
        "fact_id": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
        "source_name": "Nat.gcd_fib_add_self",
        "target_definition": "Axeyum.Autogenesis.Coverage.r091",
        "stream_sha256": "fc1117679c743009e8548a25d1f73f71f6cd42555ea77b3efce07844673670b2",
        "exact_target_submissions_reserved": 2,
    }:
        raise PlanError("target reservation changed")

    decision = plan["decision"]
    if (
        decision.get("selected_route")
        != "constructive-official-euclidean-and-balanced-bezout"
        or decision.get("rejected_shortcut")
        != "import-or-graft-official-or-native-same-name-theorems"
    ):
        raise PlanError("bridge decision changed")

    stages = plan["fixed_stages"]
    if (
        [row.get("id") for row in stages]
        != [
            "official-division-equation-root-audit-v1",
            "joint-div-mod-fuel-invariant-v1",
            "constructive-official-div-add-mod-v1",
            "target-balanced-gcd-bezout-v1",
            "target-coprime-factor-cancellation-v1",
        ]
        or stages[0].get("roots")
        != ["Nat.div.go.eq_1", "Nat.modCore.go.eq_1", "Nat.mod.eq_2"]
        or stages[0].get("required_footprint") != []
        or stages[0].get("decline_if_any_root_is_assumption_bearing") is not True
        or [row.get("fresh_reconstructions") for row in stages[1:]] != [2, 2, 2, 2]
        or stages[2].get("required_type_shape") != "Nat.div_add_mod"
        or stages[4].get("required_type_shape")
        != "Axeyum.Autogenesis.NatCoprimeFactorDivisibilityCancellation"
    ):
        raise PlanError("fixed bridge stages changed")

    if plan["budget"] != {
        "max_equation_root_audits": 1,
        "max_new_support_theorem_declarations": 4,
        "fresh_reconstructions_per_declaration": 2,
        "max_new_kernel_theorem_submissions": 8,
        "max_exact_source_target_submissions": 0,
        "max_executor_invocations": 0,
        "max_retries": 0,
    }:
        raise PlanError("bridge budget changed")
    if plan["gates"] != {
        "equation_roots_before_authored_proofs": True,
        "all_new_theorem_footprints_must_be_empty": True,
        "public_equation_type_must_match_official_target": True,
        "cancellation_type_must_match_accepted_native_support": True,
        "direct_dependencies_must_be_enumerated": True,
        "failed_or_partial_private_kernels_must_not_publish": True,
    }:
        raise PlanError("bridge gates changed")
    if plan["authority"] != {
        "proof_bodies_allowed": False,
        "same_name_transport_allowed": False,
        "official_assumption_bearing_proof_import_allowed": False,
        "exact_target_submission_allowed": False,
        "executor_invocation_allowed": False,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("bridge authority changed")
    return plan


def main() -> int:
    try:
        plan = validate()
        budget = plan["budget"]
        print(
            "AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EUCLIDEAN_BRIDGE_PLAN_OK|"
            "stages=5|support_declarations=0/4|"
            f"kernel_submissions=0/{budget['max_new_kernel_theorem_submissions']}|"
            "target_submissions=0/0|executions=0|retries=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-euclidean-bridge-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
