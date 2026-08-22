#!/usr/bin/env python3
"""Verify the preregistered Int.gcd contract-to-theorem bridge policy."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
POLICY = ROOT / "artifacts/autogenesis/mathlib-int-gcd-contract-theorem-control-policy-v1.json"


class ControlPolicyError(RuntimeError):
    """The preregistration changed, weakened, or claims execution credit."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ControlPolicyError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fact_path(fact_id: str) -> pathlib.Path:
    return ROOT / "artifacts/facts" / f"{fact_id.replace(':', '-').replace('/', '-')}.json"


def validate_policy(
    policy: dict[str, Any],
    reviewed: dict[str, Any],
    contract_manifest: dict[str, Any],
    facts: dict[str, dict[str, Any]],
) -> None:
    if (
        policy.get("schema_version") != 1
        or policy.get("kind")
        != "axeyum-autogenesis-int-gcd-contract-theorem-control-policy"
        or policy.get("state") != "preregistered-not-run-no-theorem-or-ledger-credit"
    ):
        raise ControlPolicyError("policy envelope changed")
    inputs = policy.get("inputs")
    immediate = policy.get("immediate_control")
    horizon = policy.get("evaluation_horizon")
    producer = policy.get("producer")
    acceptance = policy.get("acceptance")
    authority = policy.get("authority")
    if not all(isinstance(value, dict) for value in [inputs, immediate, horizon, producer, acceptance, authority]):
        raise ControlPolicyError("policy sections changed")
    reviewed_input = inputs.get("reviewed_nursery")
    contract_input = inputs.get("source_contract_manifest")
    if not isinstance(reviewed_input, dict) or not isinstance(contract_input, dict):
        raise ControlPolicyError("policy inputs changed")
    reviewed_path = ROOT / reviewed_input.get("path", "")
    contract_path = ROOT / contract_input.get("path", "")
    if (
        reviewed_path != ROOT / "artifacts/autogenesis/mathlib-nat-int-reviewed-nursery-v1.json"
        or contract_path
        != ROOT / "artifacts/autogenesis/mathlib-int-gcd-trace-contract-receipt-v1.json"
        or sha256(reviewed_path) != reviewed_input.get("sha256")
        or sha256(contract_path) != contract_input.get("sha256")
        or contract_input.get("observation_sha256")
        != contract_manifest.get("observation_archive", {}).get("observation_sha256")
        or contract_input.get("receipt_sha256")
        != "ae7585751df713ac8fda6f611c3197b0917c9001dc8bda134e9a43416ce3ec82"
        or contract_manifest.get("result", {}).get("source_contract_receipts_issued") != 1
    ):
        raise ControlPolicyError("source authority changed")
    candidates = {
        row.get("name"): row for row in reviewed.get("reviewed_candidates", [])
    }
    control = candidates.get("Int.gcd_def")
    target = candidates.get("Int.gcd_fib")
    if (
        control is None
        or control.get("candidate_id") != immediate.get("candidate_id")
        or control.get("dependency_component_id")
        != immediate.get("dependency_component_id")
        or control.get("statement") != immediate.get("statement")
        or control.get("disposition") != "calibration-only"
        or immediate.get("review_disposition") != "calibration-only"
        or immediate.get("credit_class") != "mechanism-control-only"
    ):
        raise ControlPolicyError("immediate control changed")
    if (
        target is None
        or target.get("candidate_id") != horizon.get("candidate_id")
        or target.get("statement") != horizon.get("statement")
        or target.get("disposition") != "evaluation-eligible"
        or horizon.get("review_disposition") != "evaluation-eligible"
        or horizon.get("fact_id") != "F:ml430-int-gcd-fib-73bdafc2"
    ):
        raise ControlPolicyError("evaluation horizon changed")
    expected_premises = [
        "F:ml430-int-fib-neg-b4021d37",
        "F:ml430-nat-fib-gcd-d1d98407",
    ]
    premise_rows = horizon.get("direct_premises")
    if (
        not isinstance(premise_rows, list)
        or [row.get("fact_id") for row in premise_rows] != expected_premises
        or facts["F:ml430-int-gcd-fib-73bdafc2"].get("depends_on") != expected_premises
    ):
        raise ControlPolicyError("evaluation dependency chain changed")
    target_fact = facts["F:ml430-int-gcd-fib-73bdafc2"]
    if target_fact.get("epistemic_status") == "open":
        if horizon.get("target_file_sha256") != sha256(
            fact_path("F:ml430-int-gcd-fib-73bdafc2")
        ):
            raise ControlPolicyError("open evaluation horizon identity changed")
    elif (
        target_fact.get("epistemic_status") != "proved"
        or target_fact.get("proof_route") != "kernel-lean"
        or target_fact.get("axiom_footprint") != []
    ):
        raise ControlPolicyError("settled evaluation horizon assurance changed")
    for row in premise_rows:
        fact_id = row["fact_id"]
        fact = facts[fact_id]
        if row.get("epistemic_status") != "open":
            raise ControlPolicyError("frozen premise prestate changed")
        if fact.get("epistemic_status") == "open":
            if row.get("file_sha256") != sha256(fact_path(fact_id)):
                raise ControlPolicyError("open premise identity changed")
        elif (
            fact.get("epistemic_status") != "proved"
            or fact.get("proof_route") != "kernel-lean"
            or fact.get("axiom_footprint") != []
            or not fact.get("evidence")
        ):
            raise ControlPolicyError(
                "settled premise lacks axiom-free kernel evidence"
            )
    if producer != {
        "policy_version": "int-gcd-contract-theorem-control-v1",
        "operation": "trace-contract-reflexivity-v1",
        "grammar": "introduce exactly two pointwise arguments, then construct Eq.refl",
        "max_binders": 2,
        "max_constructed_nodes": 5,
        "max_invocations": 1,
        "max_retries": 0,
        "required_source_contract_receipts": 1,
        "required_source_axioms": 0,
    }:
        raise ControlPolicyError("producer budget changed")
    if acceptance != {
        "exact_target": "Int.gcd_def",
        "source_contract_receipt_replayed": True,
        "kernel_accepts_constructed_theorem": True,
        "theorem_axiom_footprint": 0,
        "semantic_theorem_receipts_issued": 1,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ControlPolicyError("acceptance contract changed")
    if authority != {
        "partitions_allowed": ["train"],
        "held_out_allowed": False,
        "proof_bodies_allowed": False,
        "historical_producer_outcomes_are_selection_inputs": False,
        "producer_invocations_so_far": 0,
        "semantic_theorem_receipts_issued_so_far": 0,
        "ledger_writes_so_far": 0,
    }:
        raise ControlPolicyError("execution authority changed")


def validate() -> dict[str, Any]:
    policy = load(POLICY)
    inputs = policy["inputs"]
    reviewed = load(ROOT / inputs["reviewed_nursery"]["path"])
    contract_manifest = load(ROOT / inputs["source_contract_manifest"]["path"])
    fact_ids = [
        "F:ml430-int-fib-neg-b4021d37",
        "F:ml430-nat-fib-gcd-d1d98407",
        "F:ml430-int-gcd-fib-73bdafc2",
    ]
    facts = {fact_id: load(fact_path(fact_id)) for fact_id in fact_ids}
    validate_policy(policy, reviewed, contract_manifest, facts)
    return policy


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_INT_GCD_CONTRACT_THEOREM_CONTROL_POLICY_OK|"
            "control=Int.gcd_def|credit=mechanism-only|binders=2|nodes=5|"
            "invocations=0/1|theorem_receipts=0|evaluation=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ControlPolicyError) as error:
        print(f"autogenesis-int-gcd-contract-theorem-control-policy: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
