#!/usr/bin/env python3
"""Verify the preregistered Nat Fibonacci/GCD premise sequence."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
POLICY = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-premise-selection-policy-v1.json"


class PremiseSelectionError(RuntimeError):
    """The selection, sequence, budget, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PremiseSelectionError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fact_path(fact_id: str) -> pathlib.Path:
    return ROOT / "artifacts/facts" / f"{fact_id.replace(':', '-')}.json"


def validate_policy(policy: dict[str, Any], reviewed: dict[str, Any], facts: dict[str, dict[str, Any]]) -> None:
    if (
        policy.get("schema_version") != 1
        or policy.get("kind") != "axeyum-autogenesis-nat-fib-gcd-premise-selection-policy"
        or policy.get("state") != "preregistered-no-proof-evaluation-or-ledger-credit"
    ):
        raise PremiseSelectionError("policy envelope changed")
    inputs = policy["inputs"]
    for key in ["reviewed_nursery", "dependency_components", "checked_slice_manifest"]:
        row = inputs[key]
        if sha256(ROOT / row["path"]) != row["sha256"]:
            raise PremiseSelectionError("input identity changed")
    candidates = {row["name"]: row for row in reviewed["reviewed_candidates"]}
    choice = policy["strategic_choice"]
    if (
        choice != {
            "selected": "Nat.fib_gcd",
            "selected_fact_id": "F:ml430-nat-fib-gcd-d1d98407",
            "selected_direct_unlocks": ["F:ml430-int-gcd-fib-73bdafc2", "F:ml430-nat-fib-dvd-f80f3de1"],
            "selected_slice_abstractions": 1,
            "selected_slice_retained": 46,
            "deferred": "Int.fib_neg",
            "deferred_direct_unlocks": ["F:ml430-int-gcd-fib-73bdafc2"],
            "deferred_slice_abstractions": 2,
            "deferred_slice_retained": 93,
        }
        or candidates["Nat.fib_gcd"]["disposition"] != "evaluation-eligible"
        or candidates["Int.fib_neg"]["disposition"] != "evaluation-eligible"
    ):
        raise PremiseSelectionError("strategic choice changed")
    chain = policy["bottom_up_chain"]
    expected_ids = [
        "F:ml430-nat-fib-add-two-b86e0c82",
        "F:ml430-nat-fib-coprime-fib-succ-162fc738",
        "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
        "F:ml430-nat-fib-gcd-d1d98407",
    ]
    if [row["fact_id"] for row in chain] != expected_ids:
        raise PremiseSelectionError("bottom-up sequence changed")
    for row in chain:
        fact = facts[row["fact_id"]]
        if row["status"] != "open" or fact["epistemic_status"] != "open" or row["depends_on"] != fact["depends_on"]:
            raise PremiseSelectionError("fact status or dependency changed")
    target = policy["immediate_target"]
    candidate = candidates["Nat.fib_add_two"]
    if (
        target["fact_id"] != expected_ids[0]
        or target["candidate_id"] != candidate["candidate_id"]
        or target["statement"] != candidate["statement"]
        or target["disposition"] != "evaluation-eligible"
        or target["artifact_file"] != "r080.ndjson"
        or target["type_slice_receipt_sha256"] != "daf20a56a5dc6b70ed218fcdb29be0c057d86427520c96f29fae9712d2e7c0dd"
        or target["slice_abstractions"] != 0
        or target["slice_retained"] != 46
    ):
        raise PremiseSelectionError("immediate target changed")
    if policy["producer"] != {
        "policy_version": "nat-fib-iterate-recurrence-v1",
        "operation": "bounded-iterate-recurrence-v1",
        "allowed_helper_schemas": 1,
        "max_plan_templates": 2,
        "max_kernel_submissions": 2,
        "max_executor_invocations": 1,
        "max_retries": 0,
        "proof_bodies_allowed": False,
        "historical_target_outcomes_are_inputs": False,
    }:
        raise PremiseSelectionError("producer budget changed")
    if policy["authority"] != {
        "partitions_allowed": ["train"],
        "held_out_allowed": False,
        "executor_invocations_so_far": 0,
        "semantic_theorem_receipts_so_far": 0,
        "evaluation_credit_so_far": 0,
        "ledger_writes_so_far": 0,
    }:
        raise PremiseSelectionError("execution authority changed")


def validate() -> dict[str, Any]:
    policy = load(POLICY)
    reviewed = load(ROOT / policy["inputs"]["reviewed_nursery"]["path"])
    fact_ids = [row["fact_id"] for row in policy["bottom_up_chain"]]
    fact_ids += policy["strategic_choice"]["selected_direct_unlocks"]
    facts = {fact_id: load(fact_path(fact_id)) for fact_id in set(fact_ids)}
    validate_policy(policy, reviewed, facts)
    return policy


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_NAT_FIB_GCD_PREMISE_SELECTION_POLICY_OK|strategic=Nat.fib_gcd|foothold=Nat.fib_add_two|chain=4|unlocks=2|plans=2|submissions=0/2|evaluation=0|held_out=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PremiseSelectionError) as error:
        print(f"autogenesis-nat-fib-gcd-premise-selection-policy: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
