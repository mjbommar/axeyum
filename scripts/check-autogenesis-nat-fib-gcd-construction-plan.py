#!/usr/bin/env python3
"""Validate the exact bounded Nat.fib_gcd construction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-plan-v1.json"


class PlanError(RuntimeError):
    """The construction route, inputs, or submission ceiling changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    target = plan.get("target") or {}
    contract = plan.get("contract_result") or {}
    inputs = plan.get("inputs")
    submissions = plan.get("submissions")
    budget = plan.get("budget") or {}
    acceptance = plan.get("acceptance") or {}
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-construction-plan-v1"
        or plan.get("state")
        != "preregistered-two-submission-per-run-exact-construction-before-code"
        or target.get("fact_id") != "F:ml430-nat-fib-gcd-d1d98407"
        or target.get("name") != "Nat.fib_gcd"
        or target.get("statement")
        != "∀ (m n : ℕ), Nat.fib (m.gcd n) = (Nat.fib m).gcd (Nat.fib n)"
        or sha(ROOT / "artifacts/facts/F-ml430-nat-fib-gcd-d1d98407.json")
        != target.get("fact_file_sha256")
        or sha(ROOT / contract["path"]) != contract.get("sha256")
    ):
        raise PlanError("target or checked helper-contract identity changed")
    if (
        not isinstance(inputs, list)
        or [row.get("root") for row in inputs]
        != ["Nat.gcd_greatest", "Nat.gcd_fib_add_self"]
        or any(sha(pathlib.Path(row["capsule"])) != row.get("sha256") for row in inputs)
        or not isinstance(submissions, list)
        or [(row.get("order"), row.get("name")) for row in submissions]
        != [
            (1, "Axeyum.Autogenesis.fibGcdQuotientIterationV1"),
            (2, "Nat.fib_gcd"),
        ]
    ):
        raise PlanError("input roots or exact submission order changed")
    if (
        len(plan.get("required_named_dependencies") or []) != 16
        or budget
        != {
            "driver_builds": 1,
            "complete_invocations": 2,
            "capsule_reads": 4,
            "fresh_output_imports": 4,
            "helper_theorem_submissions": 2,
            "target_theorem_submissions": 2,
            "proof_search_invocations": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or acceptance
        != {
            "both_invocations_accept_both_exact_statements": True,
            "all_theorem_axiom_footprints": [],
            "outputs_byte_identical": True,
            "receipts_byte_identical": True,
            "target_fact_status_changes": 0,
        }
    ):
        raise PlanError("dependency set, submission ceiling, or acceptance changed")
    return plan


def main() -> int:
    try:
        plan = validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-construction-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_CONSTRUCTION_PLAN_OK|"
        f"submissions={len(plan['submissions'])}|runs=0/2|helper=0/2|target=0/2|retries=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
