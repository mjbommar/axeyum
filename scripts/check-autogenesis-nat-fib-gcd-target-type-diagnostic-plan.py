#!/usr/bin/env python3
"""Validate the bounded Nat.fib_gcd target-type diagnostic plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-target-type-diagnostic-plan-v1.json"


class PlanError(RuntimeError):
    """The diagnostic input, operation, or zero-target-authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    implementation = plan.get("implementation_prestate") or {}
    diagnostic = plan.get("diagnostic") or {}
    implementation_matches_prestate = (
        sha(ROOT / implementation["path"]) == implementation.get("sha256")
    )
    if not implementation_matches_prestate:
        result_path = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-target-type-diagnostic-result-v1.json"
        result = json.loads(result_path.read_text())
        if (
            result.get("state")
            != "target-proof-inference-stopped-at-internal-type-mismatch-no-target-submission"
            or result.get("plan", {}).get("sha256") != sha(PLAN)
            or result.get("implementation", {}).get("sha256")
            != sha(ROOT / implementation["path"])
        ):
            raise PlanError("implementation changed without the exact diagnostic result")
    if (
        plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-target-type-diagnostic-plan-v1"
        or plan.get("state") != "preregistered-target-proof-inference-before-diagnostic-code"
        or sha(ROOT / source["result"]) != source.get("sha256")
        or diagnostic.get("mode") != "--target-native-fib-gcd-target-type-diagnostic"
        or diagnostic.get("theorem_statement_changes") != 0
        or diagnostic.get("proof_route_changes") != 0
        or diagnostic.get("rendered_material")
        != {"expected_theorem_types": 1, "inferred_theorem_types": 1, "proof_values": 0}
        or plan.get("budget")
        != {
            "complete_diagnostics": 1,
            "helper_theorem_submissions": 1,
            "target_proof_inferences": 1,
            "target_theorem_submissions": 0,
            "capsule_writes": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("diagnostic identity, operation, or authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-target-type-diagnostic-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_TARGET_TYPE_DIAGNOSTIC_PLAN_OK|budget=spent|target=0|writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
