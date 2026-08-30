#!/usr/bin/env python3
"""Validate the bounded Exists.rec prefix diagnostic plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-exists-rec-prefix-diagnostic-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-exists-rec-prefix-diagnostic-result-v1.json"


class PlanError(RuntimeError):
    """The prefix order, budget, or zero-target-authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    implementation = plan.get("implementation_prestate") or {}
    diagnostic = plan.get("diagnostic") or {}
    if sha(ROOT / implementation["path"]) != implementation.get("sha256"):
        result = json.loads(RESULT.read_text())
        if (
            result.get("plan", {}).get("sha256") != sha(PLAN)
            or result.get("implementation", {}).get("sha256")
            != sha(ROOT / implementation["path"])
        ):
            raise PlanError("implementation changed without the exact prefix result")
    if (
        plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-exists-rec-prefix-diagnostic-plan-v1"
        or plan.get("state") != "preregistered-exists-rec-prefix-inference-before-code"
        or sha(ROOT / source["result"]) != source.get("sha256")
        or diagnostic.get("mode")
        != "--target-native-fib-gcd-exists-rec-prefix-diagnostic"
        or diagnostic.get("ordered_arguments")
        != ["Nat", "predicate", "motive", "minor", "witness"]
        or diagnostic.get("proof_values_rendered") != 0
        or diagnostic.get("theorem_statement_changes") != 0
        or diagnostic.get("proof_route_changes") != 0
        or plan.get("budget")
        != {
            "complete_diagnostics": 1,
            "helper_theorem_submissions": 1,
            "prefix_inferences": 5,
            "target_theorem_submissions": 0,
            "capsule_writes": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("prefix diagnostic identity, order, or authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-exists-rec-prefix-diagnostic-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_EXISTS_REC_PREFIX_DIAGNOSTIC_PLAN_OK|prefixes=0/5|target=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
