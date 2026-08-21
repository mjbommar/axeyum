#!/usr/bin/env python3
"""Validate the no-submission helper type diagnostic plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-type-diagnostic-plan-v1.json"


class PlanError(RuntimeError):
    """The diagnostic scope or zero-submission boundary changed."""


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    target = plan.get("target") or {}
    budget = plan.get("budget") or {}
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-helper-type-diagnostic-plan-v1"
        or plan.get("state")
        != "preregistered-no-submission-expected-versus-inferred-type-diagnostic"
        or hashlib.sha256((ROOT / source["decline_result"]).read_bytes()).hexdigest()
        != source.get("sha256")
        or target.get("name") != "Axeyum.Autogenesis.fibGcdQuotientIterationV1"
        or "render proof value" not in plan.get("observation", {}).get("forbidden", [])
        or budget
        != {
            "driver_builds": 1,
            "complete_diagnostics": 1,
            "capsule_reads": 2,
            "proof_inferences": 1,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("diagnostic input, target, or authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-type-diagnostic-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_HELPER_TYPE_DIAGNOSTIC_PLAN_OK|diagnostics=0/1|inferences=0/1|submissions=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
