#!/usr/bin/env python3
"""Validate the type-only Nat.fib_gcd helper-contract audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-contract-plan-v1.json"


class PlanError(RuntimeError):
    """The type-only contract scope changed."""


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    result_path = ROOT / source.get("surface_result", "")
    budget = plan.get("budget") or {}
    observation = plan.get("observation") or {}
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-helper-contract-plan-v1"
        or plan.get("state")
        != "preregistered-type-only-contract-audit-before-code-or-stream-read"
        or hashlib.sha256(result_path.read_bytes()).hexdigest()
        != source.get("surface_result_sha256")
        or plan.get("contracts")
        != [
            "Nat.gcd.induction",
            "Axeyum.Autogenesis.modQuotientWitnessV4",
            "Nat.gcd_greatest",
            "Nat.gcd_fib_add_self",
        ]
        or observation.get("allowed", [None])[0] != "rendered theorem type only"
        or "theorem value or proof-body rendering" not in observation.get(
            "forbidden", []
        )
        or budget
        != {
            "driver_builds": 1,
            "complete_audits": 1,
            "capsule_reads": 2,
            "fresh_imports": 2,
            "rendered_theorem_types": 4,
            "rendered_theorem_values": 0,
            "theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("input, contract set, or zero-authority budget changed")
    return plan


def main() -> int:
    try:
        plan = validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-contract-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_HELPER_CONTRACT_PLAN_OK|"
        f"contracts={len(plan['contracts'])}|audits=0/1|types=0/4|values=0|submissions=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
