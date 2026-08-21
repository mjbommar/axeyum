#!/usr/bin/env python3
"""Validate the proof-free GCD recursion bridge audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-gcd-recursion-bridge-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-gcd-recursion-bridge-result-v1.json"


class PlanError(RuntimeError):
    """The candidate order, contract, or zero-submission authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    implementation = plan.get("implementation_prestate") or {}
    audit = plan.get("audit") or {}
    if sha(ROOT / implementation["path"]) != implementation.get("sha256"):
        result = json.loads(RESULT.read_text())
        if (
            result.get("plan", {}).get("sha256") != sha(PLAN)
            or result.get("implementation", {}).get("sha256")
            != sha(ROOT / implementation["path"])
        ):
            raise PlanError("implementation changed without the exact bridge result")
    if (
        plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-gcd-recursion-bridge-plan-v1"
        or plan.get("state") != "preregistered-proof-free-bridge-audit-before-code"
        or sha(ROOT / source["result"]) != source.get("sha256")
        or audit.get("mode") != "--target-native-fib-gcd-gcd-recursion-bridge-audit"
        or audit.get("ordered_candidates")
        != [
            "Axeyum.Autogenesis.officialNatGcdSuccClosedV1",
            "Axeyum.Autogenesis.nat_gcd_succ",
        ]
        or audit.get("required_axiom_footprint") != []
        or audit.get("proof_values_rendered") != 0
        or plan.get("budget")
        != {
            "complete_audits": 1,
            "kernel_submissions": 0,
            "capsule_writes": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("bridge audit identity, candidates, or authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-gcd-recursion-bridge-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_GCD_RECURSION_BRIDGE_PLAN_OK|audits=0/1|candidates=2|submissions=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
