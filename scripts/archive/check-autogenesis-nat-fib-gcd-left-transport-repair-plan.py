#!/usr/bin/env python3
"""Validate the explicit Nat.fib_gcd left-transport repair plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-left-transport-repair-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-left-transport-repair-result-v1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan["input"]
    implementation = plan["implementation_prestate"]
    repair = plan["repair"]
    if sha(ROOT / implementation["path"]) != implementation["sha256"]:
        result = json.loads(RESULT.read_text())
        if result.get("plan", {}).get("sha256") != sha(PLAN):
            raise RuntimeError("implementation changed without the exact repair result")
    if (
        plan.get("state") != "preregistered-explicit-gcd-left-transport-before-code"
        or sha(ROOT / source["bridge_result"]) != source["sha256"]
        or repair.get("selected_theorem")
        != "Axeyum.Autogenesis.officialNatGcdSuccClosedV1"
        or repair.get("other_equality_chain_changes") != 0
        or repair.get("theorem_statement_changes") != 0
        or repair.get("proof_route_changes") != 0
        or plan.get("verification")
        != {
            "mode": "--target-native-fib-gcd-target-type-diagnostic",
            "complete_diagnostics": 1,
            "helper_theorem_submissions": 1,
            "target_proof_inferences": 1,
            "required_definitionally_equal": True,
            "target_theorem_submissions": 0,
            "capsule_writes": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("repair identity, scope, or diagnostic authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-left-transport-repair-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_LEFT_TRANSPORT_REPAIR_PLAN_OK|repairs=0/1|diagnostics=0/1|target=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
