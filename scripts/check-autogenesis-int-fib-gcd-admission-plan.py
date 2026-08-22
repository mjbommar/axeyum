#!/usr/bin/env python3
"""Validate the preregistered exact Int.fib_gcd admission."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-admission-plan-v1.json"


class PlanError(RuntimeError):
    """The exact admission authority changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    target = plan["target"]
    evidence = plan["evidence"]
    operation = plan["operation"]
    protocol = plan["protocol"]
    budget = plan["budget"]
    fact_path = ROOT / "artifacts/facts/F-ml430-int-fib-gcd-3a8bfdec.json"
    fact = json.loads(fact_path.read_text())
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-gcd-admission-plan-v1"
        or plan.get("state")
        != "preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write"
        or target.get("fact_id") != "F:ml430-int-fib-gcd-3a8bfdec"
        or target.get("name") != "Int.fib_gcd"
        or sha256(fact_path) != target.get("fact_sha256")
        or fact.get("epistemic_status") != "open"
        or sha256(ROOT / evidence["construction_result"])
        != evidence.get("construction_result_sha256")
        or sha256(ROOT / evidence["identity_result"])
        != evidence.get("identity_result_sha256")
        or evidence.get("receipt_sha256")
        != "6c5a72c0853beb1136f4934b92ce189427b05e58e2f4af020509b718e8b602cc"
        or evidence.get("goal_sha256")
        != "c073add7c75a14558f57793924f2bfaac48ff452c9382bfd77727386ba7a464d"
        or evidence.get("declaration_sha256")
        != "d269d9ef0763dd923c7825c77c0a3a3dd05ebbe4fbad4d84f3ce93482386a0bf"
        or evidence.get("axiom_footprint") != []
        or evidence.get("direct_theorem_dependencies")
        != ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]
        or operation
        != {
            "id": "authoritative-mathlib-int-fib-gcd-kernel-capsule-v1",
            "required_checker": "scripts/check-autogenesis-int-fib-gcd-capsule.py",
            "registry_writes": 1,
        }
        or protocol.get("fault_injection_after_intent_exit") != 75
        or protocol.get("require_fact_unchanged_before_recovery") is not True
        or protocol.get("authoritative_ledger_writes") != 1
        or protocol.get("fixture_writes") != 0
        or protocol.get("isolated_clean_replay") is not True
        or budget.get("max_operation_registrations") != 1
        or budget.get("max_authoritative_ledger_writes") != 1
        or budget.get("max_clean_replays") != 1
        or plan.get("expected_newly_ready") != []
    ):
        raise PlanError("admission identity, evidence, protocol, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-gcd-admission-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-gcd-admission-plan: PASS: "
        "operation=1|fault=1|recovery=1|ledger_writes=1|replays=1"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
