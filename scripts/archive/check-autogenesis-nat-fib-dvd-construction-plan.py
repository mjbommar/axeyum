#!/usr/bin/env python3
"""Validate the preregistered exact Nat.fib_dvd construction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-dvd-construction-plan-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-fib-dvd-f80f3de1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    fact = json.loads(FACT.read_text())
    target = plan["target"]
    source = plan["input"]
    acceptance = plan["acceptance"]
    budget = plan["budget"]
    capsule = pathlib.Path(source["capsule_path"])
    if (
        plan.get("state")
        != "preregistered-exact-target-construction-before-code-or-capsule-read"
        or fact.get("epistemic_status") != "open"
        or fact.get("depends_on") != ["F:ml430-nat-fib-gcd-d1d98407"]
        or target.get("fact_id") != fact.get("id")
        or target.get("fact_sha256") != sha(FACT)
        or target.get("name") != "Nat.fib_dvd"
        or target.get("formal_statement_sha256")
        != hashlib.sha256(fact["formal"]["statement"].encode()).hexdigest()
        or sha(capsule) != source.get("capsule_sha256")
        or source.get("required_roots")
        != [
            "Nat.fib_gcd",
            "Axeyum.Autogenesis.dvdReflOfficialV1",
            "Axeyum.Autogenesis.dvdAntisymmOfficialV1",
            "Axeyum.Autogenesis.dvdGcdOfficialV1",
            "Axeyum.Autogenesis.gcdDvdLeftOfficialV1",
            "Axeyum.Autogenesis.gcdDvdRightOfficialV1",
        ]
        or acceptance
        != {
            "complete_invocations": 2,
            "target_theorem_submissions": 2,
            "exports": 2,
            "fresh_imports": 4,
            "outputs_byte_identical": True,
            "observations_byte_identical": True,
            "axiom_footprint": [],
        }
        or budget.get("max_target_theorem_submissions") != 2
        or budget.get("max_retries") != 0
        or budget.get("max_search_invocations") != 0
        or budget.get("max_ledger_writes") != 0
    ):
        raise RuntimeError("Nat.fib_dvd construction authority changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-dvd-construction-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_DVD_CONSTRUCTION_PLAN_OK|runs=0/2|target=0/2|imports=0/4|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
