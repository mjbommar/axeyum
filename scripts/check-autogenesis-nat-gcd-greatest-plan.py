#!/usr/bin/env python3
"""Verify the frozen target-native Nat.gcd_greatest construction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-greatest-plan-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-gcd-greatest-0a04214a.json"


class PlanError(RuntimeError):
    """The target, inputs, proof boundary, or budget changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-gcd-greatest-plan-v1"
        or plan.get("state")
        != "preregistered-target-native-gcd-greatest-before-code-or-execution"
    ):
        raise PlanError("plan identity changed")
    predecessor = plan["predecessor"]
    if sha256(ROOT / predecessor["path"]) != predecessor["sha256"]:
        raise PlanError("predecessor admission identity changed")
    fact = load(FACT)
    target = plan["target"]
    if (
        target.get("fact_id") != fact.get("id")
        or target.get("name") != "Nat.gcd_greatest"
        or target.get("statement") != (fact.get("formal") or {}).get("statement")
        or fact.get("epistemic_status") != "open"
        or fact.get("evidence") != []
        or any(key in fact for key in ("proof_route", "axiom_footprint"))
    ):
        raise PlanError("target fact identity or open state changed")
    capsule = plan["input_capsule"]
    capsule_path = pathlib.Path(capsule["path"])
    result_path = ROOT / capsule["result_manifest"]
    result = load(result_path)
    if (
        sha256(capsule_path) != capsule["sha256"]
        or capsule_path.stat().st_size != capsule["bytes"]
        or stat.S_IMODE(capsule_path.stat().st_mode) != 0o444
        or sha256(result_path) != capsule["result_manifest_sha256"]
        or result.get("state")
        != "three-gcd-divisibility-theorems-reconstructed-twice-byte-identical-empty-footprint"
        or any(row.get("axiom_footprint") != [] for row in result.get("supports", []))
    ):
        raise PlanError("input capsule or accepted GCD support changed")
    if plan["required_direct_theorem_dependencies"] != [
        "Axeyum.Autogenesis.dvdAntisymmOfficialV1",
        "Axeyum.Autogenesis.dvdGcdOfficialV1",
        "Axeyum.Autogenesis.gcdDvdLeftOfficialV1",
        "Axeyum.Autogenesis.gcdDvdRightOfficialV1",
    ]:
        raise PlanError("required theorem dependency boundary changed")
    if plan["acceptance"] != {
        "one_driver_build": True,
        "complete_invocations": 2,
        "exact_target_submissions": 2,
        "exports": 2,
        "fresh_imports": 4,
        "outputs_byte_identical": True,
        "receipts_byte_identical": True,
        "all_axiom_footprints": [],
    }:
        raise PlanError("acceptance contract changed")
    if plan["budget"] != {
        "max_driver_builds": 1,
        "max_complete_invocations": 2,
        "max_exact_target_submissions": 2,
        "max_exports": 2,
        "max_imports": 4,
        "max_retries": 0,
        "max_search_invocations": 0,
        "max_evaluations": 0,
        "max_ledger_writes": 0,
    }:
        raise PlanError("budget changed")
    return plan


def main() -> int:
    try:
        plan = validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"AUTOGENESIS_NAT_GCD_GREATEST_PLAN_ERROR|{error}", file=sys.stderr)
        return 1
    budget = plan["budget"]
    print(
        "AUTOGENESIS_NAT_GCD_GREATEST_PLAN_OK|target=Nat.gcd_greatest|"
        f"invocations=0/{budget['max_complete_invocations']}|"
        f"submissions=0/{budget['max_exact_target_submissions']}|"
        "search=0|evaluation=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
