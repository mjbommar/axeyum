#!/usr/bin/env python3
"""Verify the frozen official-representation gcd-zero-left source plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-zero-left-reconstruction-plan-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_nat_gcd_fix_eq_v2.lean"
PREDECESSOR = ROOT / "scripts/lean/autogenesis_nat_gcd_fix_eq.lean"
AUDIT_RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-fix-compatibility-audit-result-v1.json"
SOURCE_SHA256 = "a893175b87b5ddcab95a9fdf5abf5436880ba116d308e1f5169f5dd512bb83c1"
PREDECESSOR_SHA256 = "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"
AUDIT_RESULT_SHA256 = "a4a9995a85590e1d493270fcc6232cf434cb24a1b26fb8e3aea067ffa0ed7cc1"
THEOREM_INSERTION = """theorem gcdModel_zero_left (n : Nat) : gcdModel 0 n = n := by
  delta gcdModel gcdUnary WellFounded.Nat.fix
  let x : GcdArgs := ⟨0, n⟩
  have hx : gcdMeasure x < 1 := by
    change 0 < 1
    exact Nat.zero_lt_succ 0
  calc
    _ = WellFounded.Nat.fix.go gcdMeasure gcdStep 1 x hx :=
      gcdGo_congr _ _ _ _ _
    _ = n := by rfl

theorem nat_gcd_zero_left (n : Nat) : Nat.gcd 0 n = n := by
  delta Nat.gcd Nat.gcd._unary
  exact gcdModel_zero_left n

"""
PRINT_INSERTION = """#print axioms Axeyum.Autogenesis.gcdModel_zero_left
#print axioms Axeyum.Autogenesis.nat_gcd_zero_left
"""


class OfficialGcdZeroLeftPlanError(RuntimeError):
    """The predecessor delta, environment, budget, or zero authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdZeroLeftPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-zero-left-reconstruction-plan", "preregistered-official-representation-pointwise-zero-left-before-compilation-no-theorem-credit"):
        raise OfficialGcdZeroLeftPlanError("plan identity changed")
    if sha256(SOURCE) != SOURCE_SHA256 or plan.get("inputs", {}).get("authored_source", {}).get("sha256") != SOURCE_SHA256:
        raise OfficialGcdZeroLeftPlanError("authored source identity changed")
    if sha256(PREDECESSOR) != PREDECESSOR_SHA256 or sha256(AUDIT_RESULT) != AUDIT_RESULT_SHA256:
        raise OfficialGcdZeroLeftPlanError("input identity changed")
    source = SOURCE.read_text()
    if source.count(THEOREM_INSERTION) != 1 or source.count(PRINT_INSERTION) != 1:
        raise OfficialGcdZeroLeftPlanError("exact source insertion changed")
    if source.replace(THEOREM_INSERTION, "").replace(PRINT_INSERTION, "") != PREDECESSOR.read_text():
        raise OfficialGcdZeroLeftPlanError("predecessor changed outside the exact insertion")
    inserted = THEOREM_INSERTION
    if any(token in inserted for token in ("Nat.gcd_zero_left", "WellFounded.Nat.fix_eq", "funext", "propext", "simp", "rw [")):
        raise OfficialGcdZeroLeftPlanError("forbidden token entered the new proof")
    construction = plan.get("construction", {})
    if construction.get("target") != "Axeyum.Autogenesis.nat_gcd_zero_left" or construction.get("new_support_theorem") != "Axeyum.Autogenesis.gcdModel_zero_left":
        raise OfficialGcdZeroLeftPlanError("construction boundary changed")
    budget = {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_closed_balanced_bezout_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdZeroLeftPlanError("budget changed")
    if any(value != 0 for value in plan.get("authority", {}).values()):
        raise OfficialGcdZeroLeftPlanError("pre-execution authority must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_ZERO_LEFT_PLAN_OK|copies=1|compiles=1|exports=1|imports=2|closed_bezout=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdZeroLeftPlanError) as error:
        print(f"autogenesis-official-gcd-zero-left-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
