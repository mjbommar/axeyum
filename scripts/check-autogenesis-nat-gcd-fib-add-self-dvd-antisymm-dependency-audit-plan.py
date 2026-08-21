#!/usr/bin/env python3
"""Fail closed over the gcd-shift divisibility-antisymmetry audit plan."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = pathlib.Path(os.environ.get("AXEYUM_DVD_ANTISYMM_AUDIT_PLAN", ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-plan-v1.json"))
ROOTS = ["Eq.symm", "Nat.eq_zero_of_zero_dvd", "Nat.le_antisymm", "Nat.le_of_dvd", "Nat.succ_pos"]
BUDGET = {"max_binary_builds": 1, "max_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_retries": 0}


class DvdAntisymmDependencyAuditPlanError(RuntimeError):
    """The audit population, evidence, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise DvdAntisymmDependencyAuditPlanError("plan is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-plan", "preregistered-five-root-nonrendering-audit-before-stream-reread"):
        raise DvdAntisymmDependencyAuditPlanError("plan identity changed")
    for predecessor in plan["predecessors"].values():
        if hashlib.sha256((ROOT / predecessor["path"]).read_bytes()).hexdigest() != predecessor["sha256"]:
            raise DvdAntisymmDependencyAuditPlanError("predecessor identity changed")
    input_row = plan["input"]
    if hashlib.sha256(pathlib.Path(input_row["path"]).read_bytes()).hexdigest() != input_row["sha256"] or input_row["textual_read_allowed"] is not False:
        raise DvdAntisymmDependencyAuditPlanError("sealed input identity or policy changed")
    tool = plan["tool"]
    if hashlib.sha256((ROOT / tool["path"]).read_bytes()).hexdigest() != tool["sha256"] or tool["proof_terms_types_or_values_may_be_rendered"] is not False:
        raise DvdAntisymmDependencyAuditPlanError("audit tool identity or rendering policy changed")
    if plan.get("ordered_roots") != ROOTS or len(set(plan["ordered_roots"])) != 5:
        raise DvdAntisymmDependencyAuditPlanError("ordered root population changed")
    if plan.get("budget") != BUDGET:
        raise DvdAntisymmDependencyAuditPlanError("budget changed")
    if any(value != 0 for value in plan["authority"].values()):
        raise DvdAntisymmDependencyAuditPlanError("plan grants authority before audit")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_GCD_SHIFT_DVD_ANTISYMM_AUDIT_PLAN_OK|roots=5|reads=1|submissions=0|authority=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, DvdAntisymmDependencyAuditPlanError) as error:
        print(f"autogenesis-gcd-shift-dvd-antisymm-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
