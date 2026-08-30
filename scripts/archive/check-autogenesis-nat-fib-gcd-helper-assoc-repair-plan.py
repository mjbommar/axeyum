#!/usr/bin/env python3
"""Validate the single-intermediate Fibonacci helper repair plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-assoc-repair-plan-v1.json"


class PlanError(RuntimeError):
    """The one-edit repair scope changed."""


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    source = plan.get("input") or {}
    repair = plan.get("repair") or {}
    verification = plan.get("verification") or {}
    if (
        plan.get("state") != "preregistered-one-intermediate-correction-before-code"
        or hashlib.sha256((ROOT / source["diagnostic_result"]).read_bytes()).hexdigest()
        != source.get("sha256")
        or repair
        != {
            "function": "declare_fib_gcd_quotient_iteration",
            "operation": "final reversed Nat.add_assoc transport",
            "replace_middle": "m*q + (m + r)",
            "with_middle": "m*q + (r + m)",
            "permitted_source_edits": 1,
            "theorem_statement_changes": 0,
            "route_changes": 0,
        }
        or verification
        != {
            "mode": "existing no-submission helper type diagnostic",
            "complete_diagnostics": 1,
            "required_definitionally_equal": True,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
        }
    ):
        raise PlanError("source identity, exact edit, or no-submission verification changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-assoc-repair-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_HELPER_ASSOC_REPAIR_PLAN_OK|edits=0/1|diagnostics=0/1|submissions=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
