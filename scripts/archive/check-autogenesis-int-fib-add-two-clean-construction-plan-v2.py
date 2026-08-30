#!/usr/bin/env python3
"""Verify the frozen V2 integer Fibonacci recurrence repair."""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v2.json"
PRIOR = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v1.json"


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        prior = json.loads(PRIOR.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        if (
            prior["state"] != plan["prior_result"]["required_state"]
            or plan["state"] != "preregistered-after-v1-normalization-failure-before-v2-source"
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or plan["repair"]["proof_route_unchanged"] is not True
            or plan["repair"]["new_automation"] is not False
            or plan["budget"]["max_compiler_invocations"] != 1
            or plan["budget"]["max_retries"] != 0
            or plan["budget"]["max_ledger_writes"] != 0
        ):
            raise RuntimeError("prior failure, repair scope, prestate, or budget changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_PLAN_V2_OK|compile=0/1|repair=normalization-only|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-plan-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
