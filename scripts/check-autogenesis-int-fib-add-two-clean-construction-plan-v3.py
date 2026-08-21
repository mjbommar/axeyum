#!/usr/bin/env python3
"""Verify the frozen V3 explicit-parity integer Fibonacci plan."""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v3.json"
PRIOR = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v2.json"


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        prior = json.loads(PRIOR.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        if (
            prior["state"] != plan["prior_result"]["required_state"]
            or plan["state"] != "preregistered-after-v2-parity-branch-failure-before-v3-source"
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or len(plan["repair"]["facts"]) != 3
            or plan["repair"]["new_automation"] is not False
            or plan["repair"]["representation_unchanged"] is not True
            or plan["budget"]["max_compiler_invocations"] != 1
            or plan["budget"]["max_retries"] != 0
            or plan["budget"]["max_ledger_writes"] != 0
        ):
            raise RuntimeError("prior failure, repair scope, prestate, or budget changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_PLAN_V3_OK|parity_facts=3|compile=0/1|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-plan-v3: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
