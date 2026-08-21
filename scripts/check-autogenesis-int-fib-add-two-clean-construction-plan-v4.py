#!/usr/bin/env python3
"""Verify the frozen V4 abelian-normalization recurrence plan."""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v4.json"
PRIOR = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v3.json"


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        prior = json.loads(PRIOR.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        if (
            prior["state"] != plan["prior_result"]["required_state"]
            or plan["state"] != "preregistered-after-v3-abelian-boundary-before-v4-source"
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or plan["repair"]["tactic"] != "abel"
            or plan["repair"]["classification"] != "normalization-not-search"
            or plan["repair"]["representation_unchanged"] is not True
            or plan["budget"]["max_compiler_invocations"] != 1
            or plan["budget"]["max_retries"] != 0
            or plan["budget"]["max_ledger_writes"] != 0
        ):
            raise RuntimeError("prior boundary, repair scope, prestate, or budget changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_PLAN_V4_OK|normalizer=abel|compile=0/1|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-plan-v4: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
