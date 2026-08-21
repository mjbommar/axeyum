#!/usr/bin/env python3
"""Verify the V5 dependency partition and residualization boundary."""

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-v5-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-residualization-plan-v1.json"


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        plan = json.loads(PLAN.read_text())
        partition = (
            result["empty_footprint"]
            + result["propext_bearing"]
            + list(result["other_assumption_bearing"])
        )
        fact = json.loads(
            (ROOT / "artifacts/facts/F-ml430-nat-fib-add-two-b86e0c82.json").read_text()
        )
        if (
            result["state"] != plan["parent_result"]["required_state"]
            or result["summary"] != {
                "population": 23,
                "empty_footprint": 9,
                "propext_bearing": 13,
                "other_assumption_bearing": 1,
            }
            or len(partition) != 23
            or len(set(partition)) != 23
            or result["execution"]["proof_bearing_stream_reads"] != 1
            or result["execution"]["ledger_writes"] != 0
            or plan["state"] != "preregistered-after-exact-dependency-partition-before-residual-source-or-code"
            or len(plan["residual_contracts"]) != 7
            or fact["epistemic_status"] != "proved"
            or fact.get("axiom_footprint") != []
            or plan["implementation"]["source_or_code_present_at_plan_commit"] is not False
            or plan["budget"]["max_closed_target_submissions"] != 0
            or plan["authority"]["closed_target_authorized"] is not False
            or plan["authority"]["ledger_writes"] != 0
        ):
            raise RuntimeError("partition, reuse premise, residual scope, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_DEPENDENCY_RESIDUAL_PLAN_OK|clean=9|carriers=14|contracts=7|closed_submissions=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-dependency-residual-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
