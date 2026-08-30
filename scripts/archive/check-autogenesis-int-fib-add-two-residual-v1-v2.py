#!/usr/bin/env python3
"""Verify the first residual failure and exact V2 match repair."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V1_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-residualization-plan-v1.json"
V1_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-residualization-result-v1.json"
V2_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-residualization-plan-v2.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(V1_RESULT.read_text())
        plan = json.loads(V2_PLAN.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        if (
            result["state"] != plan["prior_result"]["required_state"]
            or sha256(V1_PLAN) != result["plan_sha256"]
            or sha256(ROOT / result["source"]["path"]) != result["source"]["sha256"]
            or result["execution"]["compiler_invocations"] != 1
            or result["execution"]["exporter_invocations"] != 0
            or result["cleanup"]["checkout_baseline_restored"] is not True
            or plan["state"] != "preregistered-after-v1-match-reduction-failure-before-v2-source"
            or plan["repair"]["contracts_unchanged"] is not True
            or plan["repair"]["new_automation"] is not False
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or plan["budget"]["max_closed_target_submissions"] != 0
            or plan["budget"]["max_retries"] != 0
            or plan["budget"]["max_ledger_writes"] != 0
        ):
            raise RuntimeError("V1 failure, V2 repair, prestate, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_RESIDUAL_V1_V2_OK|v1=match-boundary|v2=explicit-conditionals|closed_submissions=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-residual-v1-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
