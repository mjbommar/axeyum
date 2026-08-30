#!/usr/bin/env python3
"""Verify the V4 failure and narrow V5 import repair."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V4_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v4.json"
V4_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v4.json"
V5_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v5.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(V4_RESULT.read_text())
        plan = json.loads(V5_PLAN.read_text())
        source = ROOT / plan["execution"]["source"]
        pack = pathlib.Path(plan["execution"]["pack"])
        if (
            result["state"] != plan["prior_result"]["required_state"]
            or sha256(V4_PLAN) != result["plan_sha256"]
            or sha256(ROOT / result["source"]["path"]) != result["source"]["sha256"]
            or result["execution"]["compiler_invocations"] != 1
            or result["execution"]["exporter_invocations"] != 0
            or result["cleanup"]["checkout_baseline_restored"] is not True
            or plan["state"] != "preregistered-after-v4-missing-tactic-before-v5-source"
            or plan["repair"]["only_source_change"] != "import Mathlib.Tactic.Abel"
            or plan["repair"]["proof_body_unchanged"] is not True
            or source.exists() != plan["execution"]["source_present_at_plan_commit"]
            or pack.exists() != plan["execution"]["pack_present_at_plan_commit"]
            or plan["budget"]["max_retries"] != 0
            or plan["budget"]["max_ledger_writes"] != 0
        ):
            raise RuntimeError("V4 failure, V5 repair, prestate, or budget changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_V4_V5_OK|v4=missing-tactic|v5=narrow-import|compile=0/1|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-v4-v5: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
