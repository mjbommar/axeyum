#!/usr/bin/env python3
"""Verify the retained V3 integer Fibonacci recurrence boundary."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v3.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v3.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        execution = result["execution"]
        if (
            result["state"] != "v3-closes-parity-and-leaves-two-abelian-group-identities"
            or sha256(PLAN) != result["plan_sha256"]
            or sha256(ROOT / result["source"]["path"]) != result["source"]["sha256"]
            or execution["compiler_invocations"] != 1
            or execution["compiler_exit_status"] != 1
            or any(execution[key] != 0 for key in ("exporter_invocations", "importer_runs", "target_theorem_submissions", "retries", "search_invocations", "ledger_writes"))
            or result["diagnostic"]["parity_branches_closed"] is not True
            or result["diagnostic"]["remaining_goals"] != 2
            or result["cleanup"]["checkout_baseline_restored"] is not True
            or result["authority"]["fact_admission_authorized"] is not False
        ):
            raise RuntimeError("plan, source, failure boundary, cleanup, or authority changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_RESULT_V3_OK|parity=closed|remaining=abelian-2|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-result-v3: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
