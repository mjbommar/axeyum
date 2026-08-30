#!/usr/bin/env python3
"""Verify the retained first Int.fib_add_two construction failure."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-two-clean-construction-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        source = ROOT / result["source"]["path"]
        execution = result["execution"]
        if (
            result["state"] != "first-source-stops-at-negative-successor-normalization-no-export"
            or sha256(PLAN) != result["plan_sha256"]
            or sha256(source) != result["source"]["sha256"]
            or execution != {
                "compiler_invocations": 1,
                "compiler_exit_status": 1,
                "exporter_invocations": 0,
                "importer_runs": 0,
                "target_theorem_submissions": 0,
                "retries": 0,
                "search_invocations": 0,
                "ledger_writes": 0,
            }
            or len(result["diagnostic"]["completed_cases"]) != 3
            or len(result["diagnostic"]["open_cases"]) != 2
            or result["cleanup"]["checkout_baseline_restored"] is not True
            or result["conclusion"]["construction_succeeded"] is not False
            or result["conclusion"]["fact_admission_authorized"] is not False
        ):
            raise RuntimeError("plan, source, failure, cleanup, or authority changed")
        print("AUTOGENESIS_INT_FIB_ADD_TWO_CLEAN_CONSTRUCTION_RESULT_OK|compile=1|open_cases=2|submissions=0|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-add-two-clean-construction-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
