#!/usr/bin/env python3
"""Verify the target-owned clean Int.fib construction plan."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-clean-definition-construction-plan-v1.json"
PARENT = ROOT / "artifacts/autogenesis/mathlib-int-fib-definition-blocker-partition-result-v2.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-clean-definition-v1.lean"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        if plan["kind"] != "axeyum-autogenesis-int-fib-clean-definition-construction-plan" or sha256(PARENT) != plan["parent_result"]["sha256"] or sha256(SOURCE) != plan["source"]["sha256"] or plan["definitions"]["target"] != "Int.fib" or plan["theorem"]["target"] != "Int.fib_natCast" or "Int.instDecidablePredEven" not in plan["definitions"]["strategy"] or plan["execution"] != {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_ledger_writes": 0} or plan["success"]["required_axiom_footprint"] != [] or plan["success"]["fact_admission_authorized"] is not False:
            raise RuntimeError("parent, source, definition strategy, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_CLEAN_DEFINITION_CONSTRUCTION_PLAN_OK|definitions=0/1|theorems=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-clean-definition-construction-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
