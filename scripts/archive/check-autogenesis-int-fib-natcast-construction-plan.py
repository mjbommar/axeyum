#!/usr/bin/env python3
"""Verify the direct Int.fib_natCast construction preregistration."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-construction-plan-v1.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-natcast-direct-v1.lean"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-natcast-d5886be4.json"
QUALIFICATION = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-root-export-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        fact = json.loads(FACT.read_text())
        if plan["kind"] != "axeyum-autogenesis-int-fib-natcast-construction-plan" or plan["target_fact"] != fact["id"] or fact["epistemic_status"] != "open" or plan["target_statement"] != fact["formal"]["statement"] or sha256(SOURCE) != plan["source"]["sha256"] or sha256(QUALIFICATION) != plan["inputs"]["qualification_result"]["sha256"] or plan["execution"] != {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_exact_negative_fibonacci_submissions": 0, "max_ledger_writes": 0} or plan["success"]["required_axiom_footprint"] != [] or plan["success"]["fact_admission_authorized"] is not False:
            raise RuntimeError("target, source, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_NATCAST_CONSTRUCTION_PLAN_OK|submissions=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-construction-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
