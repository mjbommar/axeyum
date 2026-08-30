#!/usr/bin/env python3
"""Verify the corrected rooted Int.fib_natCast construction plan."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-rooted-construction-plan-v2.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-natcast-direct-v1.lean"
PRIOR = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-construction-result-v1.json"


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        prior = json.loads(PRIOR.read_text())
        if plan["kind"] != "axeyum-autogenesis-int-fib-natcast-rooted-construction-plan" or prior["state"] != plan["prior_result"]["required_state"] or hashlib.sha256(SOURCE.read_bytes()).hexdigest() != plan["source"]["sha256"] or not plan["remote"]["olean_path"].endswith("/.lake/build/lib/lean/AxeyumIntFibNatCastDirectV1.olean") or plan["execution"] != {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_ledger_writes": 0} or plan["success"]["required_axiom_footprint"] != [] or plan["success"]["fact_admission_authorized"] is not False:
            raise RuntimeError("prior result, rooted path, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_NATCAST_ROOTED_CONSTRUCTION_PLAN_OK|compiles=0/1|exports=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-natcast-rooted-construction-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
