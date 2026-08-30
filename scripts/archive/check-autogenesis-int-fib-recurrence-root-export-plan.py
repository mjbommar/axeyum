#!/usr/bin/env python3
"""Verify the fresh two-root integer Fibonacci export plan."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-root-export-plan-v1.json"
FAILURE = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-support-audit-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    try:
        plan = json.loads(PLAN.read_text())
        environment = plan["fixed_environment"]
        if plan["kind"] != "axeyum-autogenesis-int-fib-recurrence-root-export-plan" or plan["fixed_roots"] != ["Int.fib_natCast", "Int.fib_add_two"] or sha256(FAILURE) != plan["inputs"]["failure_result"]["sha256"] or environment["mathlib_commit"] != "c5ea00351c28e24afc9f0f84379aa41082b1188f" or len(environment["mathlib_untracked_baseline"]) != 3 or plan["budget"] != {"max_exporter_invocations": 1, "max_batch_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_reconstruction_source_compilations": 0, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_executor_invocations": 0} or plan["authority"]["reconstruction_allowed"] is not False or plan["authority"]["ledger_writes"] != 0:
            raise RuntimeError("root, environment, budget, or authority changed")
        print("AUTOGENESIS_INT_FIB_RECURRENCE_ROOT_EXPORT_PLAN_OK|roots=2|exports=0/1|audits=0/1|ledger_writes=0")
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError, RuntimeError) as error:
        print(f"autogenesis-int-fib-recurrence-root-export-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
