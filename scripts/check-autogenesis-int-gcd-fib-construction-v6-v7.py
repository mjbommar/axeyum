#!/usr/bin/env python3
"""Validate the V6 compiler decline and rewrite-only V7 retry."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V6_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v6.json"
V6_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v6.json"
V7_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v7.json"
SOURCE = ROOT / "artifacts/autogenesis/sources/int-fib-natabs-residual-v2.lean"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(V6_RESULT.read_text())
    retry = json.loads(V7_PLAN.read_text())
    if (
        result.get("state")
        != "compiler-declined-before-export-at-second-natabs-occurrences"
        or result["plan"].get("sha256") != sha256(V6_PLAN)
        or result["source"].get("sha256") != sha256(SOURCE)
        or result["execution"]
        != {
            "compiler_invocations": 1,
            "compiler_accepted": False,
            "exporter_invocations": 0,
            "proof_bearing_stream_reads": 0,
            "specialization_submissions": 0,
            "int_gcd_fib_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or result["diagnosis"].get("forbidden_constant_failure_observed") is not False
        or not all(result["cleanup"].values())
        or retry.get("state")
        != "preregistered-before-explicit-second-natabs-rewrite"
        or retry["parent_result"].get("sha256") != sha256(V6_RESULT)
        or retry["source"].get("before_sha256") != sha256(SOURCE)
        or retry["unchanged"].get("explicit_parameter_count") != 8
        or retry["execution"].get("max_lean_compiler_invocations") != 1
        or retry["execution"].get("max_exporter_invocations") != 2
        or retry["execution"].get("max_importer_runs") != 2
        or retry["execution"].get("max_retries") != 0
        or retry["execution"].get("specialization_submissions") != 0
        or retry["execution"].get("ledger_writes") != 0
        or retry["acceptance"].get("axiom_footprint") != []
    ):
        raise ValueError("V6 decline or V7 correction boundary changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v6-v7: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-v6-v7: PASS: "
        "compile=declined|exports=0|only_change=second-natAbs-rewrites|"
        "specializations=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
