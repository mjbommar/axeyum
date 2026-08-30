#!/usr/bin/env python3
"""Validate the retained first Nat.fib_gcd construction decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-result-v1.json"


class ResultError(RuntimeError):
    """The retained rejection or zero-credit boundary changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def historical_sha(commit: str, path: str) -> str:
    value = subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)
    return hashlib.sha256(value).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    observation = result.get("observation") or {}
    execution = result.get("execution") or {}
    authority = result.get("authority") or {}
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-construction-result-v1"
        or result.get("state")
        != "first-helper-submission-type-mismatch-second-run-skipped-zero-target-credit"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or historical_sha("b2341d1f6", implementation["path"])
        != implementation.get("sha256")
        or observation
        != {
            "invocation": 1,
            "stage": "helper trusted-kernel submission",
            "helper": "Axeyum.Autogenesis.fibGcdQuotientIterationV1",
            "error": "Fibonacci quotient iteration rejected: TypeMismatch { expected: ExprId(109659), got: ExprId(109670) }",
            "process_local_expression_ids_are_not_semantic_evidence": True,
            "capsule_output_written": False,
            "target_submitted": False,
            "second_invocation_skipped": True,
        }
        or execution
        != {
            "driver_builds": 1,
            "complete_invocations": 0,
            "capsule_reads": 2,
            "fresh_output_imports": 0,
            "helper_theorem_submissions": 1,
            "target_theorem_submissions": 0,
            "proof_search_invocations": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or any(authority.get(key) != 0 for key in authority)
    ):
        raise ResultError("rejection identity, execution count, or authority changed")
    return result


def main() -> int:
    try:
        result = validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-construction-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_CONSTRUCTION_RESULT_OK|"
        f"stage={result['observation']['stage']}|helper_submissions=1|target_submissions=0|credit=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
