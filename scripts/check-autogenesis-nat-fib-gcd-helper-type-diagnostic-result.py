#!/usr/bin/env python3
"""Validate the retained helper inference decline and one localized seam."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-type-diagnostic-result-v1.json"


class ResultError(RuntimeError):
    """The failed diagnostic, localization, or zero authority changed."""


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
    seam = result.get("localized_structural_seam") or {}
    if (
        result.get("state")
        != "proof-inference-stopped-at-internal-type-mismatch-no-submission"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or historical_sha("754193742", implementation["path"])
        != implementation.get("sha256")
        or observation.get("helper_submitted") is not False
        or observation.get("target_submitted") is not False
        or observation.get("proof_value_rendered") is not False
        or seam.get("incorrect_middle") != "m*q + (m + r)"
        or seam.get("required_middle") != "m*q + (r + m)"
        or result.get("execution")
        != {
            "complete_diagnostics": 0,
            "proof_inferences": 1,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise ResultError("diagnostic identity, seam, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-type-diagnostic-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_HELPER_TYPE_DIAGNOSTIC_RESULT_OK|inferences=1|submissions=0|seam=add-assoc-middle")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
