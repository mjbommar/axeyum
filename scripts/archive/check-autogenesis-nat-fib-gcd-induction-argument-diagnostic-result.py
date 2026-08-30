#!/usr/bin/env python3
"""Validate the retained base-pass, step-fail Nat.fib_gcd diagnostic."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-induction-argument-diagnostic-result-v1.json"


class ResultError(RuntimeError):
    """The induction diagnostic evidence or zero authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def implementation_exists(path: str, expected: str) -> bool:
    current = ROOT / path
    if current.exists() and sha(current) == expected:
        return True
    rows = subprocess.check_output(
        ["git", "rev-list", "--objects", "--all", "--", path], cwd=ROOT, text=True
    )
    for row in rows.splitlines():
        object_id = row.split(" ", 1)[0]
        if (
            subprocess.check_output(
                ["git", "cat-file", "-t", object_id], cwd=ROOT, text=True
            ).strip()
            != "blob"
        ):
            continue
        value = subprocess.check_output(["git", "cat-file", "blob", object_id], cwd=ROOT)
        if hashlib.sha256(value).hexdigest() == expected:
            return True
    return False


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    pack = result.get("evidence_pack") or {}
    observation = result.get("observation") or {}
    pack_path = pathlib.Path(pack["path"])
    if (
        result.get("state") != "base-infers-step-internal-type-mismatch-no-target-submission"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or not implementation_exists(implementation["path"], implementation["sha256"])
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation.json") != pack.get("observation_sha256")
        or sha(pack_path / "stderr.txt") != pack.get("stderr_sha256")
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack_path.iterdir())
        or (pack_path / "observation.json").stat().st_size != 0
        or observation.get("error", "") not in (pack_path / "stderr.txt").read_text()
        or observation.get("base_proof_inference_succeeded") is not True
        or observation.get("step_proof_inference_succeeded") is not False
        or observation.get("target_submitted") is not False
        or result.get("execution")
        != {
            "complete_diagnostics": 0,
            "helper_theorem_submissions": 1,
            "base_proof_inferences": 1,
            "step_proof_inferences": 1,
            "target_proof_inferences": 0,
            "target_theorem_submissions": 0,
            "proof_values_rendered": 0,
            "capsule_writes": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise ResultError("induction diagnostic identity, evidence, execution, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-induction-argument-diagnostic-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_INDUCTION_ARGUMENT_DIAGNOSTIC_RESULT_OK|base=pass|step=fail|target=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
