#!/usr/bin/env python3
"""Validate the retained V2 target rejection and zero-credit boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-result-v2.json"


class ResultError(RuntimeError):
    """The V2 rejection, evidence, or zero authority changed."""


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    implementation = result.get("implementation") or {}
    pack = result.get("evidence_pack") or {}
    observation = result.get("observation") or {}
    pack_path = pathlib.Path(pack["path"])
    if (
        result.get("state") != "helper-accepted-target-type-mismatch-second-run-skipped-zero-credit"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or sha(ROOT / implementation["path"]) != implementation.get("sha256")
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation-1.json") != pack.get("observation_sha256")
        or sha(pack_path / "stderr-1.txt") != pack.get("stderr_sha256")
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack_path.iterdir())
        or observation.get("helper_submission_accepted") is not True
        or observation.get("target_submission_accepted") is not False
        or observation.get("capsule_output_written") is not False
        or observation.get("second_invocation_skipped") is not True
        or "TypeMismatch" not in observation.get("error", "")
        or (pack_path / "observation-1.json").stat().st_size != 0
        or observation.get("error", "") not in (pack_path / "stderr-1.txt").read_text()
        or result.get("execution")
        != {
            "complete_invocations": 0,
            "capsule_reads": 2,
            "fresh_output_imports": 0,
            "helper_theorem_submissions": 1,
            "target_theorem_submissions": 1,
            "proof_search_invocations": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise ResultError("V2 rejection identity, evidence, execution, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-construction-result-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_CONSTRUCTION_RESULT_V2_OK|helper=1|target_rejected=1|run2=skipped|credit=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
