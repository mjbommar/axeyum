#!/usr/bin/env python3
"""Validate the retained successful helper associativity repair diagnostic."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-helper-assoc-repair-result-v1.json"


class ResultError(RuntimeError):
    """The repair evidence or its zero-authority boundary changed."""


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
        result.get("state")
        != "one-associativity-middle-corrected-helper-type-definitionally-equal-no-submission"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or sha(ROOT / implementation["path"]) != implementation.get("sha256")
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation.json") != pack.get("observation_sha256")
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack_path.iterdir())
        or observation.get("definitionally_equal") is not True
        or observation.get("proof_value_rendered") is not False
        or result.get("repair")
        != {
            "source_edits": 1,
            "corrected_middle": "m*q + (r + m)",
            "theorem_statement_changes": 0,
            "route_changes": 0,
        }
        or result.get("execution")
        != {
            "complete_diagnostics": 1,
            "proof_inferences": 1,
            "proof_values_rendered": 0,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or any(value != 0 for value in result.get("authority", {}).values())
    ):
        raise ResultError("repair identity, diagnostic, evidence, or authority changed")
    recorded = json.loads((pack_path / "observation.json").read_text())
    if (
        recorded.get("definitionally_equal") is not True
        or recorded.get("expected", {}).get("sha256")
        != observation.get("expected_type_sha256")
        or recorded.get("inferred", {}).get("sha256")
        != observation.get("inferred_type_sha256")
        or recorded.get("execution") != result.get("execution")
    ):
        raise ResultError("recorded diagnostic does not match the retained result")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"autogenesis-nat-fib-gcd-helper-assoc-repair-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_HELPER_ASSOC_REPAIR_RESULT_OK|inferences=1|defeq=1|submissions=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
