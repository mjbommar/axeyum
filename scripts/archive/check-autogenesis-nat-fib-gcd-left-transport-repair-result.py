#!/usr/bin/env python3
"""Validate the successful no-target Nat.fib_gcd left-transport repair."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-left-transport-repair-result-v1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result["plan"]
    pack = result["evidence_pack"]
    pack_path = pathlib.Path(pack["path"])
    recorded = json.loads((pack_path / "observation.json").read_text())
    observation = result["observation"]
    if (
        result.get("state") != "explicit-gcd-left-transport-closes-target-proof-type"
        or sha(ROOT / plan["path"]) != plan["sha256"]
        or sha(pack_path / "SHA256SUMS") != pack["index_sha256"]
        or sha(pack_path / "observation.json") != pack["observation_sha256"]
        or recorded.get("definitionally_equal") is not True
        or recorded.get("expected", {}).get("sha256") != observation["expected_type_sha256"]
        or recorded.get("inferred", {}).get("sha256") != observation["inferred_type_sha256"]
        or result.get("execution") != recorded.get("execution")
        or observation.get("target_submitted") is not False
        or result.get("authority") != {
            "repair_credit": 1,
            "target_credit": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("repair identity, evidence, execution, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-left-transport-repair-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_LEFT_TRANSPORT_REPAIR_RESULT_OK|defeq=1|target_submissions=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
