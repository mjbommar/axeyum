#!/usr/bin/env python3
"""Validate the twice-reconstructed exact Nat.fib_dvd capsule."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-dvd-construction-result-v1.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result["plan"]
    implementation = result["implementation"]
    pack = result["evidence_pack"]
    pack_path = pathlib.Path(pack["path"])
    first = json.loads((pack_path / "observation-1.json").read_text())
    second = json.loads((pack_path / "observation-2.json").read_text())
    target = dict(result["target"])
    target_goal_sha256 = target.pop("goal_sha256")
    if (
        result.get("state")
        != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
        or sha(ROOT / plan["path"]) != plan["sha256"]
        or sha(ROOT / implementation["path"]) != implementation["sha256"]
        or sha(pack_path / "SHA256SUMS") != pack["index_sha256"]
        or sha(pack_path / "observation-1.json") != pack["observation_sha256"]
        or sha(pack_path / "observation-2.json") != pack["observation_sha256"]
        or sha(pack_path / "target-1.ndjson") != pack["capsule_sha256"]
        or sha(pack_path / "target-2.ndjson") != pack["capsule_sha256"]
        or stat.S_IMODE(pack_path.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack_path.iterdir())
        or first != second
        or first.get("target") != target
        or first.get("target_goal_sha256") != target_goal_sha256
        or first.get("capsule", {}).get("bytes") != result.get("capsule", {}).get("bytes")
        or first.get("capsule", {}).get("sha256") != result.get("capsule", {}).get("sha256")
        or result.get("execution")
        != {
            "complete_invocations": 2,
            "target_theorem_submissions": 2,
            "exports": 2,
            "fresh_imports": 4,
            "outputs_byte_identical": True,
            "observations_byte_identical": True,
            "retries": 0,
            "search_invocations": 0,
            "ledger_writes": 0,
        }
        or result.get("authority")
        != {
            "target_credit": 1,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("Nat.fib_dvd result identity, evidence, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-dvd-construction-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_DVD_CONSTRUCTION_RESULT_OK|runs=2|imports=4|footprint=0|target_credit=1")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
