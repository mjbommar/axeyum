#!/usr/bin/env python3
"""Validate the selected empty-footprint GCD recursion bridge."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-gcd-recursion-bridge-result-v2.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    result = json.loads(RESULT.read_text())
    plan = result.get("plan") or {}
    pack = result.get("evidence_pack") or {}
    pack_path = pathlib.Path(pack["path"])
    recorded = json.loads((pack_path / "observation.json").read_text())
    candidates = {row["name"]: row for row in recorded["candidates"]}
    selected = candidates["Axeyum.Autogenesis.officialNatGcdSuccClosedV1"]
    rejected = candidates["Axeyum.Autogenesis.nat_gcd_succ"]
    if (
        result.get("state") != "official-closed-successor-bridge-selected-empty-footprint"
        or sha(ROOT / plan["path"]) != plan.get("sha256")
        or sha(pack_path / "SHA256SUMS") != pack.get("index_sha256")
        or sha(pack_path / "observation.json") != pack.get("observation_sha256")
        or sha(pack_path / "stderr.txt") != pack.get("stderr_sha256")
        or selected.get("present") is not True
        or selected.get("definitionally_equal") is not True
        or selected.get("axiom_footprint_count") != 0
        or result.get("selection", {}).get("type_sha256") != selected.get("type_sha256")
        or rejected.get("present") is not True
        or rejected.get("definitionally_equal") is not False
        or result.get("execution") != recorded.get("execution")
        or result.get("authority") != {
            "bridge_selection_credit": 1,
            "target_credit": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("bridge selection identity, evidence, or authority changed")
    return result


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-gcd-recursion-bridge-result-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_GCD_RECURSION_BRIDGE_RESULT_V2_OK|selected=official-closed|defeq=1|footprint=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
