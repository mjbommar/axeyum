#!/usr/bin/env python3
"""Verify the official-arithmetic-base-first V2 clean-order plan."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v2.json"
RESULT = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-result-v1.json"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def check() -> None:
    plan=json.loads(PLAN.read_text()); result=json.loads(RESULT.read_text())
    assert sha256(RESULT) == plan["predecessor"]["sha256"]
    assert result["execution"]["support_submissions"] == result["execution"]["exact_target_submissions"] == 0
    assert plan["sequencing_change"][1].startswith("compose and replay the official cancellation capsule")
    assert plan["acceptance"]["all_axiom_footprints"] == [] and plan["acceptance"]["exact_target_submissions"] == 0
    assert plan["budget"]["max_exact_target_submissions"] == plan["budget"]["max_retries"] == 0
    assert all(value == 0 for value in plan["authority"].values())
def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-official-r091-clean-dvd-antisymm-plan-v2: {error}", file=sys.stderr); return 1
    print("AUTOGENESIS_OFFICIAL_R091_CLEAN_DVD_ANTISYMM_PLAN_V2_OK|order=cancellation-first|runs=2|target=0"); return 0
if __name__ == "__main__": raise SystemExit(main())
