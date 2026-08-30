#!/usr/bin/env python3
"""Verify the single-change V3 exact-target plan."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v3.json"
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v2.json"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def check() -> None:
    plan = json.loads(PLAN.read_text()); result = json.loads(RESULT.read_text())
    assert sha256(RESULT) == plan["predecessor"]["sha256"]
    assert result["execution"]["input_stream_reads"] == result["execution"]["exact_target_submissions"] == 0
    assert plan["authorized_change"].startswith("add #[allow(clippy::too_many_lines)] to run")
    assert plan["acceptance"]["target_axiom_footprint"] == []
    assert plan["budget"] == {"max_driver_builds": 1, "max_complete_invocations": 2, "max_exact_target_submissions": 2, "max_retries": 0}
    assert all(value == 0 for value in plan["authority"].values())
def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-exact-plan-v3: {error}", file=sys.stderr); return 1
    print("AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EXACT_PLAN_V3_OK|change=lint-allow|runs=2|retries=0"); return 0
if __name__ == "__main__": raise SystemExit(main())
