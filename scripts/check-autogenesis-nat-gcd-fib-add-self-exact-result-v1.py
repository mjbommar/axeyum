#!/usr/bin/env python3
"""Verify the first exact Fibonacci GCD-shift source-build decline."""
from __future__ import annotations
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-exact-plan-v1.json"
PLAN_SHA256 = "8124c428e2092945a1a4e1fd9e7be321e21948fe5f9561d5d33eab103cb67d13"
EXECUTION = {"driver_builds": 1, "input_stream_reads": 0, "capsule_compositions": 0, "local_gcd_comm_submissions": 0, "exact_target_submissions": 0, "complete_invocations": 0, "retries": 0}
AUTHORITY = {"target_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def check() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "first-driver-build-declined-before-stream-read-or-submission-no-retry"
    assert sha256(PLAN) == result["plan"]["sha256"] == PLAN_SHA256
    assert result["attempted_source"]["sha256"] == "e2e60c3aa113395fbd55d1b582418c4b92c7e6e8a3bddbff384afc379e851179"
    assert result["attempted_source"]["retained_in_git"] is False
    assert result["decline"]["executable_produced"] is False
    assert result["execution"] == EXECUTION and result["authority"] == AUTHORITY
def main() -> int:
    try: check()
    except (AssertionError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-exact-result-v1: {error}", file=sys.stderr); return 1
    print("AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_EXACT_RESULT_V1_OK|builds=1|reads=0|submissions=0")
    return 0
if __name__ == "__main__": raise SystemExit(main())
