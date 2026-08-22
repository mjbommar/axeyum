#!/usr/bin/env python3
"""Validate the hash-only Int.gcd_fib identity audit authority."""

import hashlib, json, pathlib, stat, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-goal-identity-plan-v1.json"

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    try:
        plan = json.loads(PLAN.read_text()); fact_path = ROOT / plan["fact"]["path"]; fact = json.loads(fact_path.read_text()); source = pathlib.Path(plan["input"]["path"]); tool = ROOT / plan["tool"]["path"]
        valid = (plan.get("state") == "preregistered-before-single-nonrendering-capsule-read"
            and sha256(ROOT / plan["predecessor"]["path"]) == plan["predecessor"].get("sha256")
            and sha256(fact_path) == plan["fact"].get("sha256") and fact.get("id") == plan["fact"].get("id") and fact.get("epistemic_status") == "open"
            and source.stat().st_size == plan["input"].get("bytes") and stat.S_IMODE(source.stat().st_mode) == 0o444 and sha256(source) == plan["input"].get("sha256")
            and sha256(tool) == plan["tool"].get("sha256") and plan["acceptance"].get("name") == "Int.gcd_fib"
            and plan["execution"].get("max_importer_runs") == 1 and plan["execution"].get("max_stream_reads") == 1
            and plan["execution"].get("max_retries") == 0 and plan["execution"].get("ledger_writes") == 0)
        if not valid: raise ValueError("goal identity authority changed")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-goal-identity-plan: FAIL: {error}", file=sys.stderr); return 1
    print("autogenesis-int-gcd-fib-goal-identity-plan: PASS: reads=0/1|rendered=0|ledger_writes=0"); return 0

if __name__ == "__main__": raise SystemExit(main())
