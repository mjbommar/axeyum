#!/usr/bin/env python3
"""Validate isolated Nat.fib_pos admission replay authority."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-admission-replay-plan-v1.json"; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-admission-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); r=json.loads(RESULT.read_text()); source=p["source"]; archive=pathlib.Path(p["primary_archive"]["path"]); replay=p["replay"]
  assert p["state"]=="preregistered-after-primary-recovery-before-isolated-replay" and r["identity"]["transaction_sha256"]==source["transaction_sha256"] and r["identity"]["after_fact_sha256"]==source["after_fact_sha256"]
  assert sha(archive/"frontier-before.json")==r["archive"]["frontier_before_file_sha256"] and sha(archive/"execution.json")==r["archive"]["execution_file_sha256"] and sha(archive/"transaction.json")==r["archive"]["transaction_file_sha256"] and sha(archive/"frontier-after.json")==r["archive"]["frontier_after_file_sha256"] and sha(archive/"readiness.json")==r["archive"]["readiness_file_sha256"]
  assert replay["must_not_preexist"] is True and not pathlib.Path(replay["output"]).exists() and replay["expected_fault_exit"]==75 and replay["authoritative_ledger_writes"]==1 and source["expected_newly_ready"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-admission-replay-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-admission-replay-plan: PASS: replays=0/1|faults=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
