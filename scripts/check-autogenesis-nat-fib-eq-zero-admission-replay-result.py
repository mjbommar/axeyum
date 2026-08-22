#!/usr/bin/env python3
"""Validate the isolated Nat.fib_eq_zero admission replay result."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-admission-replay-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); a=r["archive"]; root=pathlib.Path(a["path"]); replay=json.loads((root/"replay.json").read_text())
  for name,key in [("replay.json","replay_file_sha256"),("frontier-before.json","frontier_before_file_sha256"),("execution.json","execution_file_sha256"),("transaction.json","transaction_file_sha256"),("admission-event.json","admission_event_file_sha256"),("frontier-after.json","frontier_after_file_sha256"),("readiness.json","readiness_file_sha256")]: assert sha(root/name)==a[key]
  assert r["state"]=="isolated-clean-semantic-replay-accepted" and replay["replay_sha256"]==r["identity"]["replay_sha256"] and replay["checks"]==r["checks"] and all(r["checks"].values())
  assert r["fault"]=={"boundary":"after-intent","exit_status":75,"fact_unchanged_before_recovery":True} and r["result"]=={"recovery_executions":1,"authoritative_ledger_writes":1,"expected_newly_ready":[],"actual_newly_ready":[],"fact_operation_checker_passed":True}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-eq-zero-admission-replay-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-admission-replay-result: PASS: fault=75|recovery=1|writes=1|newly_ready=0"); return 0
if __name__=="__main__": raise SystemExit(main())
