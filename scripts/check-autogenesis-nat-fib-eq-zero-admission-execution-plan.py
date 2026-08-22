#!/usr/bin/env python3
"""Validate crash-safe Nat.fib_eq_zero admission execution authority."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-admission-execution-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); reg=p["registration"]; inputs=p["inputs"]; a=p["apply"]; proto=p["protocol"]; wt=pathlib.Path(reg["worktree"])
  assert p["state"]=="preregistered-after-clean-commit-transaction-before-fault-injection" and subprocess.check_output(["git","rev-parse","HEAD"],cwd=wt,text=True).strip()==reg["commit"]
  for name in ("frontier","execution","transaction"): assert sha(pathlib.Path(inputs[name]["path"]))==inputs[name]["file_sha256"]
  fact=wt/a["before_fact"]; assert sha(fact)==inputs["before_fact"]["sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  journal=pathlib.Path(a["journal"]); assert journal.is_dir() and not any(journal.rglob("*")) and a["must_be_canonical_repository_path"] is True and a["fault_after"]=="intent" and a["expected_exit"]==75
  assert p["selection"]=={"fact_id":"F:ml430-nat-fib-eq-zero-61879073","operation_id":"authoritative-mathlib-nat-fib-eq-zero-kernel-capsule-v1","unique_admissible":True}
  assert proto=={"max_fault_injection_executions":1,"require_fact_unchanged_after_fault":True,"max_recovery_executions":1,"authoritative_ledger_writes":1,"max_retries_after_intent":0} and p["expected_newly_ready"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError,subprocess.CalledProcessError) as error: print(f"autogenesis-nat-fib-eq-zero-admission-execution-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-admission-execution-plan: PASS: faults=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
