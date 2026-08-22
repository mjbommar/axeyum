#!/usr/bin/env python3
"""Validate isolated replay of crash-safe Int.fib_of_nonneg admission."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-admission-replay-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); s=p["source"]; a=p["primary_archive"]; r=p["replay"]
  assert p["state"]=="preregistered-after-primary-exit75-recovery-before-isolated-replay" and s["registration_commit"]==r["source_commit"] and s["ledger_writes"]==r["authoritative_ledger_writes"]==1 and s["expected_newly_ready"]==r["expected_newly_ready"]==[]
  root=pathlib.Path(a["path"]); assert all(sha(root/name)==digest for name,digest in a["artifacts"].items())
  assert r["must_not_preexist"] is True and all(not pathlib.Path(r[name]).exists() for name in ("worktree","archive","journal")) and r["max_frontier_builds"]==2 and r["max_operation_executions"]==r["max_transaction_preparations"]==r["max_fault_injection_executions"]==r["max_recovery_executions"]==1 and r["fault_after"]=="intent" and r["expected_fault_exit"]==75
  assert r["expected_after_fact_sha256"]==s["after_fact_sha256"] and r["expected_post_frontier_sha256"]==s["post_frontier_sha256"] and all(p["acceptance"].values())
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-admission-replay-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-admission-replay-plan: PASS: selections=0/1|faults=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
