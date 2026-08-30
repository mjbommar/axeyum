#!/usr/bin/env python3
"""Validate transition-source Int.fib_eq_zero replay authority."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-admission-replay-plan-v1.json"; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-admission-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); r=json.loads(RESULT.read_text()); source=p["source"]; archive=pathlib.Path(p["primary_archive"]["path"]); replay=p["replay"]
  assert subprocess.check_output(["git","rev-parse",f'{source["commit"]}^'],cwd=ROOT,text=True).strip()==source["parent"] and source["commit"]==r["source"]["detached_transition_commit"]
  fact=subprocess.check_output(["git","show",f'{source["commit"]}:artifacts/facts/F-ml430-int-fib-eq-zero-8193c7cb.json'],cwd=ROOT); assert hashlib.sha256(fact).hexdigest()==r["identity"]["after_fact_sha256"]
  assert sha(archive/"frontier-before.json")==p["primary_archive"]["frontier_before_file_sha256"] and not pathlib.Path(source["worktree"]).exists() and source["worktree_must_not_preexist"] is True
  assert replay["must_not_preexist"] is True and not pathlib.Path(replay["output"]).exists() and replay["max_driver_invocations"]==1 and replay["expected_fault_exit"]==75 and replay["authoritative_ledger_writes"]==1
 except (AssertionError,OSError,ValueError,KeyError,TypeError,subprocess.CalledProcessError) as error: print(f"autogenesis-int-fib-eq-zero-admission-replay-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-admission-replay-plan: PASS: driver=0/1|faults=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
