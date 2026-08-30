#!/usr/bin/env python3
"""Validate corrected crash-safe Int.fib_of_nonneg admission execution."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-admission-execution-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); reg=p["registration"]; pre=p["preflight_rejection"]; inputs=p["inputs"]; c=p["correction"]; proto=p["protocol"]; wt=pathlib.Path(reg["worktree"])
  assert p["state"]=="preregistered-after-archived-before-fact-preflight-rejection" and subprocess.check_output(["git","rev-parse","HEAD"],cwd=wt,text=True).strip()==reg["commit"]
  fact=wt/c["before_fact"]; assert sha(fact)==pre["fact_sha256_after"] and json.loads(fact.read_text())["epistemic_status"]==pre["fact_status_after"]=="open" and pre["exit_code"]==1 and pre["durable_intents"]==pre["ledger_writes"]==0
  for item in inputs.values(): assert sha(pathlib.Path(item["path"]))==item["sha256"]
  journal=pathlib.Path(c["journal"]); assert journal.is_dir() and not any(journal.rglob("*")) and c["must_be_canonical_repository_path"] is True and c["fault_after"]=="intent" and c["expected_exit"]==75
  assert proto=={"max_corrected_apply_attempts":1,"require_fact_unchanged_after_fault":True,"max_recovery_attempts":1,"authoritative_ledger_writes":1,"max_retries_after_intent":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError,subprocess.CalledProcessError) as error: print(f"autogenesis-int-fib-of-nonneg-admission-execution-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-admission-execution-plan: PASS: corrected_applies=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
