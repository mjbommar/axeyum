#!/usr/bin/env python3
"""Validate exact Int.fib_eq_zero admission authority."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-admission-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); t=p["target"]; e=p["evidence"]; fact=ROOT/"artifacts/facts/F-ml430-int-fib-eq-zero-8193c7cb.json"
  assert p["state"]=="preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert sha(pathlib.Path(e["capsule_path"]))==e["capsule_sha256"] and sha(pathlib.Path(e["manifest_path"]))==e["manifest_sha256"] and sha(ROOT/e["construction_result"])==e["construction_result_sha256"] and sha(ROOT/e["identity_result"])==e["identity_result_sha256"]
  assert not e["axiom_footprint"] and len(e["direct_theorem_dependencies"])==4 and p["budget"]=={"max_operation_registrations":1,"max_fault_injection_executions":1,"max_recovery_executions":1,"max_authoritative_ledger_writes":1,"max_clean_replays":1,"max_search_invocations":0,"max_evaluations":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-admission-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-admission-plan: PASS: operation=0/1|fault=0/1|recovery=0/1|writes=0/1|replay=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
