#!/usr/bin/env python3
"""Validate the preregistered exact Nat.fib_pos admission."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-admission-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); t=p["target"]; e=p["evidence"]; b=p["budget"]; fact=ROOT/"artifacts/facts/F-ml430-nat-fib-pos-9e67bd8e.json"
  assert p["state"]=="preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert sha(ROOT/e["construction_result"])==e["construction_result_sha256"] and sha(ROOT/e["identity_result"])==e["identity_result_sha256"] and sha(pathlib.Path(e["capsule_path"]))==e["capsule_sha256"] and sha(pathlib.Path(e["manifest_path"]))==e["manifest_sha256"]
  assert e["receipt_sha256"]=="60954cc8fbe7d947c08ffca5dbc55e600864151ca5a824c3d950614478c46aff" and e["axiom_footprint"]==[] and len(e["direct_theorem_dependencies"])==5
  assert p["operation"]["registry_writes"]==1 and p["protocol"]["fault_injection_after_intent_exit"]==75 and b["max_operation_registrations"]==b["max_authoritative_ledger_writes"]==b["max_clean_replays"]==1 and p["expected_newly_ready"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-admission-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-admission-plan: PASS: operation=1|fault=1|recovery=1|ledger_writes=1|replays=1"); return 0
if __name__=="__main__": raise SystemExit(main())
