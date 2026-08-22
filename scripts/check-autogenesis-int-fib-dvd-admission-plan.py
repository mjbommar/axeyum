#!/usr/bin/env python3
"""Validate the preregistered exact Int.fib_dvd admission."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-admission-plan-v1.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); target=p["target"]; ev=p["evidence"]; budget=p["budget"]; fact=ROOT/"artifacts/facts/F-ml430-int-fib-dvd-ffb3c5c1.json"
  assert p["state"]=="preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write" and target["fact_id"]=="F:ml430-int-fib-dvd-ffb3c5c1" and sha256(fact)==target["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert sha256(ROOT/ev["construction_result"])==ev["construction_result_sha256"] and sha256(ROOT/ev["identity_result"])==ev["identity_result_sha256"] and ev["receipt_sha256"]=="a39586b5f2cc15a7e6f6b9d2ac189035c6b81df1825ca83a5c864095bf99b897" and ev["axiom_footprint"]==[] and len(ev["direct_theorem_dependencies"])==6
  assert p["operation"]=={"id":"authoritative-mathlib-int-fib-dvd-kernel-capsule-v1","required_checker":"scripts/check-autogenesis-int-fib-dvd-capsule.py","registry_writes":1} and p["protocol"]["fault_injection_after_intent_exit"]==75 and budget["max_operation_registrations"]==budget["max_authoritative_ledger_writes"]==budget["max_clean_replays"]==1 and p["expected_newly_ready"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-admission-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-admission-plan: PASS: operation=1|fault=1|recovery=1|ledger_writes=1|replays=1"); return 0
if __name__=="__main__": raise SystemExit(main())
