#!/usr/bin/env python3
"""Validate exact Nat.fib_eq_zero admission authority."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-admission-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); t=p["target"]; e=p["evidence"]; fact=ROOT/"artifacts/facts/F-ml430-nat-fib-eq-zero-61879073.json"
  assert p["state"]=="preregistered-sealed-capsule-admission-before-operation-code-or-ledger-write" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert sha(ROOT/e["construction_result"])==e["construction_result_sha256"] and sha(ROOT/e["identity_result"])==e["identity_result_sha256"] and sha(pathlib.Path(e["capsule_path"]))==e["capsule_sha256"] and sha(pathlib.Path(e["manifest_path"]))==e["manifest_sha256"]
  assert e["receipt_sha256"]=="c8466767c516d48e0e214aaf7e8a43e88a8bc7fa952a7baa2748eff03d51f3d3" and e["axiom_footprint"]==[] and len(e["direct_theorem_dependencies"])==4 and p["expected_newly_ready"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-eq-zero-admission-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-admission-plan: PASS: operation=1|fault=1|recovery=1|writes=1|replay=1"); return 0
if __name__=="__main__": raise SystemExit(main())
