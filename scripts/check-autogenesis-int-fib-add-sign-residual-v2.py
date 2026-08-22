#!/usr/bin/env python3
"""Validate accepted pair-case evidence and recurrence-uniqueness successor plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-sign-residual-result-v2.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-recurrence-uniqueness-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); t=r["target"]
  assert r["state"]=="accepted-empty-footprint-after-hash-only-contract-correction" and t["axiom_footprint"]==[] and t["direct_theorem_dependencies"]==["Eq.symm","Exists.elim","Or.elim"] and r["authority"]=={"residual_credit":1,"exact_int_fib_add_credit":0}
  assert r["execution"]=={"hash_only_reads":3,"proof_bearing_stream_reads":0,"compilations":0,"exports":0,"imports":0,"theorem_submissions":0,"exact_target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
  capsule=pathlib.Path(p["inputs"]["pair_case_capsule"]["path"]); assert sha(capsule)==p["inputs"]["pair_case_capsule"]["sha256"]==r["evidence"]["root_sha256"]
  assert p["design"]["target"]=="Axeyum.Autogenesis.intFibonacciRecurrenceUniqueV1" and p["budget"]["max_source_compilations"]==1 and p["budget"]["max_exports"]==0 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-sign-residual-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-sign-residual-v2: PASS: residual=accepted|axioms=0|next=recurrence-uniqueness|compiles=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
