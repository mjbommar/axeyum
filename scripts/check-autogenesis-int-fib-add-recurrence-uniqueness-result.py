#!/usr/bin/env python3
"""Validate accepted recurrence uniqueness and its bounded support API plan."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-recurrence-uniqueness-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-specialization-support-api-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); pack=pathlib.Path(r["pack"]["path"]); target=r["target"]
  assert r["state"]=="accepted-reproduced-empty-footprint-recurrence-uniqueness" and sha(pack/"manifest.json")==r["pack"]["manifest_sha256"] and sha(pack/"root-1.ndjson")==sha(pack/"root-2.ndjson")==r["pack"]["root_sha256"]
  assert stat.S_IMODE(pack.stat().st_mode)==0o555 and target["axiom_footprint"]==[] and target["direct_theorem_dependencies"]==["And.left","And.right","Eq.symm","Eq.trans","congrArg"] and r["authority"]["recurrence_uniqueness_credit"]==1
  for path,digest in zip(r["fresh_imports"]["result_paths"],r["fresh_imports"]["result_sha256"],strict=True): assert sha(pathlib.Path(path))==digest
  assert p["query"]["public_declaration"]=="Int.inductionOn" and p["query"]["proof_body_may_be_read"] is False and p["budget"]["max_compiler_invocations"]==1 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-recurrence-uniqueness-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-recurrence-uniqueness-result: PASS: exports=2|imports=2|axioms=0|next_type_queries=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
