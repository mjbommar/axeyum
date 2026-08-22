#!/usr/bin/env python3
"""Validate the induction adapter and its five-support successor plan."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-induction-adapter-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-constructor-laws-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); pack=pathlib.Path(r["pack"]["path"]); target=r["target"]
  assert r["state"]=="accepted-reproduced-empty-footprint-constructive-induction-adapter" and sha(pack/"manifest.json")==r["pack"]["manifest_sha256"] and sha(pack/"root-1.ndjson")==sha(pack/"root-2.ndjson")==r["pack"]["root_sha256"]
  assert stat.S_IMODE(pack.stat().st_mode)==0o555 and target["axiom_footprint"]==[] and target["direct_theorem_dependencies"]==["Eq.symm","Exists.elim","Or.elim"] and r["authority"]["induction_support_credit"]==1
  for path,digest in zip(r["fresh_imports"]["result_paths"],r["fresh_imports"]["result_sha256"],strict=True): assert sha(pathlib.Path(path))==digest
  assert len(p["ordered_targets"])==5 and p["ordered_targets"][0]["name"]=="Axeyum.Autogenesis.intConstructorSplitV1" and p["budget"]["max_source_compilations"]==1 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-induction-adapter-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-induction-adapter-result: PASS: adapter_axioms=0|targets=5|compiles=0/1|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
