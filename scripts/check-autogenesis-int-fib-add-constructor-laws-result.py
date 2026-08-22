#!/usr/bin/env python3
"""Validate five constructor supports and exact induction plan."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-constructor-laws-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-exact-induction-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); pack=pathlib.Path(r["pack"]["path"])
  assert r["state"]=="accepted-five-reproduced-empty-footprint-constructor-supports" and sha(pack/"manifest.json")==r["pack"]["manifest_sha256"] and sha(pack/"roots-1.ndjson")==sha(pack/"roots-2.ndjson")==r["pack"]["root_sha256"] and stat.S_IMODE(pack.stat().st_mode)==0o555
  assert len(r["ordered_targets"])==5 and r["axiom_footprints"]==[[],[],[],[],[]] and r["authority"]=={"constructor_support_credit":5,"exact_int_fib_add_credit":0}
  for path,digest in zip(r["fresh_imports"]["result_paths"],r["fresh_imports"]["result_sha256"],strict=True): assert sha(pathlib.Path(path))==digest
  assert sha(pathlib.Path(p["inputs"]["adapter"]["path"]))==p["inputs"]["adapter"]["sha256"] and sha(pathlib.Path(p["inputs"]["constructor_laws"]["path"]))==p["inputs"]["constructor_laws"]["sha256"]
  assert p["target"]["name"]=="Axeyum.Autogenesis.intSuccPredInductionV1" and p["budget"]["max_source_compilations"]==1 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-constructor-laws-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-constructor-laws-result: PASS: roots=5|axioms=0|next=exact-induction|compiles=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
