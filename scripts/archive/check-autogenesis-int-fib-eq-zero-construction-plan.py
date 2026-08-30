#!/usr/bin/env python3
"""Validate the preregistered Int.fib_eq_zero construction boundary."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-construction-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); t=p["target"]; c=p["construction"]; outputs=p["outputs"]; exe=p["execution"]
  assert p["state"]=="preregistered-before-source-construction-or-proof-stream-access" and sha(ROOT/p["predecessor"]["path"])==p["predecessor"]["sha256"]
  fact=ROOT/t["fact_path"]; assert sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert c["source_must_not_preexist"] is True and not (ROOT/c["source"]).exists() and c["imports"]==["Init.Prelude"]
  assert "Int.natAbs_eq_zero" in c["support"]["forbidden_constants"] and "Int.fib_eq_zero" in c["residual"]["forbidden_constants"] and len(c["residual"]["parameters"])==5
  assert outputs["must_not_preexist"] is True and not pathlib.Path(outputs["directory"]).exists() and len(p["later_exact_inputs"])==2
  assert exe=={"max_lean_compilations":1,"max_exporter_runs":2,"max_importer_runs":4,"require_byte_identical_streams":True,"max_source_corrections":0,"target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-construction-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-construction-plan: PASS: compiles=0/1|exports=0/2|imports=0/4|targets=0|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
