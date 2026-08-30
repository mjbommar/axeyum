#!/usr/bin/env python3
"""Validate the Nat.fib_eq_zero residual construction plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-residual-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; r=p["residual"]; o=p["outputs"]; e=p["execution"]
  assert p["state"]=="preregistered-before-source-construction-or-lean-execution" and sha(ROOT/pred["path"])==pred["sha256"]
  fact=ROOT/t["fact_path"]; assert sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]==t["required_status"]=="open"
  assert r["source_must_not_preexist"] is True and not (ROOT/r["source"]).exists() and r["imports"]==["Init.Prelude"] and len(r["parameters"])==4 and "Nat.fib" in r["forbidden_constants"] and "Nat.fib_eq_zero" in r["forbidden_constants"]
  assert o["must_not_preexist"] is True and not pathlib.Path(o["directory"]).exists() and e=={"max_lean_compilations":1,"max_exporter_runs":2,"max_importer_runs":2,"require_byte_identical_streams":True,"max_source_corrections":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-eq-zero-residual-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-residual-plan: PASS: compiles=0/1|exports=0/2|imports=0/2|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
