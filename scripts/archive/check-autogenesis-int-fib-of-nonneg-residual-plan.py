#!/usr/bin/env python3
"""Validate the direct constructor residual boundary for Int.fib_of_nonneg."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; r=p["residual"]; o=p["output"]; e=p["execution"]; fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-before-direct-residual-source" and sha(ROOT/pred["path"])==pred["sha256"]
  assert t["fact_id"]=="F:ml430-int-fib-of-nonneg-438018c5" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert r["name"]=="Axeyum.Autogenesis.intFibOfNonnegResidualV1" and r["source_must_not_preexist"] is True and not (ROOT/r["source"]).exists()
  assert r["forbidden_roots"]==["Int.fib_of_nonneg","Int.negSucc_not_nonneg","Int.negSucc_lt_zero","Int.not_le_of_gt"] and "nomatch" in r["method"]
  assert o["must_not_preexist"] is True and not pathlib.Path(o["pack"]).exists()
  assert e=={"max_source_writes":1,"max_compiler_invocations":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_retries":0,"residual_theorem_submissions":1,"target_theorem_submissions":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-plan: PASS: compiles=0/1|exports=0/2|targets=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
