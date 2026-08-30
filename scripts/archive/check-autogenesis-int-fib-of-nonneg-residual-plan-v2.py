#!/usr/bin/env python3
"""Validate the explicit-olean residual export repair."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; s=p["source"]; t=p["target"]; x=p["export"]; e=p["execution"]; fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-explicit-olean-before-repaired-export" and sha(ROOT/pred["path"])==pred["sha256"] and sha(ROOT/s["path"])==s["sha256"] and " -o " in f" {s['compile_shape']} "
  assert t["fact_id"]=="F:ml430-int-fib-of-nonneg-438018c5" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert x["root"]=="Axeyum.Autogenesis.intFibOfNonnegResidualV1" and x["must_not_preexist"] is x["stderr_must_be_empty"] is True and not pathlib.Path(x["pack"]).exists()
  assert e=={"max_olean_compilations":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_retries":0,"target_theorem_submissions":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-plan-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-plan-v2: PASS: olean=0/1|exports=0/2|imports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
