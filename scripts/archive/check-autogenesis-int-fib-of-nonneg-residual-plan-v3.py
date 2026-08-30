#!/usr/bin/env python3
"""Validate scoped module staging for the direct nonnegative residual."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-plan-v3.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; s=p["staging"]; x=p["export"]; e=p["execution"]; fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-scoped-module-staging-before-export" and sha(ROOT/pred["path"])==pred["sha256"] and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert s["source_bytes"]==16216 and s["destination_must_not_preexist"] is s["cleanup_required"] is True and s["copy_operations"]==s["cleanup_operations"]==1
  assert x["root"]=="Axeyum.Autogenesis.intFibOfNonnegResidualV1" and x["must_not_preexist"] is x["stderr_must_be_empty"] is True and not pathlib.Path(x["pack"]).exists()
  assert e=={"max_compilations":0,"max_stage_copies":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_cleanup_removals":1,"max_retries":0,"target_theorem_submissions":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-plan-v3: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-plan-v3: PASS: stage=0/1|exports=0/2|cleanup=0/1|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
