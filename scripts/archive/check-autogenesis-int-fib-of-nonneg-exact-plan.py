#!/usr/bin/env python3
"""Validate the exact Int.fib_of_nonneg specialization plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-exact-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; inputs=p["inputs"]; c=p["construction"]; e=p["execution"]; fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-before-exact-specialization-driver" and sha(ROOT/pred["path"])==pred["sha256"] and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  for item in inputs: assert sha(pathlib.Path(item["path"]))==item["sha256"]
  assert c["driver_must_not_preexist"] is True and not (ROOT/c["driver"]).exists() and c["specialization_arguments"]==["Int.fib","Nat.fib","Int.fib_natCast"]
  assert c["expected_direct_theorem_dependencies"]==["Axeyum.Autogenesis.intFibOfNonnegResidualV1","Int.fib_natCast"] and c["expected_closure_extra_dependencies"]==["Eq.symm"] and c["output_must_not_preexist"] is True and not pathlib.Path(c["output"]).exists()
  assert e=={"max_driver_compilations":1,"max_input_stream_reads":2,"max_composition_operations":1,"max_composition_replays":1,"max_specializations":1,"max_specialization_replays":1,"max_target_exports":1,"max_fresh_imports":2,"max_retries":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-exact-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-exact-plan: PASS: compiles=0/1|specializations=0/1|imports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
