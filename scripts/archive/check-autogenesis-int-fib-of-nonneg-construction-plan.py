#!/usr/bin/env python3
"""Validate the exact Int.fib_of_nonneg construction boundary."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-construction-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); t=p["target"]; inputs=p["inputs"]; pred=p["predecessor"]; c=p["construction"]; e=p["execution"]
  fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-before-driver-code-or-target-submission" and t["fact_id"]=="F:ml430-int-fib-of-nonneg-438018c5" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert sha(ROOT/pred["path"])==pred["sha256"] and len(inputs)==2
  for item in inputs:
   path=pathlib.Path(item["path"]); assert sha(path)==item["sha256"] and path.stat().st_size==item["bytes"]
  assert c["driver"]=="crates/axeyum-lean-import/examples/int_fib_of_nonneg_exact.rs" and not (ROOT/c["driver"]).exists() and c["driver_must_not_preexist"] is True
  assert c["expected_direct_theorem_dependencies"]==["if_pos"] and c["forbidden_roots"]==["Int.fib_of_nonneg"] and c["output_must_not_preexist"] is True and not pathlib.Path(c["output"]).exists()
  assert e=={"max_driver_compilations":1,"max_input_stream_reads":2,"max_composition_operations":1,"max_composition_replays":1,"max_target_theorem_submissions":1,"max_target_exports":1,"max_fresh_imports":2,"max_retries":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-construction-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-construction-plan: PASS: compiles=0/1|reads=0/2|targets=0/1|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
