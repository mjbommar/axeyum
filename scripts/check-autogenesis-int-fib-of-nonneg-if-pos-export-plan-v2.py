#!/usr/bin/env python3
"""Validate the corrected containing-module if_pos export plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-if-pos-export-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; target=p["target"]; env=p["fixed_environment"]; support=p["support"]; command=p["command"]; execution=p["execution"]
  fact=ROOT/target["fact_path"]
  assert p["state"]=="preregistered-corrected-containing-module-before-second-export" and sha(ROOT/pred["path"])==pred["sha256"]
  assert target["fact_id"]=="F:ml430-int-fib-of-nonneg-438018c5" and sha(fact)==target["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert env["hostname"]=="server5" and env["mathlib_commit"]=="c5ea00351c28e24afc9f0f84379aa41082b1188f" and env["lean_version"]=="4.30.0" and env["lean4export_binary_sha256"]=="8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
  assert p["environment_probe"]=={"command":"import Mathlib.Data.Int.Fib.Basic; #check if_pos","result":"if_pos elaborates with the expected conditional-equality type","proof_stream_reads":0}
  assert support=={"module":"Mathlib.Data.Int.Fib.Basic","ordered_roots":["if_pos"],"forbidden_roots":["Int.fib_of_nonneg"],"root_selection_required":True}
  assert command["stderr_must_be_empty"] is command["output_must_not_preexist"] is True and command["minimum_bytes"]==174
  assert execution["max_exporter_invocations"]==execution["max_root_stream_writes"]==1 and execution["max_importer_runs"]==2 and execution["max_retries"]==0
  assert execution["rendered_proof_terms"]==execution["rendered_theorem_types"]==execution["rendered_theorem_values"]==execution["target_theorem_submissions"]==execution["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as e: print(f"autogenesis-int-fib-of-nonneg-if-pos-export-plan-v2: FAIL: {e}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-if-pos-export-plan-v2: PASS: exporter=0/1|imports=0/2|forbidden_target=1|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
