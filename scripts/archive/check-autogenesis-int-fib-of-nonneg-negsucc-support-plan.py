#!/usr/bin/env python3
"""Validate the bounded negative-constructor support export."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-negsucc-support-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; env=p["fixed_environment"]; s=p["support"]; c=p["command"]; e=p["execution"]; fact=ROOT/t["fact_path"]
  assert p["state"]=="preregistered-before-negative-constructor-support-export" and sha(ROOT/pred["path"])==pred["sha256"]
  assert t["fact_id"]=="F:ml430-int-fib-of-nonneg-438018c5" and sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  assert env["hostname"]=="server5" and env["mathlib_commit"]=="c5ea00351c28e24afc9f0f84379aa41082b1188f" and env["lean_version"]=="4.30.0" and env["lean4export_binary_sha256"]=="8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
  assert s["ordered_roots"]==["Int.negSucc_not_nonneg"] and s["forbidden_roots"]==["Int.fib_of_nonneg"] and s["root_selection_required"] is True
  assert c["output_must_not_preexist"] is c["stderr_must_be_empty"] is True and not pathlib.Path(c["output"]).exists() and c["minimum_bytes"]==174
  assert e=={"max_exporter_invocations":1,"max_root_stream_writes":1,"max_importer_runs":2,"max_retries":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"target_theorem_submissions":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-negsucc-support-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-negsucc-support-plan: PASS: exporters=0/1|imports=0/2|targets=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
