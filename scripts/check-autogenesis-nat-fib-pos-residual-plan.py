#!/usr/bin/env python3
"""Validate function-abstracted Nat.fib_pos residual plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-residual-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; c=p["construction"]; e=p["environment"]; b=p["budget"]
  assert p["state"]=="preregistered-before-source-construction-or-lean-execution" and sha(ROOT/pred["path"])==pred["sha256"]
  fact=ROOT/t["fact_path"]; assert sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]==t["required_status"]=="open"
  assert c["source_must_not_preexist"] is True and not (ROOT/c["source"]).exists() and c["function_abstracted"] is True and c["forbidden_roots"]==["Nat.fib","Nat.fib_pos","Nat.fib_eq_zero"] and c["expected_direct_theorem_dependencies"]==[] and c["output_must_not_preexist"] is True and not pathlib.Path(c["output"]).exists()
  assert e["mathlib_commit"]=="c5ea00351c28e24afc9f0f84379aa41082b1188f" and e["lean_version"]=="4.30.0" and e["lean4export_binary_sha256"]=="8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
  assert b=={"max_source_writes":1,"max_lean_compilations":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_retries":0,"target_theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-residual-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-residual-plan: PASS: source=0/1|compiles=0/1|exports=0/2|imports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
