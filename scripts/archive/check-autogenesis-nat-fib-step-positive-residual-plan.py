#!/usr/bin/env python3
"""Validate function-abstracted Fibonacci step-positivity residual plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-step-positive-residual-plan-v5.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; s=p["source"]; b=p["budget"]
  assert p["state"]=="preregistered-before-source-construction-or-lean-execution" and sha(ROOT/pred["path"])==pred["sha256"] and s["must_not_preexist"] is True and not (ROOT/s["path"]).exists() and s["forbidden_roots"]==["Nat.fib","Nat.fib_add_two","Nat.fib_pos","Nat.fib_eq_zero"] and s["expected_direct_theorem_dependencies"]==["Eq.symm","congrArg"]
  assert p["output_must_not_preexist"] is True and not pathlib.Path(p["output"]).exists() and b=={"max_source_writes":1,"max_lean_compilations":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_retries":0,"target_theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-step-positive-residual-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-step-positive-residual-plan: PASS: source=0/1|compiles=0/1|exports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
