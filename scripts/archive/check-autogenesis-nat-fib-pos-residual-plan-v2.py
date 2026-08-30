#!/usr/bin/env python3
"""Validate narrow V2 repairs for the Nat.fib_pos residual."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-residual-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; s=p["source"]; e=p["execution"]
  assert p["state"]=="preregistered-after-first-compile-localized-two-elaboration-repairs" and sha(ROOT/pred["path"])==pred["sha256"] and sha(ROOT/s["path"])==s["sha256_before"] and len(s["permitted_edits"])==2 and len(s["forbidden_edits"])==4
  assert e=={"max_source_edits":1,"max_lean_compilations":1,"max_exporter_invocations":2,"max_importer_runs":2,"max_retries":0,"target_theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0} and p["output_must_not_preexist"] is True and not pathlib.Path(p["output"]).exists()
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-residual-plan-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-residual-plan-v2: PASS: edits=0/1|compiles=0/1|exports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
