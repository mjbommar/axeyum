#!/usr/bin/env python3
"""Validate the nonrendering Int.fib_dvd goal identity plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-goal-identity-plan-v1.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; fact=p["fact"]; tool=p["tool"]
  assert p["state"]=="preregistered-before-single-nonrendering-capsule-read" and sha256(ROOT/pred["path"])==pred["sha256"] and sha256(ROOT/fact["path"])==fact["sha256"] and json.loads((ROOT/fact["path"]).read_text())["epistemic_status"]=="open" and sha256(ROOT/tool["path"])==tool["sha256"]
  assert p["execution"]=={"max_importer_runs":1,"max_stream_reads":1,"max_retries":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-goal-identity-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-goal-identity-plan: PASS: reads=0/1|renders=0|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
