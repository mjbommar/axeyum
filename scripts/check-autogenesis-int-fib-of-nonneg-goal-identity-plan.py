#!/usr/bin/env python3
"""Validate the nonrendering Int.fib_of_nonneg goal identity plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-goal-identity-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; i=p["input"]; fact=p["fact"]; tool=p["tool"]
  assert p["state"]=="preregistered-before-single-nonrendering-capsule-read" and sha(ROOT/pred["path"])==pred["sha256"]
  path=pathlib.Path(i["path"]); assert path.stat().st_size==i["bytes"] and sha(path)==i["sha256"] and i["root"]=="Int.fib_of_nonneg"
  assert sha(ROOT/fact["path"])==fact["sha256"] and json.loads((ROOT/fact["path"]).read_text())["epistemic_status"]==fact["required_status"]=="open"
  assert sha(ROOT/tool["path"])==tool["sha256"] and tool["binary_present"] is True and (ROOT/tool["binary"]).is_file()
  assert p["execution"]=={"max_importer_runs":1,"max_stream_reads":1,"max_retries":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
  assert not (ROOT/p["output"]).exists()
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-goal-identity-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-goal-identity-plan: PASS: reads=0/1|renders=0|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
