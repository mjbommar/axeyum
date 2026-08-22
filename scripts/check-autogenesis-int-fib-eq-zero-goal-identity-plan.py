#!/usr/bin/env python3
"""Validate the nonrendering Int.fib_eq_zero identity audit plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-goal-identity-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); i=p["input"]; f=p["fact"]; tool=p["tool"]; exe=p["execution"]
  assert p["state"]=="preregistered-before-single-nonrendering-capsule-read" and sha(ROOT/p["predecessor"]["path"])==p["predecessor"]["sha256"]
  ip=pathlib.Path(i["path"]); assert ip.stat().st_size==i["bytes"] and sha(ip)==i["sha256"] and i["root"]=="Int.fib_eq_zero"
  fp=ROOT/f["path"]; assert sha(fp)==f["sha256"] and json.loads(fp.read_text())["epistemic_status"]=="open"
  assert sha(ROOT/tool["path"])==tool["sha256"] and not (ROOT/p["output"]).exists()
  assert exe=={"max_importer_runs":1,"max_stream_reads":1,"max_retries":0,"rendered_proof_terms":0,"rendered_theorem_types":0,"rendered_theorem_values":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-goal-identity-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-goal-identity-plan: PASS: reads=0/1|imports=0/1|rendered=0|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
