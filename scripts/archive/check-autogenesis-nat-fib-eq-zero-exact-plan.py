#!/usr/bin/env python3
"""Validate exact Nat.fib_eq_zero construction plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-exact-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; t=p["target"]; c=p["construction"]; b=p["budget"]
  assert p["state"]=="preregistered-before-exact-driver-code-or-stream-read" and sha(ROOT/pred["path"])==pred["sha256"]
  fact=ROOT/t["fact_path"]; assert sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]=="open"
  for item in p["inputs"]: assert sha(pathlib.Path(item["path"]))==item["sha256"]
  assert c["driver_must_not_preexist"] is True and not (ROOT/c["driver"]).exists() and not pathlib.Path(c["output"]).parent.exists() and len(c["specialization"]["arguments"])==4 and len(c["expected_direct_theorem_dependencies"])==4
  assert b=={"max_driver_compilations":1,"max_input_stream_reads":2,"max_composition_operations":1,"max_composition_replays":1,"max_specializations":1,"max_specialization_replays":1,"max_target_exports":1,"max_fresh_imports":2,"max_retries":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-eq-zero-exact-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-exact-plan: PASS: compiles=0/1|reads=0/2|specializations=0/1|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
