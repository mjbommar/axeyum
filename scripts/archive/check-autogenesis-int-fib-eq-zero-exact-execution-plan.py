#!/usr/bin/env python3
"""Validate one exact Int.fib_eq_zero execution authority."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-exact-execution-plan-v4.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); driver=p["driver"]; out=p["output"]; exe=p["execution"]
  assert p["state"]=="preregistered-after-clippy-clean-driver-before-proof-stream-execution" and sha(ROOT/driver["path"])==driver["sha256"] and driver["clippy"]=="passed"
  for item in p["inputs"]: assert sha(pathlib.Path(item["path"]))==item["sha256"]
  assert out["parent_must_not_preexist"] is True and not pathlib.Path(out["path"]).parent.exists()
  assert exe=={"max_complete_invocations":1,"max_input_stream_reads":3,"max_composition_operations":2,"max_composition_replays":2,"max_specializations":1,"max_specialization_replays":1,"max_target_exports":1,"max_fresh_imports":2,"max_retries":0,"fact_status_changes":0,"ledger_writes":0}
  assert len(p["acceptance"]["direct_theorem_dependencies"])==4 and p["acceptance"]["axiom_footprint"]==[]
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-exact-execution-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-exact-execution-plan: PASS: runs=0/1|reads=0/3|compositions=0/2|targets=0/1|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
