#!/usr/bin/env python3
"""Validate reusable exact-name Nat.fib_add_two capsule materialization plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-add-two-library-materialization-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; f=p["measured_frontier"]; a=p["admitted_source"]; impl=p["implementation"]; b=p["budget"]
  assert p["state"]=="preregistered-before-reusable-exact-name-capsule-code" and sha(ROOT/pred["path"])==pred["sha256"] and f["registered_admissible_fact_ids"]==[]
  target=f["next_bottom_up_fact"]; assert sha(ROOT/target["path"])==target["sha256"] and json.loads((ROOT/target["path"]).read_text())["epistemic_status"]==target["status"]=="open"
  fact=a["fact"]; assert sha(ROOT/fact["path"])==fact["sha256"] and json.loads((ROOT/fact["path"]).read_text())["epistemic_status"]==fact["status"]=="proved"
  receipt=a["receipt"]; stream=a["stream"]; assert sha(ROOT/receipt["path"])==receipt["sha256"] and sha(pathlib.Path(stream["path"]))==stream["sha256"] and pathlib.Path(stream["path"]).stat().st_size==stream["bytes"]
  assert sha(ROOT/impl["path"])==impl["sha256_before"] and impl["max_source_edits"]==1 and impl["mode"]=="--export-admitted-capsule" and impl["output_must_not_preexist"] is True and not pathlib.Path(impl["output"]).exists()
  assert b=={"max_compilations":1,"max_complete_invocations":1,"max_stream_reads":1,"max_fixed_reconstructions":1,"max_exact_name_submissions":1,"max_exports":1,"max_fresh_imports":2,"max_retries":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-add-two-library-materialization-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-add-two-library-materialization-plan: PASS: edits=0/1|runs=0/1|reads=0/1|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
