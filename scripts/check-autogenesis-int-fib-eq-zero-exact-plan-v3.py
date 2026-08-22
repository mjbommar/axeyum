#!/usr/bin/env python3
"""Validate the final Int.fib_eq_zero driver borrow correction."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-exact-plan-v3.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); d=json.loads((ROOT/p["predecessor"]).read_text()); driver=p["driver"]; exe=p["execution"]
  assert p["state"]=="preregistered-after-borrow-lint-before-one-signature-correction" and d["effects"]["input_stream_reads"]==d["effects"]["ledger_writes"]==0
  assert sha(ROOT/driver["path"])==driver["sha256_before"] and driver["allowed_change"]=="pass target_evidence to write_result by shared reference"
  assert exe=={"max_source_edits":1,"max_additional_compilations":1,"max_stream_reads":0,"max_target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-exact-plan-v3: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-exact-plan-v3: PASS: edits=0/1|compiles=0/1|reads=0|targets=0|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
