#!/usr/bin/env python3
"""Validate one dependent-motive Int.fib_dvd execution."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-plan-v22.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; e=p["execution"]; impl=ROOT/"crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
  assert p["state"]=="preregistered-one-dependent-motive-execution" and sha256(ROOT/pred["path"])==pred["sha256"] and sha256(impl)==p["implementation_sha256"]
  assert e["max_complete_invocations"]==1 and e["max_input_stream_reads"]==4 and e["max_link_checks"]==5 and e["max_target_theorem_submissions"]==1 and e["max_fresh_target_imports"]==2 and e["max_retries"]==e["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-exact-execution-plan-v22: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-exact-execution-plan-v22: PASS: runs=0/1|links=0/5|targets=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
