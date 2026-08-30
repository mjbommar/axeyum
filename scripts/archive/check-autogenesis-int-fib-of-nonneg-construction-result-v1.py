#!/usr/bin/env python3
"""Validate the pre-code Int.fib_of_nonneg construction decline."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-construction-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; rep=r["representation"]; e=r["execution"]
  assert r["state"]=="declined-pre-code-representation-mismatch-missing-negative-branch-eliminator" and sha(ROOT/p["path"])==p["sha256"]
  assert sha(ROOT/rep["source"])==rep["sha256"] and r["qualified_support"]=={"name":"if_pos","still_empty_footprint":True,"sufficient_for_target":False}
  assert r["missing_support"]["preferred_root"]=="Int.negSucc_not_nonneg"
  assert e=={"driver_files_created":0,"driver_compilations":0,"input_stream_reads":0,"composition_operations":0,"target_theorem_submissions":0,"exports":0,"fresh_imports":0,"ledger_writes":0}
  assert not (ROOT/"crates/axeyum-lean-import/examples/int_fib_of_nonneg_exact.rs").exists()
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-construction-result-v1: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-construction-result-v1: PASS: compiles=0|targets=0|missing=Int.negSucc_not_nonneg|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
