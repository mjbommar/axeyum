#!/usr/bin/env python3
"""Validate corrected exact-name Nat.fib_add_two materialization execution."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-add-two-library-materialization-execution-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; i=p["implementation"]; e=p["execution"]; o=p["outputs"]
  assert p["state"]=="preregistered-after-clippy-left-stale-binary" and sha(ROOT/pred["path"])==pred["sha256"] and pred["implementation_commit"]=="65b3fee94676331cc794a7d200d283a49af2a3fe"
  assert sha(ROOT/i["path"])==i["sha256"] and i["clippy_compilations_already_spent"]==1 and i["existing_binary_is_stale"] is True
  assert e["max_binary_builds"]==e["max_complete_invocations"]==e["max_stream_reads"]==e["max_fixed_reconstructions"]==e["max_exact_name_submissions"]==e["max_exports"]==1 and e["max_fresh_imports"]==2 and e["max_retries"]==e["fact_status_changes"]==e["ledger_writes"]==0
  assert o["must_not_preexist"] is True and not pathlib.Path(o["capsule"]).exists() and not (ROOT/o["result"]).exists()
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-add-two-library-materialization-execution-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-add-two-library-materialization-execution-plan: PASS: builds=0/1|runs=0/1|reads=0/1|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
