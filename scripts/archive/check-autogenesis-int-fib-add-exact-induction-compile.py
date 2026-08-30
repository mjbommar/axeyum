#!/usr/bin/env python3
"""Validate exact induction compilation and qualification plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-exact-induction-compile-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-exact-induction-execution-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); source=ROOT/r["source"]["path"]
  assert r["state"]=="exact-constructive-induction-compiled-no-theorem-credit" and sha(source)==r["source"]["sha256"] and r["source"]["forbidden_names_absent"] is True
  assert all(name not in source.read_text() for name in ["Int.inductionOn","Int.fib","Int.fib_add","propext","Classical.choice"])
  assert r["execution"]["source_compilations"]==1 and r["authority"]["exact_induction_credit"]==0 and p["source"]["olean_sha256"]==r["environment"]["olean_sha256"] and p["source"]["target"]==r["source"]["target"]
  assert sha(ROOT/p["measurement"]["tool"])==p["measurement"]["tool_sha256"] and p["budget"]["max_remote_exports"]==2 and p["budget"]["max_fresh_imports"]==2 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-exact-induction-compile: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-exact-induction-compile: PASS: compile=1/1|credit=0|exports=0/2|imports=0/2"); return 0
if __name__=="__main__": raise SystemExit(main())
