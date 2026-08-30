#!/usr/bin/env python3
"""Validate constructor-law compilation and the five-root execution plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-constructor-laws-compile-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-constructor-laws-execution-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); source=ROOT/r["source"]["path"]
  assert r["state"]=="five-constructor-supports-compiled-no-theorem-credit" and sha(source)==r["source"]["sha256"] and r["source"]["forbidden_names_absent"] is True
  assert all(name not in source.read_text() for name in ["Int.inductionOn","Int.fib","Int.fib_add","propext","Classical.choice"])
  assert len(r["ordered_targets"])==5 and p["ordered_roots"]==r["ordered_targets"] and p["source"]["olean_sha256"]==r["environment"]["olean_sha256"]
  assert r["execution"]["source_compilations"]==1 and r["authority"]["constructor_support_credit"]==0 and sha(ROOT/p["measurement"]["tool"])==p["measurement"]["tool_sha256"]
  assert p["budget"]["max_remote_exports"]==2 and p["budget"]["max_fresh_imports"]==2 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-constructor-laws-compile: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-constructor-laws-compile: PASS: targets=5|compile=1/1|credit=0|exports=0/2"); return 0
if __name__=="__main__": raise SystemExit(main())
