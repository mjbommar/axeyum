#!/usr/bin/env python3
"""Validate induction-adapter compilation and its execution plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-induction-adapter-compile-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-induction-adapter-execution-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); source=ROOT/r["source"]["path"]
  assert r["state"]=="compiled-constructive-adapter-no-theorem-credit" and sha(source)==r["source"]["sha256"] and r["source"]["forbidden_names_absent"] is True
  text=source.read_text(); assert all(name not in text for name in ["Int.inductionOn","Int.fib","Int.fib_add","propext","Classical.choice"])
  assert r["execution"]=={"source_writes":1,"source_compilations":1,"exports":0,"imports":0,"retries":0,"theorem_submissions":1,"exact_target_submissions":0,"fact_status_changes":0,"ledger_writes":0} and r["authority"]["induction_support_credit"]==0
  assert p["source"]["olean_sha256"]==r["environment"]["olean_sha256"] and p["source"]["target"]==r["source"]["target"] and sha(ROOT/p["measurement"]["tool"])==p["measurement"]["tool_sha256"]
  assert p["budget"]["max_remote_exports"]==2 and p["budget"]["max_fresh_imports"]==2 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-induction-adapter-compile: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-induction-adapter-compile: PASS: compile=1/1|credit=0|exports=0/2|imports=0/2"); return 0
if __name__=="__main__": raise SystemExit(main())
