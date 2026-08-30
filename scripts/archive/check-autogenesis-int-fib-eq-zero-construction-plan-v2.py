#!/usr/bin/env python3
"""Validate the bounded Int.fib_eq_zero elaboration correction."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-construction-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); d=json.loads((ROOT/p["predecessor"]).read_text()); s=p["source"]; remote=p["remote"]; exe=p["execution"]
  assert p["state"]=="preregistered-after-elaboration-decline-before-source-correction" and d["effects"]["exporter_runs"]==d["effects"]["ledger_writes"]==0
  assert sha(ROOT/s["path"])==s["sha256_before"] and len(s["allowed_changes"])==2 and "theorem statements" in s["forbidden_changes"]
  assert remote["olean_must_not_preexist"] is True and remote["ilean_must_not_preexist"] is True and not pathlib.Path(p["outputs"]["directory"]).exists()
  assert exe=={"max_source_corrections":1,"max_additional_lean_compilations":1,"max_exporter_runs":2,"max_importer_runs":4,"target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-construction-plan-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-construction-plan-v2: PASS: corrections=0/1|compiles=0/1|exports=0/2|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
