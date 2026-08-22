#!/usr/bin/env python3
"""Validate bounded module staging for Int.fib_eq_zero residual export."""
import json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-construction-plan-v3.json"
def main():
 try:
  p=json.loads(PLAN.read_text()); d=json.loads((ROOT/p["predecessor"]).read_text()); c=p["cleanup"]; s=p["staging"]; exe=p["execution"]
  assert p["state"]=="preregistered-after-module-path-decline-before-staging-or-reexport" and d["export"]["partial_bytes"]==0 and d["export"]["declarations_exported"]==0
  partial=pathlib.Path(c["exact_partial"]); assert partial.is_file() and partial.stat().st_size==c["required_bytes"]==0
  assert s["source_olean"].endswith(".olean") and s["source_ilean"].endswith(".ilean") and s["destinations_must_not_preexist"] is True and s["cleanup_after_export"] is True
  assert exe=={"max_partial_removals":1,"max_staged_file_copies":2,"max_additional_lean_compilations":0,"max_fresh_exporter_runs":2,"max_importer_runs":4,"target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-construction-plan-v3: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-construction-plan-v3: PASS: partials=0/1|staged=0/2|exports=0/2|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
