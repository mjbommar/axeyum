#!/usr/bin/env python3
"""Validate hash-only qualification of the exact nonnegative residual closure."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-qualification-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; c=p["capsule"]; q=p["qualification"]; e=p["execution"]
  assert p["state"]=="preregistered-hash-only-exact-dependency-qualification" and sha(ROOT/pred["path"])==pred["sha256"]
  path=pathlib.Path(c["path"]); assert sha(path)==c["sha256"] and path.stat().st_size==c["bytes"] and sha(path.parent/"manifest.json")==c["manifest_sha256"]
  assert q["root"]=="Axeyum.Autogenesis.intFibOfNonnegResidualV1" and q["axiom_footprint"]==[] and q["exact_direct_theorem_dependencies"]==["Eq.symm"]
  assert e=={"max_committed_result_reads":1,"max_capsule_hash_reads":1,"max_exporter_invocations":0,"max_importer_runs":0,"max_theorem_submissions":0,"max_ledger_writes":0}
  assert p["acceptance"]=={"residual_credit":1,"target_theorem_credit":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-qualification-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-qualification-plan: PASS: dependency=Eq.symm|reruns=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
