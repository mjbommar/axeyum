#!/usr/bin/env python3
"""Validate the exact provisional direct residual observation."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-result-v3.json"; PACK=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-nonneg-residual-v3")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; c=r["capsule"]; t=r["theorem"]
  assert r["state"]=="provisional-empty-footprint-dependency-prediction-mismatch" and sha(ROOT/p["path"])==p["sha256"]
  assert sha(PACK/"root.ndjson")==c["sha256"] and (PACK/"root.ndjson").stat().st_size==c["bytes"] and sha(PACK/"manifest.json")==c["manifest_sha256"]
  assert stat.S_IMODE((PACK/"root.ndjson").stat().st_mode)==0o444 and stat.S_IMODE(PACK.stat().st_mode)==0o555
  assert t["axiom_footprint"]==[] and t["predicted_direct_theorem_dependencies"]==[] and t["actual_direct_theorem_dependencies"]==["Eq.symm"]
  assert r["execution"]=={"stage_copies":1,"exporter_invocations":2,"importer_runs":2,"exports_byte_identical":True,"observations_identical":True,"cleanup_removals":1,"staged_module_removed":True,"target_theorem_submissions":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-result-v3: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-result-v3: PASS: footprint=0|dependency_mismatch=Eq.symm|credit=0"); return 0
if __name__=="__main__": raise SystemExit(main())
