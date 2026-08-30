#!/usr/bin/env python3
"""Validate the declined V1 residual result and hash-only V2 correction plan."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-sign-residual-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-sign-residual-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); target=r["target"]
  assert r["state"]=="empty-footprint-reproduced-dependency-contract-mismatch-no-credit" and target["axiom_footprint"]==[] and target["dependency_contract_matched"] is False and r["authority"]["residual_credit"]==0
  assert sha(ROOT/r["source"]["path"])==r["source"]["sha256"] and sha(pathlib.Path(r["pack"]["path"])/"manifest.json")==r["pack"]["manifest_sha256"]
  correction=p["correction"]; assert correction["expected_direct_theorem_dependencies"]==target["observed_direct_theorem_dependencies"] and correction["axiom_footprint"]==[] and correction["declaration_sha256"]==target["declaration_sha256"]
  for item,expected in zip(p["inputs"]["import_results"],r["fresh_imports"]["result_sha256"],strict=True): assert sha(pathlib.Path(item["path"]))==item["sha256"]==expected
  assert p["budget"]=={"max_hash_only_reads":3,"max_proof_bearing_stream_reads":0,"max_compilations":0,"max_exports":0,"max_imports":0,"max_theorem_submissions":0,"max_exact_target_submissions":0,"max_fact_status_changes":0,"max_ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-sign-residual-v1-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-sign-residual-v1-v2: PASS: v1=dependency-mismatch|credit=0|v2=hash-only|stream_reads=0"); return 0
if __name__=="__main__": raise SystemExit(main())
