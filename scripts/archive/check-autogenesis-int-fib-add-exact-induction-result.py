#!/usr/bin/env python3
"""Validate the sealed exact constructive integer-induction result."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-exact-induction-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); pack=pathlib.Path(r["pack"]["path"]); target=r["target"]
  assert r["state"]=="accepted-reproduced-empty-footprint-exact-constructive-induction" and sha(pack/"manifest.json")==r["pack"]["manifest_sha256"] and sha(pack/"root-1.ndjson")==sha(pack/"root-2.ndjson")==r["pack"]["root_sha256"]
  assert stat.S_IMODE(pack.stat().st_mode)==0o555 and target["axiom_footprint"]==[] and len(target["direct_theorem_dependencies"])==6 and r["authority"]=={"exact_induction_credit":1,"exact_int_fib_add_credit":0}
  for path,digest in zip(r["fresh_imports"]["result_paths"],r["fresh_imports"]["result_sha256"],strict=True): assert sha(pathlib.Path(path))==digest
  assert r["execution"]=={"remote_exports":2,"fresh_imports":2,"proof_bearing_stream_reads":2,"retries":0,"compilations":0,"theorem_submissions":0,"exact_target_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-exact-induction-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-exact-induction-result: PASS: exports=2|imports=2|axioms=0|exact_target_credit=0"); return 0
if __name__=="__main__": raise SystemExit(main())
