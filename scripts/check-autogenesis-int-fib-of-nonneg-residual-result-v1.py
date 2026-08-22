#!/usr/bin/env python3
"""Validate the missing-olean residual export decline."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-result-v1.json"; PACK=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-nonneg-residual-v1")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; s=r["source"]; pack=r["rejected_pack"]
  assert r["state"]=="declined-export-before-stream-missing-olean" and sha(ROOT/p["path"])==p["sha256"] and sha(ROOT/s["path"])==s["sha256"] and s["typecheck_status"]==0 and s["olean_created"] is False
  assert r["attempt"]=={"module":"AxeyumIntFibOfNonnegResidualV1","exporter_exit_status":0,"diagnostic":"unknown module prefix AxeyumIntFibOfNonnegResidualV1","completed_export":False}
  assert (PACK/"root.ndjson").stat().st_size==pack["root_bytes"]==0 and sha(PACK/"root.ndjson")==pack["root_sha256"] and sha(PACK/"manifest.json")==pack["manifest_sha256"]
  assert stat.S_IMODE((PACK/"root.ndjson").stat().st_mode)==0o444 and stat.S_IMODE(PACK.stat().st_mode)==0o555
  assert r["execution"]=={"compiler_invocations":1,"exporter_attempts":1,"completed_exporter_invocations":0,"second_export_started":False,"importer_runs":0,"target_theorem_submissions":0,"ledger_writes":0}
  assert r["authority"]=={"residual_credit":0,"target_theorem_credit":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-result-v1: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-result-v1: PASS: typecheck=1|exports=0|imports=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
