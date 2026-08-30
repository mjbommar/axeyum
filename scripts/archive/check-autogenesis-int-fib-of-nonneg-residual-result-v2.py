#!/usr/bin/env python3
"""Validate the unstaged-olean residual export decline."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-result-v2.json"; PACK=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-nonneg-residual-v2")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; a=r["attempt"]; pack=r["rejected_pack"]
  assert r["state"]=="declined-export-olean-outside-lake-search-path" and sha(ROOT/p["path"])==p["sha256"]
  assert a["olean_created"] is True and a["olean_bytes"]==16216 and a["staged_in_lake_search_path"] is False and a["exporter_exit_status"]==0
  assert (PACK/"root.ndjson").stat().st_size==pack["root_bytes"]==0 and sha(PACK/"root.ndjson")==pack["root_sha256"] and sha(PACK/"manifest.json")==pack["manifest_sha256"]
  assert stat.S_IMODE((PACK/"root.ndjson").stat().st_mode)==0o444 and stat.S_IMODE(PACK.stat().st_mode)==0o555
  assert r["execution"]=={"olean_compilations":1,"exporter_attempts":1,"completed_exports":0,"second_export_started":False,"importer_runs":0,"target_theorem_submissions":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-result-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-result-v2: PASS: olean=1|staged=0|exports=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
