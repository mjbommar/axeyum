#!/usr/bin/env python3
"""Validate rejection of assumption-bearing negSucc nonnegativity support."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-negsucc-support-result-v1.json"; PACK=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-negsucc-not-nonneg-v1")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; c=r["capsule"]; t=r["theorem"]
  assert r["state"]=="rejected-assumption-bearing-biconditional" and sha(ROOT/p["path"])==p["sha256"]
  assert sha(PACK/"root.ndjson")==c["sha256"] and (PACK/"root.ndjson").stat().st_size==c["bytes"] and sha(PACK/"manifest.json")==c["manifest_sha256"]
  assert stat.S_IMODE((PACK/"root.ndjson").stat().st_mode)==0o444 and stat.S_IMODE(PACK.stat().st_mode)==0o555
  assert t["name"]=="Int.negSucc_not_nonneg" and t["axiom_footprint"]==["propext"] and t["direct_theorem_dependencies"]==["Eq.trans","Int.negSucc_lt_zero","Int.not_le._simp_1","iff_false"]
  assert r["execution"]=={"exporter_invocations":1,"exporter_stderr_bytes":0,"importer_runs":2,"observations_identical":True,"forbidden_target_present":False,"target_theorem_submissions":0,"ledger_writes":0}
  assert r["authority"]=={"support_credit":0,"theorem_credit":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-negsucc-support-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-negsucc-support-result: PASS: rejected=propext|imports=2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
