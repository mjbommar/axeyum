#!/usr/bin/env python3
"""Validate the sealed empty-footprint if_pos support capsule."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-if-pos-export-result-v2.json"; PACK=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/if-pos-mathlib-basic-v1")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); plan=r["plan"]; c=r["capsule"]; t=r["theorem"]; e=r["execution"]
  assert r["state"]=="qualified-sealed-if-pos-root-empty-footprint" and sha(ROOT/plan["path"])==plan["sha256"]
  assert sha(PACK/"root.ndjson")==c["sha256"] and (PACK/"root.ndjson").stat().st_size==c["bytes"] and sha(PACK/"manifest.json")==c["manifest_sha256"]
  assert stat.S_IMODE((PACK/"root.ndjson").stat().st_mode)==0o444 and stat.S_IMODE(PACK.stat().st_mode)==0o555
  assert t=={"name":"if_pos","canonical_type_sha256":"bea4c2dc0742e0d32e503e825af128997b6f84e269773683edab93a29ee599aa","canonical_declaration_sha256":"389c40b4ea4ac025ec31cf30ae1e601a6c9780952a08f1220a875db7fcf4e09a","axiom_footprint":[],"direct_theorem_dependencies":[]}
  assert e=={"exporter_invocations":1,"exporter_stderr_bytes":0,"root_stream_writes":1,"importer_runs":2,"observations_identical":True,"forbidden_target_scans":1,"forbidden_target_present":False,"retries":0,"target_theorem_submissions":0,"ledger_writes":0}
  assert r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0} and r["authority"]=={"support_credit":1,"target_theorem_credit":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-if-pos-export-result-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-if-pos-export-result-v2: PASS: root=if_pos|imports=2|footprint=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
