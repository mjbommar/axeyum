#!/usr/bin/env python3
"""Validate exact qualification of the direct nonnegative residual."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-residual-qualification-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; c=r["capsule"]; t=r["theorem"]; path=pathlib.Path(c["path"])
  assert r["state"]=="qualified-exact-residual-empty-footprint" and sha(ROOT/p["path"])==p["sha256"] and sha(path)==c["sha256"] and path.stat().st_size==c["bytes"]
  assert t=={"name":"Axeyum.Autogenesis.intFibOfNonnegResidualV1","canonical_type_sha256":"d398a26df89636ad189b8e1439d79744a4aea222a95233da4962e8c5fb2d5471","canonical_declaration_sha256":"2373556137e8144c5927501b5fe2eaa4fa3ac7357cdd5d58d89b21e43e13e605","axiom_footprint":[],"direct_theorem_dependencies":["Eq.symm"]}
  assert r["execution"]=={"committed_result_reads":1,"capsule_hash_reads":1,"exporter_invocations":0,"importer_runs":0,"theorem_submissions":0,"ledger_writes":0} and r["authority"]["residual_credit"]==1
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-residual-qualification-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-residual-qualification-result: PASS: footprint=0|dependencies=Eq.symm|credit=1"); return 0
if __name__=="__main__": raise SystemExit(main())
