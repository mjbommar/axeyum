#!/usr/bin/env python3
"""Validate the nonrendering Int.fib_of_nonneg goal identity result."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-goal-identity-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); theorem=r["theorem"]; execution=r["execution"]
  assert r["state"]=="exact-goal-identity-bound-without-rendering" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha(pathlib.Path(r["input"]["path"]))==r["input"]["sha256"]
  assert theorem=={"name":"Int.fib_of_nonneg","canonical_type_sha256":"a413a3afa1649837fd125688c9a49be0755f288964fa425bad8ae7875fba9f0a","canonical_declaration_sha256":"67ad588faa0778a3fa0f76890475ced5d41c575cfad76238f614dec52798aa80","axiom_footprint":[],"direct_theorem_dependencies":["Axeyum.Autogenesis.intFibOfNonnegResidualV1","Int.fib_natCast"]}
  assert r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0} and execution=={"importer_runs":1,"stream_reads":1,"retries":0,"ledger_writes":0} and r["authority"]=={"qualified_exact_target":1,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-goal-identity-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-goal-identity-result: PASS: type=a413a3afa...|axioms=0|renders=0|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
