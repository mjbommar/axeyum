#!/usr/bin/env python3
"""Validate the nonrendering Int.fib_dvd goal identity result."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-goal-identity-result-v1.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); theorem=r["theorem"]; execution=r["execution"]
  assert r["state"]=="exact-goal-identity-bound-without-rendering" and sha256(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha256(pathlib.Path(r["input"]["path"]))==r["input"]["sha256"]
  assert theorem["name"]=="Int.fib_dvd" and theorem["canonical_type_sha256"]=="ed84c258cad64868b6e14a1fe1cf46732aa2ca7e231defa0a627a16fae795016" and theorem["axiom_footprint"]==[] and len(theorem["direct_theorem_dependencies"])==6
  assert r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0} and execution=={"importer_runs":1,"stream_reads":1,"retries":0,"ledger_writes":0} and r["authority"]["qualified_exact_target"]==1
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-goal-identity-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-goal-identity-result: PASS: type=ed84c258...|axioms=0|renders=0|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
