#!/usr/bin/env python3
"""Validate the nonrendering Nat.fib_pos goal identity result."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-goal-identity-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); t=r["theorem"]
  assert r["state"]=="exact-goal-identity-bound-without-rendering" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha(pathlib.Path(r["input"]["path"]))==r["input"]["sha256"]
  assert t=={"name":"Nat.fib_pos","canonical_type_sha256":"24233cf6ebabcb044ad6fa8be564c7cfbff822a421afb1c94ff906c65d029f56","canonical_declaration_sha256":"f441b137a185604cee38d4f5c311cd48cd83ffb4279ceab467c7852dad326e65","axiom_footprint":[],"direct_theorem_dependencies":["Axeyum.Autogenesis.natFibOnePositiveV1","Axeyum.Autogenesis.natFibPosResidualV1","Axeyum.Autogenesis.natFibStepPositiveV1","Axeyum.Autogenesis.natFibZeroV1","Nat.zero_lt_succ"]}
  assert r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0} and r["execution"]=={"importer_runs":1,"stream_reads":1,"retries":0,"ledger_writes":0} and r["authority"]["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-goal-identity-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-goal-identity-result: PASS: type=24233cf6e...|axioms=0|renders=0|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
