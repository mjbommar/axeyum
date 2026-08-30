#!/usr/bin/env python3
"""Validate exact Int.fib_eq_zero goal identity and manifest."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-goal-identity-result-v1.json"; MANIFEST=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-eq-zero-exact-v1/manifest.json")
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); t=r["theorem"]; m=json.loads(MANIFEST.read_text()); raw=pathlib.Path(r["raw_audit"]["path"])
  assert r["state"]=="exact-goal-identity-bound-without-rendering" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha(raw)==r["raw_audit"]["sha256"]
  assert t["name"]=="Int.fib_eq_zero" and t["canonical_declaration_sha256"]=="3df28cc187a56dd5774f529937eeb2aff53b4c919ab130976c804b3a929b82e7" and not t["axiom_footprint"] and len(t["direct_theorem_dependencies"])==4
  assert m["theorem"]["canonical_type_sha256"]==t["canonical_type_sha256"] and m["theorem"]["direct_theorem_dependencies"]==t["direct_theorem_dependencies"] and m["root"]["sha256"]==r["input"]["sha256"]
  assert r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0} and r["execution"]["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-goal-identity-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-goal-identity-result: PASS: target=Int.fib_eq_zero|type-bound|footprint=0|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
