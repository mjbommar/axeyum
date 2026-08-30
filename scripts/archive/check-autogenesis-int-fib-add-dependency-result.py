#!/usr/bin/env python3
"""Validate Int.fib_add dependency localization and the residual plan."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-dependency-audit-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-sign-residual-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); audit_path=pathlib.Path(r["audit"]["path"]); audit=json.loads(audit_path.read_text())
  assert sha(audit_path)==r["audit"]["sha256"] and stat.S_IMODE(audit_path.stat().st_mode)==0o444 and stat.S_IMODE(audit_path.parent.stat().st_mode)==0o555
  projected=[{"name":row["name"],"class":row["class"],"declaration_sha256":row["declaration_sha256"],**({"direct_theorem_dependencies":row["direct_theorem_dependencies"]} if row["class"]=="empty-footprint" else {})} for row in audit["rows"]]
  assert projected==r["roots"] and audit["summary"]["class_counts"]=={"empty-footprint":2,"other-assumption-bearing":0,"propext-bearing":3} and audit["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0}
  assert len(r["decision"]["reusable_roots"])==2 and len(r["decision"]["forbidden_composition_roots"])==3 and p["target"]["name"]=="Axeyum.Autogenesis.intPairCasesResidualV1"
  assert p["budget"]["max_source_compilations"]==1 and p["budget"]["max_exact_target_submissions"]==0 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-dependency-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-dependency-result: PASS: clean=2|rejected=3|residual_compiles=0/1|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
