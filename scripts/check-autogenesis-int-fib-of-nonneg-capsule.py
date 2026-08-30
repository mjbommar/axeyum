#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_of_nonneg."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; CONSTRUCTION=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-exact-result-v1.json"; IDENTITY=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-goal-identity-result-v1.json"; FACT=ROOT/"artifacts/facts/F-ml430-int-fib-of-nonneg-438018c5.json"; CAPSULE=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-nonneg-exact-v1/root.ndjson"); MANIFEST=CAPSULE.parent/"manifest.json"
DEPS=["Axeyum.Autogenesis.intFibOfNonnegResidualV1","Int.fib_natCast"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def validate():
 c=json.loads(CONSTRUCTION.read_text()); i=json.loads(IDENTITY.read_text()); f=json.loads(FACT.read_text()); t=i["theorem"]
 assert sha(CAPSULE)=="efb1875d675810bdf737215b5ebbc2e1afeb1f085c6b1cfccc56d9b779540bd9" and sha(MANIFEST)=="c79087ba0b3ab464193edb4b177951f5e88024ce0f115f9ec52ab9e18c64d380" and stat.S_IMODE(CAPSULE.stat().st_mode)==0o444 and stat.S_IMODE(CAPSULE.parent.stat().st_mode)==0o555
 assert c["state"]=="accepted-exact-target-specialized-exported-twice-reimported-and-sealed" and c["target"]["axiom_footprint"]==[] and c["target"]["direct_theorem_dependencies"]==DEPS and t["canonical_type_sha256"]=="a413a3afa1649837fd125688c9a49be0755f288964fa425bad8ae7875fba9f0a" and t["canonical_declaration_sha256"]=="67ad588faa0778a3fa0f76890475ced5d41c575cfad76238f614dec52798aa80" and t["direct_theorem_dependencies"]==DEPS
 statement=f["formal"]["statement"]; authority={"fact_id":f["id"],"formal_statement_sha256":hashlib.sha256(statement.encode()).hexdigest(),"result_manifest":"artifacts/autogenesis/mathlib-int-fib-of-nonneg-goal-identity-result-v1.json","result_manifest_sha256":sha(IDENTITY),"capsule_path":str(CAPSULE),"capsule_sha256":"efb1875d675810bdf737215b5ebbc2e1afeb1f085c6b1cfccc56d9b779540bd9","target_theorem":"Int.fib_of_nonneg","goal_sha256":"a413a3afa1649837fd125688c9a49be0755f288964fa425bad8ae7875fba9f0a","declaration_sha256":"67ad588faa0778a3fa0f76890475ced5d41c575cfad76238f614dec52798aa80","axiom_footprint":[],"direct_theorem_dependencies":DEPS,"fresh_imports":2,"fixed_plan_reconstructions":1,"target_theorem_submissions":1,"search_invocations":0,"ledger_writes":0}
 return {"authority":authority,"receipt_sha256":digest(authority)}
def main():
 try: receipt=validate(); assert receipt["receipt_sha256"]=="21be310e9e3e0175d7f79ba8409ea1ebec37a71532c4d0e4a8720e94cb2ed0e2"
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"sealed-int-fib-of-nonneg-capsule: FAIL: {error}",file=sys.stderr); return 1
 print(f"sealed-int-fib-of-nonneg-capsule: PASS: receipt={receipt['receipt_sha256']} target=Int.fib_of_nonneg footprint=0 dependencies=2"); return 0
if __name__=="__main__": raise SystemExit(main())
