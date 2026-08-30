#!/usr/bin/env python3
"""Validate sealed exact Int.fib_eq_zero capsule and receipt."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; C=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-exact-result-v1.json"; I=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-goal-identity-result-v1.json"; F=ROOT/"artifacts/facts/F-ml430-int-fib-eq-zero-8193c7cb.json"; CAPSULE=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-eq-zero-exact-v1/root.ndjson"); MANIFEST=CAPSULE.parent/"manifest.json"; DEPS=["Axeyum.Autogenesis.intFibEqZeroResidualV1","Axeyum.Autogenesis.intFibNatAbsV1","Axeyum.Autogenesis.intNatAbsEqZeroV1","Nat.fib_eq_zero"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(v): return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def validate():
 c=json.loads(C.read_text()); i=json.loads(I.read_text()); f=json.loads(F.read_text()); t=i["theorem"]
 assert sha(CAPSULE)=="bd36472c8d898066df2c388d30452bd1859a42ffa1b1ae1be184ce5a494a0f73" and sha(MANIFEST)=="50f29b4b26f6638fbff2794686407978a40510ec720354e35ae54237293f7691" and stat.S_IMODE(CAPSULE.stat().st_mode)==stat.S_IMODE(MANIFEST.stat().st_mode)==0o444 and stat.S_IMODE(CAPSULE.parent.stat().st_mode)==0o555
 assert c["target"]["direct_theorem_dependencies"]==t["direct_theorem_dependencies"]==DEPS and t["axiom_footprint"]==[]
 a={"fact_id":f["id"],"formal_statement_sha256":hashlib.sha256(f["formal"]["statement"].encode()).hexdigest(),"result_manifest":"artifacts/autogenesis/mathlib-int-fib-eq-zero-goal-identity-result-v1.json","result_manifest_sha256":sha(I),"capsule_path":str(CAPSULE),"capsule_sha256":"bd36472c8d898066df2c388d30452bd1859a42ffa1b1ae1be184ce5a494a0f73","target_theorem":"Int.fib_eq_zero","goal_sha256":"1822290d2018cbd3e5c956c8c7c4b42704509f20560e8177c6e9a1b9367770bc","declaration_sha256":"3df28cc187a56dd5774f529937eeb2aff53b4c919ab130976c804b3a929b82e7","axiom_footprint":[],"direct_theorem_dependencies":DEPS,"fresh_imports":2,"fixed_plan_reconstructions":1,"target_theorem_submissions":1,"search_invocations":0,"ledger_writes":0}; return {"authority":a,"receipt_sha256":digest(a)}
def main():
 try: checked=validate(); assert checked["receipt_sha256"]=="e005b5983b5cb2eee4350cba4ece4acee1cd0732582769778e279757d47eb00c"
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"sealed-int-fib-eq-zero-capsule: FAIL: {error}",file=sys.stderr); return 1
 print(f"sealed-int-fib-eq-zero-capsule: PASS: receipt={checked['receipt_sha256']} target=Int.fib_eq_zero footprint=0 dependencies=4"); return 0
if __name__=="__main__": raise SystemExit(main())
