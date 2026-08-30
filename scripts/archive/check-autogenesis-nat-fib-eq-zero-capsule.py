#!/usr/bin/env python3
"""Validate sealed exact Nat.fib_eq_zero capsule and receipt."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; C=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-exact-result-v2.json"; I=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-goal-identity-result-v1.json"; F=ROOT/"artifacts/facts/F-ml430-nat-fib-eq-zero-61879073.json"; CAPSULE=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/nat-fib-eq-zero-exact-v1/root.ndjson"); MANIFEST=CAPSULE.parent/"manifest.json"; DEPS=["Axeyum.Autogenesis.natFibEqZeroResidualV1","Axeyum.Autogenesis.natFibZeroV1","Nat.fib_pos","Nat.zero_lt_succ"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(v): return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def validate():
 c=json.loads(C.read_text()); i=json.loads(I.read_text()); f=json.loads(F.read_text()); t=i["theorem"]
 assert sha(CAPSULE)=="b25fc8b0db939ace2cbb0a096e86dd79f185398b93ff3c7698bb7b3d9fd796aa" and sha(MANIFEST)=="87b2ca1a4464715e9240ab91b538e156a5d2f6a775e3ca2620ea5cdb60745213" and stat.S_IMODE(CAPSULE.stat().st_mode)==stat.S_IMODE(MANIFEST.stat().st_mode)==0o444 and stat.S_IMODE(CAPSULE.parent.stat().st_mode)==0o555
 assert c["target"]["direct_theorem_dependencies"]==t["direct_theorem_dependencies"]==DEPS and t["axiom_footprint"]==[]
 a={"fact_id":f["id"],"formal_statement_sha256":hashlib.sha256(f["formal"]["statement"].encode()).hexdigest(),"result_manifest":"artifacts/autogenesis/mathlib-nat-fib-eq-zero-goal-identity-result-v1.json","result_manifest_sha256":sha(I),"capsule_path":str(CAPSULE),"capsule_sha256":"b25fc8b0db939ace2cbb0a096e86dd79f185398b93ff3c7698bb7b3d9fd796aa","target_theorem":"Nat.fib_eq_zero","goal_sha256":"cf9757fc1ca8af964ee54762575362e33e6c48dcf34c56381aa1e3a7a0850f4c","declaration_sha256":"9709309661cd94542db84c175fd8a68f1e5a9eba9bc616374320654050435c83","axiom_footprint":[],"direct_theorem_dependencies":DEPS,"fresh_imports":2,"fixed_plan_reconstructions":1,"target_theorem_submissions":1,"search_invocations":0,"ledger_writes":0}; return {"authority":a,"receipt_sha256":digest(a)}
def main():
 try: checked=validate(); assert checked["receipt_sha256"]=="c8466767c516d48e0e214aaf7e8a43e88a8bc7fa952a7baa2748eff03d51f3d3"
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"sealed-nat-fib-eq-zero-capsule: FAIL: {error}",file=sys.stderr); return 1
 print(f"sealed-nat-fib-eq-zero-capsule: PASS: receipt={checked['receipt_sha256']} target=Nat.fib_eq_zero footprint=0 dependencies=4"); return 0
if __name__=="__main__": raise SystemExit(main())
