#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Nat.fib_pos."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; CONSTRUCTION=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-exact-result-v14.json"; IDENTITY=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-goal-identity-result-v1.json"; FACT=ROOT/"artifacts/facts/F-ml430-nat-fib-pos-9e67bd8e.json"; CAPSULE=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/nat-fib-pos-exact-v1/root.ndjson"); MANIFEST=CAPSULE.parent/"manifest.json"
DEPS=["Axeyum.Autogenesis.natFibOnePositiveV1","Axeyum.Autogenesis.natFibPosResidualV1","Axeyum.Autogenesis.natFibStepPositiveV1","Axeyum.Autogenesis.natFibZeroV1","Nat.zero_lt_succ"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def validate():
 c=json.loads(CONSTRUCTION.read_text()); i=json.loads(IDENTITY.read_text()); f=json.loads(FACT.read_text()); t=i["theorem"]
 assert sha(CAPSULE)=="ec85c45183bec3c1fe4cbd0d015c76a5ded6dbbfa4be9b279d59870da12566a0" and sha(MANIFEST)=="b36acb8397d0c66b2716380cee08ac80b22b26876d812b9d41007c26fb934c4c" and stat.S_IMODE(CAPSULE.stat().st_mode)==0o444 and stat.S_IMODE(MANIFEST.stat().st_mode)==0o444 and stat.S_IMODE(CAPSULE.parent.stat().st_mode)==0o555
 assert c["state"]=="exact-target-specialized-exported-and-twice-reimported-empty-footprint" and c["target"]["axiom_footprint"]==[] and c["target"]["direct_theorem_dependencies"]==DEPS and t["canonical_type_sha256"]=="24233cf6ebabcb044ad6fa8be564c7cfbff822a421afb1c94ff906c65d029f56" and t["canonical_declaration_sha256"]=="f441b137a185604cee38d4f5c311cd48cd83ffb4279ceab467c7852dad326e65" and t["direct_theorem_dependencies"]==DEPS
 statement=f["formal"]["statement"]; authority={"fact_id":f["id"],"formal_statement_sha256":hashlib.sha256(statement.encode()).hexdigest(),"result_manifest":"artifacts/autogenesis/mathlib-nat-fib-pos-goal-identity-result-v1.json","result_manifest_sha256":sha(IDENTITY),"capsule_path":str(CAPSULE),"capsule_sha256":"ec85c45183bec3c1fe4cbd0d015c76a5ded6dbbfa4be9b279d59870da12566a0","target_theorem":"Nat.fib_pos","goal_sha256":"24233cf6ebabcb044ad6fa8be564c7cfbff822a421afb1c94ff906c65d029f56","declaration_sha256":"f441b137a185604cee38d4f5c311cd48cd83ffb4279ceab467c7852dad326e65","axiom_footprint":[],"direct_theorem_dependencies":DEPS,"fresh_imports":2,"fixed_plan_reconstructions":1,"target_theorem_submissions":1,"search_invocations":0,"ledger_writes":0}
 return {"authority":authority,"receipt_sha256":digest(authority)}
def main():
 try: receipt=validate(); assert receipt["receipt_sha256"]=="60954cc8fbe7d947c08ffca5dbc55e600864151ca5a824c3d950614478c46aff"
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"sealed-nat-fib-pos-capsule: FAIL: {error}",file=sys.stderr); return 1
 print(f"sealed-nat-fib-pos-capsule: PASS: receipt={receipt['receipt_sha256']} target=Nat.fib_pos footprint=0 dependencies=5"); return 0
if __name__=="__main__": raise SystemExit(main())
