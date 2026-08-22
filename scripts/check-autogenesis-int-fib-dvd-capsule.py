#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_dvd."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; CONSTRUCTION=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-result-v22.json"; IDENTITY=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-goal-identity-result-v1.json"; FACT=ROOT/"artifacts/facts/F-ml430-int-fib-dvd-ffb3c5c1.json"; CAPSULE=pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson"); MANIFEST=CAPSULE.parent/"manifest.json"
DEPS=["Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1","Axeyum.Autogenesis.intFibNatAbsV1","Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1","Axeyum.Autogenesis.intNatAbsMulDirectV1","Eq.symm","Nat.fib_dvd"]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def validate():
 c=json.loads(CONSTRUCTION.read_text()); i=json.loads(IDENTITY.read_text()); f=json.loads(FACT.read_text()); t=i["theorem"]
 assert sha(CAPSULE)=="f684a4de870734f60f33abe1da468637697c0d27ce988a47d08dfed601ec6af0" and sha(MANIFEST)=="91ab6feee5b7c5d9ca5e81493915ce541251def6848abbe369903336568d6b86" and stat.S_IMODE(CAPSULE.stat().st_mode)==0o444 and stat.S_IMODE(CAPSULE.parent.stat().st_mode)==0o555
 assert c["state"]=="exact-target-constructed-exported-twice-reimported-and-sealed" and c["target"]["axiom_footprint"]==[] and c["target"]["direct_theorem_dependencies"]==DEPS and t["canonical_type_sha256"]=="ed84c258cad64868b6e14a1fe1cf46732aa2ca7e231defa0a627a16fae795016" and t["canonical_declaration_sha256"]=="2d4463d2a000519460bc3c7e644d2880af49c95ff9d51edcb16379ed974b22aa" and t["direct_theorem_dependencies"]==DEPS
 statement=f["formal"]["statement"]; authority={"fact_id":f["id"],"formal_statement_sha256":hashlib.sha256(statement.encode()).hexdigest(),"result_manifest":"artifacts/autogenesis/mathlib-int-fib-dvd-goal-identity-result-v1.json","result_manifest_sha256":sha(IDENTITY),"capsule_path":str(CAPSULE),"capsule_sha256":"f684a4de870734f60f33abe1da468637697c0d27ce988a47d08dfed601ec6af0","target_theorem":"Int.fib_dvd","goal_sha256":"ed84c258cad64868b6e14a1fe1cf46732aa2ca7e231defa0a627a16fae795016","declaration_sha256":"2d4463d2a000519460bc3c7e644d2880af49c95ff9d51edcb16379ed974b22aa","axiom_footprint":[],"direct_theorem_dependencies":DEPS,"fresh_imports":2,"fixed_plan_reconstructions":1,"target_theorem_submissions":1,"search_invocations":0,"ledger_writes":0}
 return {"authority":authority,"receipt_sha256":digest(authority)}
def main():
 try: receipt=validate(); assert receipt["receipt_sha256"]=="a39586b5f2cc15a7e6f6b9d2ac189035c6b81df1825ca83a5c864095bf99b897"
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"sealed-int-fib-dvd-capsule: FAIL: {error}",file=sys.stderr); return 1
 print(f"sealed-int-fib-dvd-capsule: PASS: receipt={receipt['receipt_sha256']} target=Int.fib_dvd footprint=0 dependencies=6"); return 0
if __name__=="__main__": raise SystemExit(main())
