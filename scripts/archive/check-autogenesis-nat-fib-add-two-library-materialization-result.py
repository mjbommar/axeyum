#!/usr/bin/env python3
"""Validate sealed reusable exact-name Nat.fib_add_two capsule."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-add-two-library-materialization-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; t=r["target"]; c=r["capsule"]; e=r["execution"]; path=pathlib.Path(c["path"])
  assert r["state"]=="accepted-reusable-exact-name-capsule-sealed" and sha(ROOT/p["path"])==p["sha256"] and sha(path)==c["sha256"] and path.stat().st_size==c["bytes"]==56115
  assert stat.S_IMODE(path.stat().st_mode)==0o444 and stat.S_IMODE(path.parent.stat().st_mode)==0o555 and c["fresh_imports"]==2
  assert t=={"name":"Nat.fib_add_two","type_sha256":"5433b34c4a138d615c488e4c7dfbee5dac8dc253e14680e114f40a55cf5eb16d","proof_sha256":"b5965831fd4654e708b03bd3145f9124f02fc57aaa04bc16ded8287b6cee50f2","declaration_sha256":"7bb254be12a9c8d97d5b2d8f51cc472c3e5eca1c0386326a1609d061a30850f3","axiom_footprint":[],"direct_theorem_dependencies":[]}
  assert e=={"clippy_compilations_before_v2":1,"binary_builds":1,"complete_invocations":1,"stream_reads":1,"fixed_reconstructions":1,"exact_name_submissions":1,"exports":1,"fresh_imports":2,"retries":0,"fact_status_changes":0,"ledger_writes":0} and r["authority"]=={"new_theorem_credit":0,"reused_admitted_theorem":1}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-add-two-library-materialization-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-add-two-library-materialization-result: PASS: target=Nat.fib_add_two|axioms=0|imports=2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
