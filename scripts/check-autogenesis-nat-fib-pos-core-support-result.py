#!/usr/bin/env python3
"""Validate sealed core positivity supports for Nat.fib_pos."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-core-support-result-v4.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); c=r["capsule"]; path=pathlib.Path(c["path"]); roots=r["roots"]
  assert r["state"]=="accepted-two-core-roots-twice-imported-and-sealed" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha(path)==c["sha256"] and path.stat().st_size==c["bytes"]==124573 and c["fresh_imports"]==2 and stat.S_IMODE(path.stat().st_mode)==0o444 and stat.S_IMODE(path.parent.stat().st_mode)==0o555
  assert [x["name"] for x in roots]==["Nat.zero_lt_succ","Nat.add_pos_right"] and all(x["axiom_footprint"]==[] for x in roots) and r["execution"]=={"exporter_invocations":1,"root_stream_writes":1,"importer_runs":2,"retries":0,"target_theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0} and r["authority"]=={"support_roots_qualified":2,"target_credit":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-core-support-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-core-support-result: PASS: roots=2|axioms=0|imports=2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
