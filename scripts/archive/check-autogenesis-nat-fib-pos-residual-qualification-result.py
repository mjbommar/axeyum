#!/usr/bin/env python3
"""Validate accepted Nat.fib_pos residual closure qualification."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-residual-qualification-result-v3.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); t=r["theorem"]; s=r["streams"]
  assert r["state"]=="qualified-exact-clean-equality-closure-without-rerun" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and t["axiom_footprint"]==[] and t["direct_theorem_dependencies"]==["Eq.symm","congrArg"]
  paths=[pathlib.Path(x) for x in s["paths"]]; assert len(paths)==2 and all(sha(x)==s["sha256"] and x.stat().st_size==s["bytes"] and stat.S_IMODE(x.stat().st_mode)==0o444 for x in paths) and stat.S_IMODE(paths[0].parent.stat().st_mode)==0o555 and s["completed_imports"]==2 and s["byte_identical"] is s["sealed"] is True
  assert r["execution"]=={"exporter_invocations":0,"importer_runs":0,"stream_reads":0,"theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0} and r["authority"]=={"residual_qualified":1,"target_credit":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-residual-qualification-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-residual-qualification-result: PASS: dependencies=2|axioms=0|reruns=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
