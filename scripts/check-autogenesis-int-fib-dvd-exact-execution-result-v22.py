#!/usr/bin/env python3
"""Validate the sealed exact Int.fib_dvd construction."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-result-v22.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); ev=r["evidence"]; target=r["target"]; execution=r["execution"]; pack=pathlib.Path(ev["pack"])
  assert r["state"]=="exact-target-constructed-exported-twice-reimported-and-sealed" and sha256(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha256(ROOT/r["implementation"]["path"])==r["implementation"]["sha256"]
  assert sha256(pack/"manifest.json")==ev["manifest_sha256"] and sha256(pack/"root.ndjson")==ev["capsule_sha256"] and stat.S_IMODE(pack.stat().st_mode)==0o555 and all(stat.S_IMODE(p.stat().st_mode)==0o444 for p in pack.iterdir())
  assert target["name"]=="Int.fib_dvd" and target["axiom_footprint"]==[] and len(target["direct_theorem_dependencies"])==6
  assert execution["link_checks_passed"]==5 and execution["target_theorem_submissions"]==1 and execution["fresh_target_imports"]==2 and execution["ledger_writes"]==0 and r["authority"]["target_credit"]==1
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-exact-execution-result-v22: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-exact-execution-result-v22: PASS: links=5|axioms=0|dependencies=6|sealed=true|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
