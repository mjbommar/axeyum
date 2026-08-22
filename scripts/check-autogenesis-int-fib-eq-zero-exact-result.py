#!/usr/bin/env python3
"""Validate the sealed exact Int.fib_eq_zero construction."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-exact-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); c=r["capsule"]; p=pathlib.Path(c["path"]); raw=pathlib.Path(r["raw_execution_result"]["path"]); target=r["target"]
  assert r["state"]=="accepted-exact-target-specialized-exported-twice-reimported-and-sealed" and sha(ROOT/r["producer"]["path"])==r["producer"]["sha256"]
  assert p.stat().st_size==c["bytes"] and sha(p)==c["sha256"] and stat.S_IMODE(p.stat().st_mode)==0o444 and stat.S_IMODE(p.parent.stat().st_mode)==0o555
  assert sha(raw)==r["raw_execution_result"]["sha256"] and not target["axiom_footprint"] and len(target["direct_theorem_dependencies"])==4
  assert r["execution"]=={"complete_invocations":1,"input_stream_reads":3,"composition_operations":2,"composition_replays":2,"specializations":1,"specialization_replays":1,"target_exports":1,"fresh_imports":2,"retries":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-exact-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-exact-result: PASS: target=Int.fib_eq_zero|footprint=0|dependencies=4|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
