#!/usr/bin/env python3
"""Validate the qualified Int.fib_eq_zero residual roots."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-eq-zero-construction-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); streams=r["streams"]; paths=[pathlib.Path(p) for p in streams["paths"]]
  assert r["state"]=="accepted-deterministic-two-root-empty-footprint-residual" and sha(ROOT/r["source"]["path"])==r["source"]["sha256"]
  assert len(r["roots"])==2 and all(not root["axiom_footprint"] for root in r["roots"]) and [root["name"] for root in r["roots"]]==["Axeyum.Autogenesis.intNatAbsEqZeroV1","Axeyum.Autogenesis.intFibEqZeroResidualV1"]
  assert all(p.stat().st_size==streams["bytes"] and sha(p)==streams["sha256"] and stat.S_IMODE(p.stat().st_mode)==0o444 for p in paths) and paths[0].read_bytes()==paths[1].read_bytes()
  audit=pathlib.Path(r["audits"]["directory"]); expected=[r["audits"]["stream_1_pass_sha256"]]*2+[r["audits"]["stream_2_pass_sha256"]]*2
  assert [sha(p) for p in sorted(audit.glob("*.json"))]==expected and r["audits"]["all_four_rows_identical"] is True
  assert r["execution"]["successful_exporter_invocations"]==2 and r["execution"]["importer_runs"]==4 and r["execution"]["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-eq-zero-construction-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-eq-zero-construction-result: PASS: roots=2|footprints=0|exports=2|imports=4|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
