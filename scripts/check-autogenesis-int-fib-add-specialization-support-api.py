#!/usr/bin/env python3
"""Validate the bounded failed API query and constructive induction fallback."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-specialization-support-api-result-v1.json"; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-induction-adapter-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(PLAN.read_text()); out=pathlib.Path(r["query"]["output"])
  assert r["state"]=="public-induction-constant-absent-constructive-fallback-selected" and sha(out)==r["query"]["sha256"] and out.read_text().strip().endswith("Unknown constant `Int.inductionOn`")
  assert stat.S_IMODE(out.stat().st_mode)==0o444 and stat.S_IMODE(out.parent.stat().st_mode)==0o555 and r["execution"]["compiler_invocations"]==1 and r["execution"]["public_types_rendered"]==0 and r["execution"]["proof_bearing_stream_reads"]==0
  assert r["decision"]["issue_another_api_query"] is False and p["target"]["name"]=="Axeyum.Autogenesis.intSuccPredInductionResidualV1" and "Int.inductionOn" in p["target"]["forbidden_names"]
  assert p["budget"]["max_source_compilations"]==1 and p["budget"]["max_exports"]==0 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-specialization-support-api: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-specialization-support-api: PASS: query=1/1|outcome=absent|next=Nat.rec-adapter|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
