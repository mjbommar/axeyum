#!/usr/bin/env python3
"""Validate hash-only qualification of congrArg-only step residual."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-step-positive-residual-qualification-plan-v6.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; q=p["qualified_observation"]
  assert p["state"]=="preregistered-hash-only-after-two-clean-imports" and sha(ROOT/pred["path"])==pred["sha256"] and q["axiom_footprint"]==[] and q["direct_theorem_dependencies"]==["congrArg"] and q["completed_imports"]==2
  prior=json.loads((ROOT/pred["path"]).read_text()); assert prior["theorem"]["canonical_declaration_sha256"]==q["canonical_declaration_sha256"] and prior["streams"]["sha256"]==q["stream_sha256"] and prior["streams"]["byte_identical"] is prior["streams"]["sealed"] is True
  assert p["execution"]=={"exporter_invocations":0,"importer_runs":0,"stream_reads":0,"theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0} and all(p["acceptance"].values())
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-step-positive-residual-qualification-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-step-positive-residual-qualification-plan: PASS: reads=0|imports=0|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
