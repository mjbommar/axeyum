#!/usr/bin/env python3
"""Validate bounded core support export for Nat.fib_pos."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-pos-core-support-plan-v4.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; e=p["environment"]; c=p["command"]; b=p["budget"]
  assert p["state"]=="preregistered-before-bounded-core-root-export" and sha(ROOT/pred["path"])==pred["sha256"] and json.loads((ROOT/"artifacts/facts/F-ml430-nat-fib-pos-9e67bd8e.json").read_text())["epistemic_status"]==p["target"]["required_status"]=="open"
  assert [r["name"] for r in p["roots"]]==["Nat.zero_lt_succ","Nat.add_pos_right"] and p["forbidden_roots"]==["Nat.fib","Nat.fib_pos","Nat.fib_eq_zero"] and e["module"]=="Init.Prelude" and e["lean_version"]=="4.30.0" and e["lean4export_binary_sha256"]=="8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
  assert c["output_must_not_preexist"] is True and not pathlib.Path(c["output"]).exists() and b=={"max_exporter_invocations":1,"max_root_stream_writes":1,"max_importer_runs":2,"max_retries":0,"target_theorem_submissions":0,"fact_status_changes":0,"ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-pos-core-support-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-pos-core-support-plan: PASS: exporters=0/1|imports=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
