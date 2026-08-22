#!/usr/bin/env python3
"""Validate the corrected exact Int.fib_of_nonneg execution boundary."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-exact-execution-plan-v2.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); pred=p["predecessor"]; d=p["driver"]; t=p["target"]; e=p["execution"]; o=p["outputs"]
  assert p["state"]=="preregistered-after-clippy-produced-no-runnable-binary" and sha(ROOT/pred["path"])==pred["sha256"] and pred["commit"]=="1eb7006b1a8f742eca97af00babd8de02af8990d"
  assert sha(ROOT/d["path"])==d["sha256"] and d["clippy_compilations_already_spent"]==1 and d["runnable_binary_present_before_plan"] is False and not (ROOT/e["binary"]).exists()
  fact=ROOT/t["fact_path"]; assert sha(fact)==t["fact_sha256"] and json.loads(fact.read_text())["epistemic_status"]==t["required_status"]=="open"
  for item in p["inputs"]: assert sha(pathlib.Path(item["path"]))==item["sha256"]
  assert e["binary_build_command"]==["cargo","build","-p","axeyum-lean-import","--example","int_fib_of_nonneg_exact","--all-features"] and e["max_binary_builds"]==e["max_complete_invocations"]==1 and e["max_input_stream_reads"]==e["max_fresh_imports"]==2 and e["max_retries"]==e["ledger_writes"]==0
  assert o["must_not_preexist"] is True and not pathlib.Path(o["capsule"]).exists() and not (ROOT/o["result"]).exists()
  assert p["acceptance"]=={"target_name":"Int.fib_of_nonneg","direct_theorem_dependencies":["Axeyum.Autogenesis.intFibOfNonnegResidualV1","Int.fib_natCast"],"axiom_footprint":[],"fresh_imports":2,"sealed_output":True}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-exact-execution-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-exact-execution-plan: PASS: builds=0/1|runs=0/1|reads=0/2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
