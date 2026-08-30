#!/usr/bin/env python3
"""Validate historical-source Nat.fib_eq_zero replay authority."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-admission-replay-plan-v2.json"; DECLINE=ROOT/"artifacts/autogenesis/mathlib-nat-fib-eq-zero-admission-replay-decline-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); d=json.loads(DECLINE.read_text()); source=p["source"]; archive=pathlib.Path(p["primary_archive"]["path"]); replay=p["replay"]; loc=d["localization"]
  assert p["state"]=="preregistered-after-preflight-decline-before-historical-source-replay" and d["attempt"]["output_created"] is False and d["attempt"]["authoritative_ledger_writes"]==0
  assert source["commit"]==loc["historical_commit"] and not pathlib.Path(source["worktree"]).exists() and source["worktree_must_not_preexist"] is True
  assert sha(archive/"frontier-before.json")==loc["retained_frontier_file_sha256"]==loc["fresh_historical_frontier_file_sha256"] and sha(pathlib.Path(loc["fresh_historical_frontier_path"]))==loc["fresh_historical_frontier_file_sha256"]
  assert replay["must_not_preexist"] is True and not pathlib.Path(replay["output"]).exists() and replay["max_driver_invocations"]==1 and replay["expected_fault_exit"]==75 and replay["authoritative_ledger_writes"]==1
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-nat-fib-eq-zero-admission-replay-plan-v2: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-nat-fib-eq-zero-admission-replay-plan-v2: PASS: driver=0/1|faults=0/1|recoveries=0/1|writes=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
