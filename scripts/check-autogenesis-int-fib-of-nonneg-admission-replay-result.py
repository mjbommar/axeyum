#!/usr/bin/env python3
"""Validate isolated exact Int.fib_of_nonneg admission replay evidence."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-admission-replay-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); i=r["identities"]; s=r["semantic_checks"]; replay=pathlib.Path(r["replay_worktree"]); archive=replay.parent/"int-fib-of-nonneg-replay-archive-v1"; journal=replay.parent/"int-fib-of-nonneg-replay-journal-v1"/i["transaction_sha256"]
  assert r["state"]=="isolated-replay-byte-identical-and-semantically-accepted" and sha(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and subprocess.check_output(["git","rev-parse","HEAD"],cwd=replay,text=True).strip()==r["source_commit"]
  for name,key in [("frontier.json","frontier_file_sha256"),("execution.json","execution_file_sha256"),("transaction.json","transaction_file_sha256"),("post-frontier.json","post_frontier_file_sha256")]: assert sha(archive/name)==i[key]
  assert sha(journal/"intent.json")==i["intent_sha256"] and sha(journal/"admission-event.json")==i["admission_event_sha256"] and sha(replay/"artifacts/facts/F-ml430-int-fib-of-nonneg-438018c5.json")==i["after_fact_sha256"]
  assert s=={"selected_fact":"F:ml430-int-fib-of-nonneg-438018c5","selected_operation":"authoritative-mathlib-int-fib-of-nonneg-kernel-capsule-v1","fault_exit":75,"fact_unchanged_before_recovery":True,"recovery_executions":1,"authoritative_ledger_writes":1,"fact_status_after":"proved","proof_route_after":"kernel-lean","axiom_footprint_after":[],"fact_operation_checker_passed":True,"expected_newly_ready":[],"actual_newly_ready":[]}
  assert all(r["comparison"].values())
 except (AssertionError,OSError,ValueError,KeyError,TypeError,subprocess.CalledProcessError) as error: print(f"autogenesis-int-fib-of-nonneg-admission-replay-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-admission-replay-result: PASS: fault=75|recoveries=1|writes=1|unlocks=0"); return 0
if __name__=="__main__": raise SystemExit(main())
