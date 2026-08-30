#!/usr/bin/env python3
"""Validate the preregistered Int.fib_add foundation selection."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; PLAN=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-foundation-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  p=json.loads(PLAN.read_text()); s=p["selection"]; m=p["measured_frontier"]
  assert p["state"]=="preregistered-bottom-up-selection-before-proof-stream-access" and s["fact_id"]==p["measured_frontier"]["integer_fibonacci_candidates"][0]["fact_id"] and s["target"]=="Int.fib_add"
  assert sha(ROOT/s["fact_path"])==s["fact_file_sha256"] and sha(ROOT/p["first_measurement"]["auditor"])==p["first_measurement"]["auditor_sha256"]
  frontier=json.loads(subprocess.check_output([sys.executable,str(ROOT/"scripts/fact-frontier.py"),"--json"],cwd=ROOT))
  assert frontier["frontier_sha256"]==m["semantic_sha256"] and frontier["selection"]["admissible_fact_ids"]==m["registered_admissible_fact_ids"]
  candidates=[{"fact_id":e["fact_id"],"fact_sha256":e["fact_sha256"],"would_unlock":e["would_unlock"]} for e in frontier["entries"] if e["dependency_ready"] and e["fact_id"].startswith("F:ml430-int-fib")]
  assert candidates==m["integer_fibonacci_candidates"] and candidates[0]["would_unlock"]==m["integer_fibonacci_candidates"][0]["would_unlock"] and len(candidates[0]["would_unlock"])==1
  assert p["budget"]=={"max_remote_exporter_invocations":1,"max_batch_importer_runs":1,"max_proof_bearing_stream_reads":1,"max_retries":0,"max_reconstruction_source_compilations":0,"max_new_theorem_submissions":0,"max_fact_status_changes":0,"max_ledger_writes":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as error: print(f"autogenesis-int-fib-add-foundation-plan: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-foundation-plan: PASS: selected=Int.fib_add|unlocks=1|stream_reads=0/1|ledger_writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
