#!/usr/bin/env python3
"""Validate the Clippy-clean dependent Eq.rec motive."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-dvd-eq-rec-motive-result-v21.json"
def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); i=r["implementation"]; e=r["execution"]
  assert r["state"]=="dependent-motive-builds-clippy-clean" and sha256(ROOT/r["plan"]["path"])==r["plan"]["sha256"] and sha256(ROOT/i["path"])==i["sha256"] and i["scoped_allowances"]==1
  assert e["focused_clippy_exit_status"]==0 and e["complete_invocations"]==e["input_stream_reads"]==e["target_theorem_submissions"]==e["ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-dvd-eq-rec-motive-result-v21: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-dvd-eq-rec-motive-result-v21: PASS: clippy=0|inputs=0|targets=0"); return 0
if __name__=="__main__": raise SystemExit(main())
