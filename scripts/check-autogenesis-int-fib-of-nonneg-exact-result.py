#!/usr/bin/env python3
"""Validate the sealed exact Int.fib_of_nonneg construction result."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-of-nonneg-exact-result-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 try:
  r=json.loads(RESULT.read_text()); p=r["plan"]; t=r["target"]; c=r["capsule"]; e=r["execution"]; path=pathlib.Path(c["path"])
  assert r["state"]=="accepted-exact-target-specialized-exported-twice-reimported-and-sealed" and sha(ROOT/p["path"])==p["sha256"]
  assert path.is_file() and sha(path)==c["sha256"] and path.stat().st_size==c["bytes"]==401185
  assert stat.S_IMODE(path.stat().st_mode)==0o444 and stat.S_IMODE(path.parent.stat().st_mode)==0o555 and c["file_mode"]=="0444" and c["directory_mode"]=="0555"
  assert t=={"name":"Int.fib_of_nonneg","declaration_sha256":"67ad588faa0778a3fa0f76890475ced5d41c575cfad76238f614dec52798aa80","axiom_footprint":[],"direct_theorem_dependencies":["Axeyum.Autogenesis.intFibOfNonnegResidualV1","Int.fib_natCast"]}
  assert e=={"clippy_compilations_before_v2":1,"binary_builds":1,"complete_invocations":1,"input_stream_reads":2,"composition_operations":1,"composition_replays":1,"specializations":1,"specialization_replays":1,"target_exports":1,"fresh_imports":2,"retries":0,"ledger_writes":0}
  assert r["fact_status_changes"]==0 and r["evaluation_credit"]==1 and r["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0}
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-of-nonneg-exact-result: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-of-nonneg-exact-result: PASS: target=Int.fib_of_nonneg|axioms=0|imports=2|writes=0"); return 0
if __name__=="__main__": raise SystemExit(main())
