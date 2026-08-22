#!/usr/bin/env python3
"""Validate the sealed Int.fib_add root audit and its next bounded plan."""
import hashlib,json,pathlib,stat,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; RESULT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-root-audit-result-v1.json"; NEXT=ROOT/"artifacts/autogenesis/mathlib-int-fib-add-dependency-audit-plan-v1.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def mode(path): return stat.S_IMODE(path.stat().st_mode)
def main():
 try:
  r=json.loads(RESULT.read_text()); p=json.loads(NEXT.read_text()); pack=pathlib.Path(r["pack"]["path"]); audit=json.loads((pack/"audit.json").read_text()); target=r["target"]
  assert r["state"]=="official-root-assumption-bearing-five-direct-theorem-boundary" and sha(pack/"manifest.json")==r["pack"]["manifest_sha256"] and sha(pack/"int-fib-add.ndjson")==r["pack"]["stream"]["sha256"] and sha(pack/"audit.json")==r["pack"]["audit_sha256"]
  assert [mode(pack/name) for name in ["int-fib-add.ndjson","audit.json","manifest.json"]]==[0o444,0o444,0o444] and mode(pack)==0o555
  assert audit["rows"]==[{"axiom_footprint":target["axiom_footprint"],"class":target["class"],"declaration_sha256":target["declaration_sha256"],"direct_theorem_dependencies":target["direct_theorem_dependencies"],"name":target["name"]}] and audit["rendered_material"]=={"proof_terms":0,"theorem_types":0,"theorem_values":0}
  assert r["decision"]["compose_official_root"] is False and p["ordered_roots"]==target["direct_theorem_dependencies"] and p["input"]["sha256"]==r["pack"]["stream"]["sha256"] and p["measurement"]["output_must_not_preexist"] is True
  assert sha(ROOT/p["measurement"]["tool"])==p["measurement"]["tool_sha256"] and p["budget"]["max_batch_importer_runs"]==1 and p["budget"]["max_ledger_writes"]==0
 except (AssertionError,OSError,ValueError,KeyError,TypeError) as error: print(f"autogenesis-int-fib-add-root-audit: FAIL: {error}",file=sys.stderr); return 1
 print("autogenesis-int-fib-add-root-audit: PASS: official=propext-bearing|direct=5|rendered=0|next_reads=0/1"); return 0
if __name__=="__main__": raise SystemExit(main())
