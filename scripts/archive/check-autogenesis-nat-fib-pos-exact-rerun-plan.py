#!/usr/bin/env python3
"""Validate the corrected exact Nat.fib_pos rerun plan."""
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-pos-exact-rerun-plan-v11.json"
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    try:
        p=json.loads(PLAN.read_text()); pred=p["predecessor"]; driver=p["driver"]
        assert p["state"]=="preregistered-after-corrected-driver-compile-before-rerun"
        assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()==p["source_commit"]
        assert sha(ROOT/pred["path"])==pred["sha256"] and sha(ROOT/driver["path"])==driver["sha256"]
        for item in p["inputs"]: assert sha(pathlib.Path(item["path"]))==item["sha256"]
        assert not pathlib.Path(p["output"]["path"]).exists() and not (ROOT/p["result"]["path"]).exists()
        assert p["execution"]["ledger_writes"]==0 and p["execution"]["max_complete_invocations"]==1
    except (AssertionError,KeyError,OSError,TypeError,ValueError,subprocess.CalledProcessError) as error:
        print(f"autogenesis-nat-fib-pos-exact-rerun-plan: FAIL: {error}",file=sys.stderr); return 1
    print("autogenesis-nat-fib-pos-exact-rerun-plan: PASS: builds=0/1|runs=0/1|reads=0/4|ledger=0"); return 0
if __name__=="__main__": raise SystemExit(main())
