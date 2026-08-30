#!/usr/bin/env python3
"""Validate the scoped Eq.rec transport lint allowance."""
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-eq-rec-motive-plan-v21.json"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def main() -> int:
    try:
        plan=json.loads(PLAN.read_text()); pred=plan["predecessor"]; execution=plan["execution"]
        assert plan["state"]=="preregistered-scoped-argument-count-allowance" and sha256(ROOT/pred["path"])==pred["sha256"]
        assert plan["correction"]["only_change"]=="add #[allow(clippy::too_many_arguments)] to eq_rec_transport" and plan["correction"]["proof_change"]=="none"
        assert execution=={"max_driver_builds":1,"max_complete_invocations":0,"max_input_stream_reads":0,"max_target_theorem_submissions":0,"max_retries":0,"ledger_writes":0}
    except (AssertionError,OSError,ValueError,KeyError,TypeError) as error:
        print(f"autogenesis-int-fib-dvd-eq-rec-motive-plan-v21: FAIL: {error}",file=sys.stderr); return 1
    print("autogenesis-int-fib-dvd-eq-rec-motive-plan-v21: PASS: allowance=1|builds=0/1|inputs=0|targets=0"); return 0
if __name__=="__main__": raise SystemExit(main())
