#!/usr/bin/env python3
"""Validate the exact Nat.fib_pos binary-build and execution plan."""
import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-pos-exact-execution-plan-v9.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    try:
        plan = json.loads(PLAN.read_text())
        predecessor = plan["predecessor"]
        driver = plan["driver"]
        assert plan["state"] == "preregistered-after-driver-compile-before-proof-stream-read"
        assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip() == plan["source_commit"]
        assert sha(ROOT / predecessor["path"]) == predecessor["sha256"]
        assert sha(ROOT / driver["path"]) == driver["sha256"]
        assert driver["focused_clippy"] == "pass" and driver["runnable_binary_after_clippy"] is False
        for item in plan["inputs"]:
            assert sha(pathlib.Path(item["path"])) == item["sha256"]
        assert plan["output"]["must_not_preexist"] is True
        assert not pathlib.Path(plan["output"]["path"]).exists()
        assert plan["result"]["must_not_preexist"] is True
        assert not (ROOT / plan["result"]["path"]).exists()
        assert plan["execution"] == {"max_binary_builds": 1, "max_complete_invocations": 1, "max_input_stream_reads": 4, "max_composition_operations": 3, "max_composition_replays": 3, "max_support_theorem_submissions": 2, "max_specializations": 2, "max_specialization_replays": 2, "max_target_exports": 1, "max_fresh_imports": 2, "max_retries": 0, "fact_status_changes": 0, "ledger_writes": 0}
    except (AssertionError, KeyError, OSError, TypeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"autogenesis-nat-fib-pos-exact-execution-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-nat-fib-pos-exact-execution-plan: PASS: builds=0/1|runs=0/1|reads=0/4|ledger=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
