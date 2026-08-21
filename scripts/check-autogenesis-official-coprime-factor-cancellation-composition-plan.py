#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-composition-plan-v1.json"

def main() -> None:
    plan = json.loads(PLAN.read_text())
    for row in plan["accepted_inputs"].values():
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]
    assert plan["state"] == "preregistered-eight-stream-native-leaf-composition-before-code"
    assert plan["composition"]["native_root"] == "Nat.dvd_add_right_cancel_of_pos"
    assert len(plan["composition"]["stream_roots"]) == 4
    assert plan["acceptance"]["fresh_complete_invocations"] == 2 and plan["acceptance"]["final_axiom_footprint"] == []
    assert plan["budget"] == {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 16, "max_composition_operations": 14, "max_specialization_operations": 10, "max_final_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0}
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_OFFICIAL_COPRIME_FACTOR_CANCELLATION_COMPOSITION_PLAN_OK|streams=8|runs=2|final=0")

if __name__ == "__main__":
    main()
