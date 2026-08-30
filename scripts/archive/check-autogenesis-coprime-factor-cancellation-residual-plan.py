#!/usr/bin/env python3
"""Check the residual cancellation preregistration."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-residual-plan-v1.json"


def main() -> None:
    plan = json.loads(PLAN.read_text())
    for row in plan["predecessors"].values():
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]
    assert plan["state"] == "preregistered-residual-cancellation-before-source"
    assert plan["explicit_parameters"] == ["balancedBezout", "rightDistrib", "dvdAddCancel"]
    assert len(plan["target_owned_support"]) == 2
    assert set(plan["eliminated_carriers"]) == {"Nat.dvd_add", "Nat.dvd_add_iff_right", "Nat.dvd_mul_right_of_dvd", "Nat.mul_left_comm", "Nat.right_distrib", "eq_self"}
    assert plan["acceptance"]["fresh_kernel_imports_required"] == 2
    assert plan["acceptance"]["all_three_axiom_footprints_must_be_empty"] is True
    assert plan["budget"]["max_retries"] == 0 and plan["budget"]["max_official_specializations"] == 0
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_RESIDUAL_PLAN_OK|support=2|parameters=3|imports=2|authority=0")


if __name__ == "__main__":
    main()
