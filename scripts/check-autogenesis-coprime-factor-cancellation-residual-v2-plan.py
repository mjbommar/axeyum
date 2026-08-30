#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-residual-v2-plan-v1.json"

def main() -> None:
    plan = json.loads(PLAN.read_text())
    for key in ["predecessor", "accepted_clean_leaf"]:
        row = plan[key]
        assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]
    assert plan["state"] == "preregistered-mul-assoc-parameterization-before-source"
    assert plan["explicit_parameters"] == ["balancedBezout", "mulAssoc", "rightDistrib", "dvdAddCancel"]
    assert plan["acceptance"]["fresh_kernel_imports_required"] == 2 and plan["acceptance"]["all_three_axiom_footprints_must_be_empty"] is True
    assert plan["budget"]["max_retries"] == 0 and plan["budget"]["max_official_specializations"] == 0
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_RESIDUAL_V2_PLAN_OK|parameters=4|roots=3|imports=2|authority=0")

if __name__ == "__main__":
    main()
