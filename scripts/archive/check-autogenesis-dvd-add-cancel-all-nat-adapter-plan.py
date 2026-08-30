#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/dvd-add-cancel-all-nat-adapter-plan-v1.json"

def main() -> None:
    plan = json.loads(PLAN.read_text())
    row = plan["predecessor"]
    assert hashlib.sha256((ROOT / row["path"]).read_bytes()).hexdigest() == row["sha256"]
    assert plan["state"] == "preregistered-zero-successor-adapter-before-source"
    assert plan["acceptance"]["fresh_kernel_imports_required"] == 2 and plan["acceptance"]["axiom_footprint_must_be_empty"] is True
    assert plan["acceptance"]["positive_cancellation_must_remain_an_explicit_parameter"] is True
    assert plan["budget"]["max_retries"] == 0 and plan["budget"]["max_positive_leaf_submissions"] == 0
    assert all(value == 0 for value in plan["authority"].values())
    print("AUTOGENESIS_DVD_ADD_CANCEL_ALL_NAT_ADAPTER_PLAN_OK|cases=2|imports=2|positive=parameter|authority=0")

if __name__ == "__main__":
    main()
