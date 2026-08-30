#!/usr/bin/env python3
"""Check the self-contained generic cancellation preregistration."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-self-contained-plan-v1.json"


def require(value: bool, message: str) -> None:
    if not value:
        raise SystemExit(message)


def main() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    require(hashlib.sha256((ROOT / predecessor["path"]).read_bytes()).hexdigest() == predecessor["sha256"], "predecessor changed")
    require(plan["state"] == "preregistered-self-contained-certificate-definition-before-source-change", "state changed")
    source = plan["source"]
    require(source["only_import"] == "Mathlib.Data.Int.GCD", "import surface changed")
    require(source["inlined_definition"] == "BalancedBezoutCancellationV2", "definition changed")
    require(source["proof_argument_unchanged_from_v1"] is True, "proof argument may change")
    require(source["proof_search_allowed"] is False and source["proof_terms_types_or_values_may_be_rendered"] is False, "proof policy changed")
    require(plan["acceptance"]["fresh_kernel_imports_required"] == 2 and plan["acceptance"]["axiom_footprint_must_be_empty"] is True, "acceptance weakened")
    require(plan["budget"]["max_retries"] == 0 and plan["budget"]["max_official_specializations"] == 0, "budget weakened")
    require(all(value == 0 for value in plan["authority"].values()), "plan grants authority")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_SELF_CONTAINED_PLAN_OK|compile=1|imports=2|authority=0")


if __name__ == "__main__":
    main()
