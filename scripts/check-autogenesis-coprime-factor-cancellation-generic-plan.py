#!/usr/bin/env python3
"""Fail closed over the generic coprime-factor cancellation plan."""

import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = Path(os.environ.get("AXEYUM_GENERIC_CANCELLATION_PLAN", ROOT / "artifacts/autogenesis/coprime-factor-cancellation-generic-plan-v1.json"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    path = ROOT / predecessor["path"]
    require(hashlib.sha256(path.read_bytes()).hexdigest() == predecessor["sha256"], "predecessor changed")
    require(plan["state"] == "preregistered-balanced-Bezout-parameterized-cancellation-before-source", "state changed")
    construction = plan["construction"]
    require(construction["target"] == "Axeyum.Autogenesis.coprimeFactorDivisibilityCancellationGenericV1", "target changed")
    require(construction["contract"].startswith("(forall a c, BalancedBezoutUpdateV2"), "balanced Bezout is not an explicit parameter")
    require(construction["proof_search_allowed"] is False, "proof search allowed")
    require(construction["upstream_proof_body_reads_allowed"] is False, "upstream proof reads allowed")
    require(construction["proof_terms_types_or_values_may_be_rendered"] is False, "proof material may be rendered")
    acceptance = plan["acceptance"]
    require(acceptance["fresh_kernel_imports_required"] == 2 and acceptance["audits_must_be_byte_identical"] is True, "two deterministic imports not required")
    require(acceptance["axiom_footprint_must_be_empty"] is True, "empty footprint not required")
    require(acceptance["balanced_Bezout_must_be_an_explicit_parameter"] is True, "certificate parameter not required")
    require(plan["budget"] == {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_generic_cancellation_submissions": 1, "max_official_specializations": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}, "budget changed")
    require(all(value == 0 for value in plan["authority"].values()), "plan grants authority")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_GENERIC_PLAN_OK|compile=1|imports=2|specializations=0|authority=0")


if __name__ == "__main__":
    main()
