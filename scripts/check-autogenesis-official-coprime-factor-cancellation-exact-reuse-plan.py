#!/usr/bin/env python3
"""Fail closed over the official cancellation exact-reuse plan."""

from __future__ import annotations

import hashlib
import json
import os
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PLAN = Path(os.environ.get("AXEYUM_CANCELLATION_REUSE_PLAN", ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-exact-reuse-plan-v1.json"))
REUSED = ["Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1"]
COMPOSED = ["Axeyum.Autogenesis.coprimeFactorDivisibilityCancellationResidualV2", "Axeyum.Autogenesis.dvdAddCancelAllNatAdapterV1", "Nat.dvd_add_right_cancel_of_pos"]
BUDGET = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 16, "max_composition_operations": 12, "max_specialization_operations": 10, "max_final_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0}


class OfficialCancellationExactReusePlanError(RuntimeError):
    """The exact-reuse acceptance boundary changed."""


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialCancellationExactReusePlanError("plan is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-coprime-factor-cancellation-exact-reuse-plan", "preregistered-two-leaf-exact-reuse-before-code-or-stream-access"):
        raise OfficialCancellationExactReusePlanError("plan identity changed")
    predecessor = plan["predecessor"]
    predecessor_path = ROOT / predecessor["path"]
    if hashlib.sha256(predecessor_path.read_bytes()).hexdigest() != predecessor["sha256"]:
        raise OfficialCancellationExactReusePlanError("predecessor identity changed")
    for entry in plan["accepted_inputs"].values():
        if hashlib.sha256((ROOT / entry["path"]).read_bytes()).hexdigest() != entry["sha256"]:
            raise OfficialCancellationExactReusePlanError("accepted input identity changed")
    acceptance = plan["acceptance"]
    required = {
        "fresh_complete_invocations": 2,
        "outputs_must_be_byte_identical": True,
        "all_input_streams_must_be_axiom_free": True,
        "reused_roots": REUSED,
        "each_reused_root_source_and_target_declaration_sha256_must_match": True,
        "each_reused_root_checked_compatibility_must_be_kernel_type_shape": True,
        "new_cancellation_composed_roots": COMPOSED,
        "total_composition_operations_per_invocation": 6,
        "total_specialization_operations_per_invocation": 5,
        "every_composition_and_specialization_must_replay": True,
        "final_theorem": "Axeyum.Autogenesis.officialCoprimeFactorDivisibilityCancellationV1",
        "final_axiom_footprint": [],
    }
    for key, expected in required.items():
        if acceptance.get(key) != expected:
            raise OfficialCancellationExactReusePlanError(f"acceptance changed: {key}")
    if set(REUSED) & set(COMPOSED):
        raise OfficialCancellationExactReusePlanError("a reused root is also composed")
    if plan.get("budget") != BUDGET:
        raise OfficialCancellationExactReusePlanError("budget changed")
    if any(value != 0 for value in plan["authority"].values()):
        raise OfficialCancellationExactReusePlanError("plan grants authority before execution")
    if plan["implementation"]["proof_terms_types_or_values_may_be_rendered"] is not False:
        raise OfficialCancellationExactReusePlanError("proof material may be rendered")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_EXACT_REUSE_PLAN_OK|runs=2|reuse=2|compositions=12|specializations=10|authority=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialCancellationExactReusePlanError) as error:
        print(f"autogenesis-official-cancellation-exact-reuse-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
