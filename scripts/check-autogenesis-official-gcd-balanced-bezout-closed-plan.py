#!/usr/bin/env python3
"""Verify the frozen dependency-bound closed gcd/Bézout specialization plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-closed-plan-v1.json"
GENERIC_RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-clean-result-v1.json"
GENERIC_RESULT_SHA256 = "dd483ff460fb1ae7ef8038ef6eb214cd931d6a60bbb83e8330bd9c90a3b1290d"
STREAMS = {
    "generic_stream": "c106a1e03a329535042f17f6a9d3cf408361e4b4691b5ea6bac4d1a71186bb56",
    "mod_invariant_stream": "5d945b100f3e2939d6ea3ffa67e10b4d78ff9efb7782a56f3d67468aa167ebf9",
    "target_stream": "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd",
    "gcd_bridge_stream": "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db",
}
ARGUMENTS = [
    {"name": "Nat.gcd_zero_left", "declaration_sha256": "f81aee8a1d8528ddf8b7be6007efbee190f2208cdef3dcfda9fa03a1f200175d"},
    {"name": "Nat.gcd_succ", "declaration_sha256": "e41996f98e01e15b88e11773bb42db825bf271888ece2d002c193627a8392727"},
]


class OfficialGcdBalancedBezoutClosedPlanError(RuntimeError):
    """The inputs, dependency identities, budget, or zero authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutClosedPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-closed-plan", "preregistered-dependency-bound-specialization-before-code-or-execution-no-closed-credit"):
        raise OfficialGcdBalancedBezoutClosedPlanError("plan identity changed")
    if sha256(GENERIC_RESULT) != GENERIC_RESULT_SHA256 or plan.get("inputs", {}).get("generic_result", {}).get("sha256") != GENERIC_RESULT_SHA256:
        raise OfficialGcdBalancedBezoutClosedPlanError("generic result identity changed")
    for key, expected in STREAMS.items():
        row = plan.get("inputs", {}).get(key, {})
        path = pathlib.Path(row.get("path", ""))
        if row.get("sha256") != expected or sha256(path) != expected:
            raise OfficialGcdBalancedBezoutClosedPlanError(f"{key} identity changed")
    implementation = plan.get("implementation", {})
    if implementation.get("new_mode") != "--closed-balanced-bezout" or implementation.get("arguments") != ARGUMENTS or implementation.get("target") != "Axeyum.Autogenesis.officialGcdBalancedBezoutClosedV1" or implementation.get("proof_rendering_allowed") is not False:
        raise OfficialGcdBalancedBezoutClosedPlanError("specialization boundary changed")
    acceptance = plan.get("acceptance", {})
    expected_dependencies = ["Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1", "Nat.gcd_succ", "Nat.gcd_zero_left"]
    if acceptance.get("fresh_complete_invocations") != 2 or acceptance.get("target_axiom_footprint") != [] or acceptance.get("required_direct_theorem_dependencies") != expected_dependencies or acceptance.get("proof_terms_types_or_values_may_be_rendered") is not False:
        raise OfficialGcdBalancedBezoutClosedPlanError("acceptance contract changed")
    budget = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 8, "max_specialization_operations": 8, "max_new_closed_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdBalancedBezoutClosedPlanError("budget changed")
    if any(value != 0 for value in plan.get("authority", {}).values()):
        raise OfficialGcdBalancedBezoutClosedPlanError("pre-execution authority must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_CLOSED_PLAN_OK|invocations=2|stream_reads<=8|specializations<=8|closed_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutClosedPlanError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-closed-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
