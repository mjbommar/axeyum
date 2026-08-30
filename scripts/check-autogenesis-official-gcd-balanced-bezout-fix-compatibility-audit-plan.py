#!/usr/bin/env python3
"""Verify the frozen proof-free WellFounded.fix compatibility audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-fix-compatibility-audit-plan-v1.json"
DECLINE = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-closed-result-v1.json"
DECLINE_SHA256 = "dc00dca67dd4ff6962cfe6a78de560356352303c8e8ad938380c4fc555af2f1a"
STREAMS = {
    "generic_stream": "c106a1e03a329535042f17f6a9d3cf408361e4b4691b5ea6bac4d1a71186bb56",
    "mod_invariant_stream": "5d945b100f3e2939d6ea3ffa67e10b4d78ff9efb7782a56f3d67468aa167ebf9",
    "target_stream": "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd",
    "gcd_bridge_stream": "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db",
}


class OfficialGcdBalancedBezoutFixAuditPlanError(RuntimeError):
    """The inputs, structural-only scope, budget, or zero authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutFixAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-plan", "preregistered-proof-free-well-founded-fix-closure-audit-before-code-or-stream-read"):
        raise OfficialGcdBalancedBezoutFixAuditPlanError("plan identity changed")
    if sha256(DECLINE) != DECLINE_SHA256 or plan.get("inputs", {}).get("decline_result", {}).get("sha256") != DECLINE_SHA256:
        raise OfficialGcdBalancedBezoutFixAuditPlanError("decline identity changed")
    for key, expected in STREAMS.items():
        row = plan.get("inputs", {}).get(key, {})
        if row.get("sha256") != expected or sha256(pathlib.Path(row.get("path", ""))) != expected:
            raise OfficialGcdBalancedBezoutFixAuditPlanError(f"{key} identity changed")
    implementation = plan.get("implementation", {})
    if implementation.get("new_mode") != "--audit-balanced-bezout-fix" or implementation.get("root") != "WellFounded.fix" or implementation.get("forbidden_rendered_fields") != ["proof terms", "theorem types", "definition values", "theorem values"]:
        raise OfficialGcdBalancedBezoutFixAuditPlanError("audit scope changed")
    acceptance = plan.get("acceptance", {})
    if acceptance.get("fresh_complete_invocations") != 2 or acceptance.get("root_source_type_shape_sha256") != "f45b230503d6ddc03c61714008f6165dd055ff995d927507fc6d7aaffcf6afd6" or acceptance.get("root_target_type_shape_sha256") != "0c2e9552a1056133fbd4e6a318344cfb1310468f7d2113efb37ebba0bf6ef32c" or acceptance.get("proof_terms_types_or_values_may_be_rendered") is not False or acceptance.get("transport_or_reconstruction_may_be_authorized") is not False:
        raise OfficialGcdBalancedBezoutFixAuditPlanError("acceptance boundary changed")
    budget = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 8, "max_intermediate_specialization_operations": 6, "max_closure_union_names": 512, "max_closed_theorem_submissions": 0, "max_retries": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdBalancedBezoutFixAuditPlanError("budget changed")
    if any(value != 0 for value in plan.get("authority", {}).values()):
        raise OfficialGcdBalancedBezoutFixAuditPlanError("audit authority must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_FIX_AUDIT_PLAN_OK|root=WellFounded.fix|invocations=2|stream_reads<=8|theorem_submissions=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutFixAuditPlanError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-fix-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
