#!/usr/bin/env python3
"""Verify the exact official Acc package composition preregistration."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-cancellation-acc-package-composition-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/official-cancellation-acc-path-audit-result-v1.json"
RESULT_SHA = "f7210223e7de17764a09c8311fb4349d584216e2a90f9c00993947470ef163f7"
PACKAGE = {
    "Acc": "ae8b799311c1ef25f167d7413eb10abf55df398053cf994f953bd31624f96e27",
    "Acc.intro": "73c42b8287c3b2b680731deb89003732efda90b571c0dd737a81cbcf2ef024c2",
    "Acc.rec": "67cc978e963fa24e78a117380175be35753a051986230e1c5f2fd2b3a2df85ac",
}


class CompositionPlanError(RuntimeError):
    """The bounded package authorization changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CompositionPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (
        1,
        "axeyum-autogenesis-official-cancellation-acc-package-composition-plan",
        "preregistered-declaration-exact-official-acc-package-before-code-or-composition",
    ):
        raise CompositionPlanError("plan identity changed")
    if hashlib.sha256(RESULT.read_bytes()).hexdigest() != RESULT_SHA or plan["inputs"]["path_audit_result"]["sha256"] != RESULT_SHA:
        raise CompositionPlanError("audit result identity changed")
    package = plan["authorized_recursive_package"]
    if [package["family"], package["constructor"], package["recursor"]] != list(PACKAGE):
        raise CompositionPlanError("package names changed")
    if package["exact_source_declaration_sha256"] != PACKAGE:
        raise CompositionPlanError("package declaration identities changed")
    required = set(plan["implementation"]["required_controls"])
    if len(required) != 5 or not any("mutation" in item for item in required):
        raise CompositionPlanError("required controls changed")
    execution = plan["execution"]
    if execution != {"complete_invocations": 2, "source_reads": 2, "target_reads": 2, "cancellation_compositions": 2, "clean_order_submissions": 0, "exact_target_submissions": 0, "retries": 0}:
        raise CompositionPlanError("execution budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]):
        raise CompositionPlanError("pre-acceptance authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_ACC_PACKAGE_PLAN_OK|package=Acc+intro+rec|runs=2|target_submissions=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CompositionPlanError) as error:
        print(f"official-cancellation-acc-package-composition-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
