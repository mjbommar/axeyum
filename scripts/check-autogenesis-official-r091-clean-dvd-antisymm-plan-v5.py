#!/usr/bin/env python3
"""Verify the post-Acc official clean-order preregistration."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-r091-clean-dvd-antisymm-plan-v5.json"
PREDECESSOR = ROOT / "artifacts/autogenesis/official-cancellation-acc-package-composition-result-v1.json"
PREDECESSOR_SHA = "fa96ec40997074828d80a0707d590bc5863fce005bf2b4e8e916abf9925e3f3d"
SUPPORTS = [
    "Axeyum.Autogenesis.eqZeroOfZeroDvdOfficialV1",
    "Axeyum.Autogenesis.leOfDvdOfficialV1",
    "Axeyum.Autogenesis.dvdAntisymmOfficialV1",
]


class PlanError(RuntimeError):
    """The proof route, budget, or zero-target authority changed."""


def load() -> dict:
    value = json.loads(PLAN.read_text())
    if not isinstance(value, dict):
        raise PlanError("plan is not an object")
    return value


def validate(plan: dict | None = None) -> dict:
    plan = load() if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (
        1,
        "axeyum-autogenesis-official-r091-clean-dvd-antisymm-plan-v5",
        "preregistered-clean-order-after-exact-acc-cancellation-composition",
    ):
        raise PlanError("plan identity changed")
    if hashlib.sha256(PREDECESSOR.read_bytes()).hexdigest() != PREDECESSOR_SHA or plan["predecessor"]["sha256"] != PREDECESSOR_SHA:
        raise PlanError("predecessor identity changed")
    if plan["construction"]["supports"] != SUPPORTS:
        raise PlanError("support set changed")
    if plan["acceptance"] != {"fresh_complete_invocations": 2, "checked_target_leaf_reuses": 2, "cancellation_compositions": 2, "support_submissions": 6, "exports": 2, "outputs_byte_identical": True, "fresh_imports_per_output": 2, "all_axiom_footprints": [], "exact_target_submissions": 0, "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}}:
        raise PlanError("acceptance boundary changed")
    if plan["budget"]["max_retries"] != 0 or plan["budget"]["max_exact_target_submissions"] != 0:
        raise PlanError("zero-retry or zero-target budget changed")
    if any(plan["authority"][key] != 0 for key in plan["authority"]):
        raise PlanError("pre-acceptance authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_R091_CLEAN_DVD_ANTISYMM_PLAN_V5_OK|runs=2|supports=3|target=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"official-r091-clean-dvd-antisymm-plan-v5: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
