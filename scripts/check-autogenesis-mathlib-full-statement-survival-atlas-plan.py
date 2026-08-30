#!/usr/bin/env python3
"""Verify the full Mathlib statement-survival atlas plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-full-statement-survival-atlas-plan-v1.json"


class PlanError(RuntimeError):
    """The atlas input, unknown boundary, budget, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind") != "axeyum-autogenesis-full-statement-survival-atlas-plan"
        or plan.get("state")
        != "post-name-observation-preregistered-before-structural-comparison"
        or plan.get("policy_version") != "mathlib-full-nat-int-statement-survival-v1"
    ):
        raise PlanError("plan identity changed")
    for key, expected in {
        "baseline_inventory": (9729, "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"),
        "current_inventory": (9822, "22246f40ae5a9b7f44a914313a5a212104b541d48974df4bf439da4006e61e5e"),
    }.items():
        row = plan["inputs"][key]
        path = pathlib.Path(row["path"])
        if (
            row.get("records") != expected[0]
            or row.get("sha256") != expected[1]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or sha256(path) != expected[1]
        ):
            raise PlanError(f"{key} changed or is mutable")
    selected = plan["inputs"]["selected_comparison"]
    if (
        selected.get("sha256")
        != "9174c2fa642a60c59bb48df5a4741103d7e98e599c13922756ba077975d0ad28"
        or sha256(ROOT / selected["path"]) != selected["sha256"]
    ):
        raise PlanError("selected comparison identity changed")
    if plan.get("observed_before_plan") != {
        "shared_names": 9712,
        "removed_names": 17,
        "added_names": 110,
        "structural_class_counts_observed": False,
    }:
        raise PlanError("observed name boundary changed")
    fixed = plan["fixed_comparison"]
    if (
        len(fixed.get("shared_row_classes", [])) != 4
        or fixed.get("unshared_row_classes")
        != ["removed-after-v4.30.0", "added-by-v4.32.1"]
        or len(fixed.get("aggregates", [])) != 4
    ):
        raise PlanError("fixed structural comparison changed")
    if plan["budget"] != {
        "max_full_structural_comparisons": 1,
        "max_inventory_extractions": 0,
        "max_policy_adaptations": 0,
        "max_proof_search_invocations": 0,
        "max_kernel_theorem_submissions": 0,
        "max_executor_invocations": 0,
        "max_retries": 0,
    }:
        raise PlanError("atlas budget changed")
    if plan["gates"] != {
        "every_union_name_must_be_classified_once": True,
        "all_shared_rows_must_bind_both_source_rows": True,
        "proof_and_value_fields_forbidden": True,
        "external_delta_must_be_read_only": True,
        "selected_240_summary_must_equal_the_full_atlas_projection": True,
    }:
        raise PlanError("atlas gates changed")
    if plan["authority"] != {
        "proof_bodies_allowed": False,
        "theorem_values_allowed": False,
        "candidate_reselection_allowed": False,
        "fact_status_changes_allowed": False,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("atlas authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_MATHLIB_FULL_SURVIVAL_PLAN_OK|shared=9712|removed=17|added=110|"
            "structural_passes=0/1|proofs=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-mathlib-full-survival-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
