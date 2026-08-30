#!/usr/bin/env python3
"""Verify the preregistered current-stable Mathlib statement comparison."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-current-stable-statement-comparison-plan-v1.json"


class PlanError(RuntimeError):
    """The version comparison route, input, budget, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-current-stable-statement-comparison-plan"
        or plan.get("state") != "preregistered-no-extraction-or-proof-credit"
        or plan.get("policy_version")
        != "mathlib-selected-statement-version-comparison-v1"
        or plan.get("observation_date") != "2026-08-20"
    ):
        raise PlanError("plan identity changed")

    baseline = plan["baseline"]
    baseline_inventory = baseline["statement_inventory"]
    baseline_path = pathlib.Path(baseline_inventory["path"])
    if (
        baseline.get("mathlib_tag") != "v4.30.0"
        or baseline.get("mathlib_commit")
        != "c5ea00351c28e24afc9f0f84379aa41082b1188f"
        or baseline.get("lean_version") != "4.30.0"
        or baseline.get("lean_githash")
        != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or baseline_inventory.get("sha256")
        != "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
        or baseline_inventory.get("records") != 9729
        or baseline_inventory.get("mode") != "0444"
        or stat.S_IMODE(baseline_path.stat().st_mode) != 0o444
        or sha256(baseline_path) != baseline_inventory["sha256"]
    ):
        raise PlanError("baseline identity changed")

    comparison = plan["comparison"]
    if comparison != {
        "mathlib_tag": "v4.32.1",
        "mathlib_commit": "520045ab14e26149ee970e2e617ca04b09bde5d6",
        "lean_version": "4.32.1",
        "lean_githash": "f054605aea4b840552cca2e725580bffd1e1b704",
        "release_channel": "stable",
        "checkout_path": "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.32.1-checkout",
        "statement_inventory_path": "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.32.1-nat-int-statement-inventory-v1.ndjson",
    }:
        raise PlanError("comparison release identity changed")

    expected_inputs = {
        "source_manifest": "8d7df257783ab2cdcfad18719de68d6f40681e1bacb06e938c7f0827d07eebdc",
        "extractor": "78cc93de6ab3c1fed5378c757f0ebfcbee47e66ecd72c25022755a4707e2b376",
        "selected_candidates": "adbb3aff520664495089312a35ac2be1fd017a4ce39e4eff6443ea067d5c0704",
    }
    for key, expected_sha256 in expected_inputs.items():
        row = plan["inputs"][key]
        if sha256(ROOT / row["path"]) != expected_sha256 or row["sha256"] != expected_sha256:
            raise PlanError(f"{key} identity changed")
    if plan["inputs"]["selected_candidates"].get("records") != 240:
        raise PlanError("selected candidate count changed")

    if len(plan.get("fixed_sequence", [])) != 6 or plan.get("comparison_classes") != [
        "absent-in-current-stable",
        "structurally-identical",
        "pretty-type-only-drift",
        "structural-type-drift",
        "module-only-drift",
    ]:
        raise PlanError("fixed comparison sequence changed")
    if plan["budget"] != {
        "max_mathlib_clones": 1,
        "max_statement_extractions": 1,
        "max_extractor_compatibility_patches": 0,
        "max_selected_comparisons": 240,
        "max_proof_search_invocations": 0,
        "max_kernel_theorem_submissions": 0,
        "max_executor_invocations": 0,
        "max_retries": 0,
    }:
        raise PlanError("comparison budget changed")
    if plan["gates"] != {
        "exact_tags_and_commits_required": True,
        "same_extractor_required": True,
        "proof_and_value_fields_forbidden": True,
        "external_inventory_must_be_read_only": True,
        "baseline_identity_must_not_change": True,
        "all_240_selected_names_must_be_classified": True,
    }:
        raise PlanError("comparison gates changed")
    if plan["authority"] != {
        "mathlib_source_proof_bodies_allowed": False,
        "theorem_values_allowed": False,
        "full_export_required": False,
        "proof_import_allowed": False,
        "fact_status_changes_allowed": False,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("comparison authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_MATHLIB_STABLE_COMPARISON_PLAN_OK|baseline=4.30.0|"
            "comparison=4.32.1|selected=240|extractions=0/1|proofs=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-mathlib-stable-comparison-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
