#!/usr/bin/env python3
"""Verify the corrected rooted xgcd projection reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-rooted-reconstruction-plan-v1.json"
DECLINE = ROOT / "artifacts/autogenesis/xgcd-val-direct-reconstruction-result-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_xgcd_val_direct.lean"
DECLINE_SHA256 = "932b622a69ef4fdc3bbeee5862c7e62d5e9e91d353dbfab52c73b7d40e224914"
SOURCE_SHA256 = "077e5c6320ac8972ca18edb0b75226faac0b062b726609e9d7a213b7f27d2e62"


class XgcdValRootedPlanError(RuntimeError):
    """The corrected execution, cleanup, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValRootedPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("kind") != "axeyum-autogenesis-xgcd-val-rooted-reconstruction-plan"
        or plan.get("state")
        != "preregistered-before-corrected-rooted-source-execution-no-projection-credit"
        or plan.get("policy_version") != "xgcd-val-rooted-reconstruction-v1"
    ):
        raise XgcdValRootedPlanError("plan identity changed")
    if sha256(DECLINE) != DECLINE_SHA256 or sha256(SOURCE) != SOURCE_SHA256:
        raise XgcdValRootedPlanError("decline or source identity changed")
    if plan.get("inputs") != {
        "execution_boundary_decline": {
            "path": "artifacts/autogenesis/xgcd-val-direct-reconstruction-result-v1.json",
            "sha256": DECLINE_SHA256,
        },
        "source": {
            "path": "scripts/lean/autogenesis_xgcd_val_direct.lean",
            "sha256": SOURCE_SHA256,
        },
    }:
        raise XgcdValRootedPlanError("inputs changed")
    if plan.get("target") != {
        "reference_name": "Nat.xgcd_val",
        "authored_name": "Axeyum.Autogenesis.xgcdValDirect",
        "type": "∀ (x y : ℕ), x.xgcd y = (x.gcdA y, x.gcdB y)",
        "type_sha256": "15f2274bf30c6540ff1415cd5f567ddc7e1438282b834a1bf0c7dc88d40ff79c",
    }:
        raise XgcdValRootedPlanError("target changed")
    if plan.get("fixed_environment") != {
        "ssh_alias": "s5",
        "hostname": "server5",
        "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449",
    }:
        raise XgcdValRootedPlanError("fixed environment changed")
    if plan.get("execution") != {
        "evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/9f135d4f0-xgcd-val-rooted-v1",
        "remote_source": "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisXgcdVal.lean",
        "remote_olean": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisXgcdVal.olean",
        "remote_ilean": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisXgcdVal.ilean",
        "all_temporary_paths_must_be_absent_before_copy": True,
        "mathlib_status_entries_before": 0,
        "mathlib_status_entries_after_cleanup": 0,
        "cleanup_scope_is_exactly_the_three_named_paths": True,
        "export_only_after_successful_compilation": True,
        "proof_terms_types_or_values_may_be_rendered": False,
    }:
        raise XgcdValRootedPlanError("execution or cleanup boundary changed")
    if plan.get("acceptance") != {
        "source_must_compile": True,
        "exported_type_must_match_target": True,
        "fresh_kernel_imports_required": 2,
        "both_import_rows_must_match": True,
        "axiom_footprint_must_be_empty": True,
        "direct_theorem_dependencies_must_be_empty": True,
        "failed_compilation_ends_increment": True,
    }:
        raise XgcdValRootedPlanError("acceptance changed")
    if plan.get("budget") != {
        "max_source_copies": 1,
        "max_source_compilations": 1,
        "max_exporter_invocations": 1,
        "max_importer_runs": 2,
        "max_proof_bearing_stream_reads": 2,
        "max_retries": 0,
        "max_new_theorem_submissions": 2,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise XgcdValRootedPlanError("budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "proof_search_allowed": False,
        "projection_equation_credit": 0,
        "extended_gcd_reconstruction_allowed": False,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValRootedPlanError("authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/xgcd-val-rooted-reconstruction-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-xgcd-val-rooted-reconstruction-plan.py"
        or plan.get("limitations")
        != "This corrected execution tests only the definitional projection equation and preserves the clean shared Mathlib checkout. Even two empty imports would not establish the extended-gcd coefficient identity."
    ):
        raise XgcdValRootedPlanError("output boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_ROOTED_PLAN_OK|copies=0/1|compilations=0/1|"
            "exports=0/1|imports=0/2|projection_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValRootedPlanError,
    ) as error:
        print(f"autogenesis-xgcd-val-rooted-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
