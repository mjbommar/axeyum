#!/usr/bin/env python3
"""Verify the baseline-preserving xgcd projection reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/xgcd-val-baseline-preserving-reconstruction-plan-v1.json"
DECLINE = ROOT / "artifacts/autogenesis/xgcd-val-rooted-reconstruction-result-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_xgcd_val_direct.lean"
DECLINE_SHA256 = "7b2255dc984e6415b04eb7b41624944c42e6b8275c4864947ee1c8d854f42212"
SOURCE_SHA256 = "077e5c6320ac8972ca18edb0b75226faac0b062b726609e9d7a213b7f27d2e62"
BASELINE = [
    {
        "path": "AxeyumFibGeneric.lean",
        "status": "untracked",
        "bytes": 1595,
        "mode": "0664",
        "sha256": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be",
    },
    {
        "path": "AxeyumNatFibRecurrencePointwise.lean",
        "status": "untracked",
        "bytes": 632,
        "mode": "0664",
        "sha256": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5",
    },
    {
        "path": "AxeyumNatGcdFixEq.lean",
        "status": "untracked",
        "bytes": 3603,
        "mode": "0664",
        "sha256": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7",
    },
]


class XgcdValBaselinePlanError(RuntimeError):
    """The baseline, exact cleanup, budget, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise XgcdValBaselinePlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("kind")
        != "axeyum-autogenesis-xgcd-val-baseline-preserving-reconstruction-plan"
        or plan.get("state")
        != "preregistered-before-baseline-preserving-rooted-execution-no-projection-credit"
        or plan.get("policy_version")
        != "xgcd-val-baseline-preserving-reconstruction-v1"
    ):
        raise XgcdValBaselinePlanError("plan identity changed")
    if sha256(DECLINE) != DECLINE_SHA256 or sha256(SOURCE) != SOURCE_SHA256:
        raise XgcdValBaselinePlanError("decline or source identity changed")
    if plan.get("preexisting_status_baseline") != BASELINE:
        raise XgcdValBaselinePlanError("preexisting baseline changed")
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
        raise XgcdValBaselinePlanError("fixed environment changed")
    if plan.get("execution") != {
        "evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/1e74d4601-xgcd-val-baseline-preserving-v1",
        "remote_source": "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisXgcdVal.lean",
        "remote_olean": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisXgcdVal.olean",
        "remote_ilean": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisXgcdVal.ilean",
        "all_temporary_paths_must_be_absent_before_copy": True,
        "status_must_equal_exact_baseline_before_copy": True,
        "status_must_equal_exact_baseline_after_cleanup": True,
        "cleanup_scope_is_exactly_the_three_named_paths": True,
        "export_only_after_successful_compilation": True,
        "proof_terms_types_or_values_may_be_rendered": False,
    }:
        raise XgcdValBaselinePlanError("execution or cleanup boundary changed")
    if plan.get("acceptance") != {
        "source_must_compile": True,
        "exported_type_must_match_target": True,
        "fresh_kernel_imports_required": 2,
        "both_import_rows_must_match": True,
        "axiom_footprint_must_be_empty": True,
        "direct_theorem_dependencies_must_be_empty": True,
        "failed_compilation_ends_increment": True,
    }:
        raise XgcdValBaselinePlanError("acceptance changed")
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
        raise XgcdValBaselinePlanError("budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "proof_search_allowed": False,
        "preexisting_files_may_be_opened_by_model": False,
        "preexisting_files_may_be_changed_or_removed": False,
        "projection_equation_credit": 0,
        "extended_gcd_reconstruction_allowed": False,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise XgcdValBaselinePlanError("authority changed")
    if (
        plan.get("inputs")
        != {
            "preflight_decline": {
                "path": "artifacts/autogenesis/xgcd-val-rooted-reconstruction-result-v1.json",
                "sha256": DECLINE_SHA256,
            },
            "source": {
                "path": "scripts/lean/autogenesis_xgcd_val_direct.lean",
                "sha256": SOURCE_SHA256,
            },
        }
        or plan.get("target")
        != {
            "reference_name": "Nat.xgcd_val",
            "authored_name": "Axeyum.Autogenesis.xgcdValDirect",
            "type": "∀ (x y : ℕ), x.xgcd y = (x.gcdA y, x.gcdB y)",
            "type_sha256": "15f2274bf30c6540ff1415cd5f567ddc7e1438282b834a1bf0c7dc88d40ff79c",
        }
    ):
        raise XgcdValBaselinePlanError("inputs or target changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/xgcd-val-baseline-preserving-reconstruction-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-xgcd-val-baseline-preserving-reconstruction-plan.py"
        or plan.get("limitations")
        != "This pass may test only the target-owned projection equation while preserving the exact preexisting three-file baseline. It cannot credit the extended-gcd coefficient identity or alter any preexisting checkout file."
    ):
        raise XgcdValBaselinePlanError("output boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_XGCD_VAL_BASELINE_PLAN_OK|baseline=3|copies=0/1|"
            "compilations=0/1|exports=0/1|imports=0/2|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        XgcdValBaselinePlanError,
    ) as error:
        print(f"autogenesis-xgcd-val-baseline-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
