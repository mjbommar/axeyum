#!/usr/bin/env python3
"""Verify the exact official-representation gcd successor export plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-succ-root-export-plan-v1.json"
ZERO_LEFT_RESULT = ROOT / "artifacts/autogenesis/official-gcd-zero-left-root-export-result-v1.json"
SOURCE = ROOT / "scripts/lean/autogenesis_nat_gcd_fix_eq_v2.lean"
ZERO_LEFT_RESULT_SHA256 = "a6bed60ca9d85ca49313a3db1968ee1d50917f201449cfb6e523be74216f8af1"
SOURCE_SHA256 = "a893175b87b5ddcab95a9fdf5abf5436880ba116d308e1f5169f5dd512bb83c1"
COMMAND_TAIL = ["env", "/home/mjbommar/lean-import-scale/lean4export/.lake/build/bin/lean4export", "AxeyumAutogenesisNatGcdFixEqV2", "--", "Axeyum.Autogenesis.nat_gcd_succ"]
FIXED_ENVIRONMENT = {"ssh_alias": "s5", "hostname": "server5", "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4", "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f", "lean_version": "4.30.0", "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622", "lean4export_binary": "/home/mjbommar/lean-import-scale/lean4export/.lake/build/bin/lean4export", "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"}
BASELINE = [
    {"path": "AxeyumFibGeneric.lean", "status": "untracked", "bytes": 1595, "mode": "0664", "sha256": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be"},
    {"path": "AxeyumNatFibRecurrencePointwise.lean", "status": "untracked", "bytes": 632, "mode": "0664", "sha256": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5"},
    {"path": "AxeyumNatGcdFixEq.lean", "status": "untracked", "bytes": 3603, "mode": "0664", "sha256": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"},
]


class OfficialGcdSuccRootExportPlanError(RuntimeError):
    """The source, representation, root, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdSuccRootExportPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-succ-root-export-plan", "preregistered-official-representation-successor-root-export-no-new-credit"):
        raise OfficialGcdSuccRootExportPlanError("plan identity changed")
    if sha256(ZERO_LEFT_RESULT) != ZERO_LEFT_RESULT_SHA256 or sha256(SOURCE) != SOURCE_SHA256:
        raise OfficialGcdSuccRootExportPlanError("input identity changed")
    inputs = plan.get("inputs", {})
    if inputs.get("accepted_zero_left_result") != {"path": "artifacts/autogenesis/official-gcd-zero-left-root-export-result-v1.json", "sha256": ZERO_LEFT_RESULT_SHA256}:
        raise OfficialGcdSuccRootExportPlanError("accepted zero-left identity changed")
    if inputs.get("authored_source") != {"path": "scripts/lean/autogenesis_nat_gcd_fix_eq_v2.lean", "sha256": SOURCE_SHA256, "proof_change_from_zero_left_execution": False}:
        raise OfficialGcdSuccRootExportPlanError("source identity changed")
    if "official Mathlib WellFounded representation" not in inputs.get("representation_reason", ""):
        raise OfficialGcdSuccRootExportPlanError("representation reason changed")
    if plan.get("fixed_environment") != FIXED_ENVIRONMENT or plan.get("preexisting_status_baseline") != BASELINE:
        raise OfficialGcdSuccRootExportPlanError("environment or remote baseline changed")
    expected_export = {"module": "AxeyumAutogenesisNatGcdFixEqV2", "separator": "--", "ordered_roots": ["Axeyum.Autogenesis.nat_gcd_succ"], "command_tail": COMMAND_TAIL, "max_stream_bytes": 2000000, "importer_record_limit": 2000000}
    if plan.get("export") != expected_export:
        raise OfficialGcdSuccRootExportPlanError("theorem-root invocation changed")
    expected_execution = {"evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/dfcff00d1-official-gcd-succ-root-v1", "remote_source": "AxeyumAutogenesisNatGcdFixEqV2.lean", "remote_output_stem": ".lake/build/lib/lean/AxeyumAutogenesisNatGcdFixEqV2", "all_three_temporary_paths_must_be_absent_before_copy": True, "status_must_equal_exact_baseline_before_copy": True, "status_must_equal_exact_baseline_after_cleanup": True, "proof_terms_types_or_values_may_be_rendered": False}
    if plan.get("execution") != expected_execution:
        raise OfficialGcdSuccRootExportPlanError("execution boundary changed")
    expected_acceptance = {"source_must_compile": True, "root_selected_stream_must_be_nonempty": True, "root_selected_stream_must_not_exceed_max_bytes": True, "fresh_kernel_imports_required": 2, "audits_must_be_byte_identical": True, "axiom_footprint_must_be_empty": True, "required_direct_dependency": "Axeyum.Autogenesis.gcdModel_succ", "forbidden_dependencies": ["Nat.gcd_succ", "WellFounded.Nat.fix_eq", "funext", "propext"], "failed_compilation_export_or_first_import_ends_increment": True}
    if plan.get("acceptance") != expected_acceptance:
        raise OfficialGcdSuccRootExportPlanError("acceptance contract changed")
    expected_budget = {"max_source_copies": 1, "max_compiler_invocations": 1, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 1, "max_closed_balanced_bezout_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != expected_budget:
        raise OfficialGcdSuccRootExportPlanError("budget changed")
    expected_authority = {"inherited_official_gcd_zero_left_credit": 1, "new_official_gcd_succ_credit": 0, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if plan.get("authority") != expected_authority:
        raise OfficialGcdSuccRootExportPlanError("authority changed")
    if plan.get("output") != "artifacts/autogenesis/official-gcd-succ-root-export-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-official-gcd-succ-root-export-plan.py":
        raise OfficialGcdSuccRootExportPlanError("result or verification path changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_SUCC_ROOT_EXPORT_PLAN_OK|roots=1|max_bytes=2000000|imports=2|new_succ_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdSuccRootExportPlanError) as error:
        print(f"autogenesis-official-gcd-succ-root-export-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
