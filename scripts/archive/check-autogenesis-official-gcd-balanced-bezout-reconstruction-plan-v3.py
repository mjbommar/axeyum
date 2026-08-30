#!/usr/bin/env python3
"""Verify the second corrected balanced-Bezout reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v3.json"
INPUTS = {
    "v2_decline": ("artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v2.json", "98bbd4c2923367f6505b00d0e0d07707d28446b356dd1e3fe180ec2dfd11dc91"),
    "private_joint_invariant_source": ("scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean", "d6daa848bea4fe5a86e9d180f2256a8b0851d44b3dd9c7245ab0c71d344599bf"),
    "corrected_source": ("scripts/lean/autogenesis_official_gcd_balanced_bezout_v3.lean", "68f29bac0488e410a00e449c86d24802114596e3bbe89114904ea0644c6f73ec"),
}
BASELINE = [
    {"path": "AxeyumFibGeneric.lean", "status": "untracked", "bytes": 1595, "mode": "0664", "sha256": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be"},
    {"path": "AxeyumNatFibRecurrencePointwise.lean", "status": "untracked", "bytes": 632, "mode": "0664", "sha256": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5"},
    {"path": "AxeyumNatGcdFixEq.lean", "status": "untracked", "bytes": 3603, "mode": "0664", "sha256": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"},
]
FORBIDDEN = ["Nat.div_add_mod", "Nat.div_eq", "Nat.mod_eq", "Nat.div_mod_exec", "Nat.gcd_zero_left", "Nat.gcd_succ", "Nat.gcd_eq_gcd_ab", "Nat.xgcd_val", "Nat.xgcd.eq_1"]


class BalancedBezoutPlanV3Error(RuntimeError):
    """The V3 source correction, execution, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutPlanV3Error(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (
        3, "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-plan",
        "preregistered-second-corrected-source-before-compilation-no-specialization-credit",
        "official-gcd-balanced-bezout-generic-v3",
    ):
        raise BalancedBezoutPlanV3Error("plan identity changed")
    expected_inputs = {key: {"path": path, "sha256": digest} for key, (path, digest) in INPUTS.items()}
    if plan.get("inputs") != expected_inputs:
        raise BalancedBezoutPlanV3Error("inputs changed")
    for path, digest in INPUTS.values():
        if sha256(ROOT / path) != digest:
            raise BalancedBezoutPlanV3Error(f"input identity changed: {path}")
    if plan.get("corrections") != [
        "rewrite the unfolded Nat.modCore dependent conditional with dif_pos hm",
        "assign both congrArg results explicit normalized product equality types",
        "definitionally change the induction hypothesis to direct Nat.mod and Nat.succ notation",
    ] or plan.get("preexisting_status_baseline") != BASELINE:
        raise BalancedBezoutPlanV3Error("corrections or baseline changed")
    environment = plan.get("fixed_environment", {})
    if environment != {
        "ssh_alias": "s5", "hostname": "server5", "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f", "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lake_binary": "/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lake",
        "lake_binary_sha256": "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b",
        "lean4export_binary": "/home/mjbommar/lean-import-scale/lean4export/.lake/build/bin/lean4export",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449",
    }:
        raise BalancedBezoutPlanV3Error("environment changed")
    if plan.get("targets") != ["Axeyum.Autogenesis.modQuotientWitnessV3", "Axeyum.Autogenesis.officialGcdBalancedBezoutV3"]:
        raise BalancedBezoutPlanV3Error("targets changed")
    if plan.get("construction") != {
        "carrier_definition": "Axeyum.Autogenesis.OfficialBalancedBezoutV3", "public_quotient_used": False,
        "official_gcd_equation_proofs_used": False, "gcd_equations_are_explicit_specialization_parameters": True,
        "required_clean_interface": ["Nat.gcd.induction", "Nat.mod.eq_1", "Nat.mod.eq_2", "Axeyum.Autogenesis.divModGoReconstruct"],
        "forbidden_dependencies": FORBIDDEN,
    }:
        raise BalancedBezoutPlanV3Error("construction changed")
    execution = plan.get("execution", {})
    if (
        execution.get("evidence_pack") != "/nas3/data/axeyum/autogenesis/reference-packs/f96a2319d-official-gcd-balanced-bezout-v3-v1"
        or execution.get("remote_support_source") != "/home/mjbommar/lean-import-scale/mathlib4/autogenesis_div_mod_go_reconstruct_v2.lean"
        or execution.get("remote_main_source") != "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisOfficialGcdBalancedBezoutV3.lean"
        or execution.get("temporary_output_stems") != [
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/autogenesis_div_mod_go_reconstruct_v2",
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisOfficialGcdBalancedBezoutV3",
        ]
        or any(execution.get(key) is not True for key in ["all_temporary_paths_must_be_absent_before_copy", "status_must_equal_exact_baseline_before_copy", "status_must_equal_exact_baseline_after_cleanup", "cleanup_scope_is_exactly_the_two_sources_and_four_outputs"])
        or execution.get("proof_terms_types_or_values_may_be_rendered") is not False
    ):
        raise BalancedBezoutPlanV3Error("execution changed")
    if plan.get("acceptance") != {"both_sources_must_compile": True, "fresh_kernel_imports_required": 2, "both_targets_audited_per_import": True, "rows_must_match_by_target": True, "axiom_footprints_must_be_empty": True, "forbidden_dependencies_must_be_absent": True, "failed_compilation_or_first_import_ends_increment": True, "specialization_authorized_in_this_increment": False}:
        raise BalancedBezoutPlanV3Error("acceptance changed")
    if plan.get("budget") != {"max_source_copies": 2, "max_source_compilations": 2, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 4, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}:
        raise BalancedBezoutPlanV3Error("budget changed")
    if plan.get("authority") != {"proof_bodies_readable_by_model": False, "upstream_proof_sources_readable_by_model": False, "preexisting_files_may_be_opened_by_model": False, "preexisting_files_may_be_changed_or_removed": False, "generic_balanced_bezout_credit_requires_acceptance": True, "target_specialization_credit": 0, "cancellation_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise BalancedBezoutPlanV3Error("authority changed")
    if plan.get("next_on_accept") != "Preregister checked target specialization with the existing empty-footprint Nat.gcd_zero_left and Nat.gcd_succ declarations." or plan.get("output") != "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v3.json" or plan.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan-v3.py" or plan.get("limitations") != "V3 may establish only the two generic theorems. It grants no closed target specialization, cancellation, Fibonacci target, receipt, evaluation, fact, or ledger credit.":
        raise BalancedBezoutPlanV3Error("successor boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_PLAN_V3_OK|targets=2|compilations=0/2|exports=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutPlanV3Error) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-plan-v3: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
