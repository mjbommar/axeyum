#!/usr/bin/env python3
"""Verify the corrected generic official-gcd balanced-Bezout plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v2.json"
INPUTS = {
    "v1_decline": (
        "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v1.json",
        "0c868e6fe4bb2e82f6db35d821d47065b93ed246d0f0036a264c97eb9193c127",
    ),
    "private_joint_invariant_source": (
        "scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean",
        "d6daa848bea4fe5a86e9d180f2256a8b0851d44b3dd9c7245ab0c71d344599bf",
    ),
    "corrected_source": (
        "scripts/lean/autogenesis_official_gcd_balanced_bezout_v2.lean",
        "30fc9fcf5edf9d467110ce36b3796efb2102d9bd6d5401af9d3537b9ae8e71d8",
    ),
}
BASELINE = [
    {"path": "AxeyumFibGeneric.lean", "status": "untracked", "bytes": 1595, "mode": "0664", "sha256": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be"},
    {"path": "AxeyumNatFibRecurrencePointwise.lean", "status": "untracked", "bytes": 632, "mode": "0664", "sha256": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5"},
    {"path": "AxeyumNatGcdFixEq.lean", "status": "untracked", "bytes": 3603, "mode": "0664", "sha256": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"},
]
FORBIDDEN = ["Nat.div_add_mod", "Nat.div_eq", "Nat.mod_eq", "Nat.div_mod_exec", "Nat.gcd_zero_left", "Nat.gcd_succ", "Nat.gcd_eq_gcd_ab", "Nat.xgcd_val", "Nat.xgcd.eq_1"]


class BalancedBezoutPlanV2Error(RuntimeError):
    """The corrected source, baseline, execution budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutPlanV2Error(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 2
        or plan.get("kind") != "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-plan"
        or plan.get("state") != "preregistered-corrected-source-before-compilation-no-specialization-credit"
        or plan.get("policy_version") != "official-gcd-balanced-bezout-generic-v2"
    ):
        raise BalancedBezoutPlanV2Error("plan identity changed")
    expected_inputs = {key: {"path": path, "sha256": digest} for key, (path, digest) in INPUTS.items()}
    if plan.get("inputs") != expected_inputs:
        raise BalancedBezoutPlanV2Error("bound inputs changed")
    for path, digest in INPUTS.values():
        if sha256(ROOT / path) != digest:
            raise BalancedBezoutPlanV2Error(f"input identity changed: {path}")
    if plan.get("corrections") != [
        {"v1_diagnostic": "Nat.mod equations did not match elaborated HMod notation", "v2_change": "helper statement and proof use direct Nat.mod applications"},
        {"v1_diagnostic": "global quotient rewrite changed the gcd remainder subterm", "v2_change": "congrArg derives two multiplication-specific equalities and each is rewritten only in its coefficient context"},
    ]:
        raise BalancedBezoutPlanV2Error("fixed source corrections changed")
    if plan.get("preexisting_status_baseline") != BASELINE:
        raise BalancedBezoutPlanV2Error("pre-existing baseline changed")
    if plan.get("fixed_environment") != {
        "ssh_alias": "s5",
        "hostname": "server5",
        "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lake_binary": "/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lake",
        "lake_binary_sha256": "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449",
    }:
        raise BalancedBezoutPlanV2Error("fixed environment changed")
    if plan.get("targets") != ["Axeyum.Autogenesis.modQuotientWitnessV2", "Axeyum.Autogenesis.officialGcdBalancedBezoutV2"]:
        raise BalancedBezoutPlanV2Error("target roots changed")
    construction = plan.get("construction", {})
    if construction != {
        "carrier_definition": "Axeyum.Autogenesis.OfficialBalancedBezout",
        "public_quotient_used": False,
        "official_gcd_equation_proofs_used": False,
        "gcd_equations_are_explicit_specialization_parameters": True,
        "required_clean_interface": ["Nat.gcd.induction", "Nat.mod.eq_1", "Nat.mod.eq_2", "Axeyum.Autogenesis.divModGoReconstruct"],
        "forbidden_dependencies": FORBIDDEN,
    }:
        raise BalancedBezoutPlanV2Error("construction boundary changed")
    execution = plan.get("execution", {})
    if (
        execution.get("evidence_pack") != "/nas3/data/axeyum/autogenesis/reference-packs/1de1558f7-official-gcd-balanced-bezout-v2-v1"
        or execution.get("remote_support_source") != "/home/mjbommar/lean-import-scale/mathlib4/autogenesis_div_mod_go_reconstruct_v2.lean"
        or execution.get("remote_main_source") != "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisOfficialGcdBalancedBezoutV2.lean"
        or execution.get("temporary_output_stems") != [
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/autogenesis_div_mod_go_reconstruct_v2",
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisOfficialGcdBalancedBezoutV2",
        ]
        or any(execution.get(key) is not True for key in ["all_temporary_paths_must_be_absent_before_copy", "status_must_equal_exact_baseline_before_copy", "status_must_equal_exact_baseline_after_cleanup", "cleanup_scope_is_exactly_the_two_sources_and_four_outputs"])
        or execution.get("proof_terms_types_or_values_may_be_rendered") is not False
    ):
        raise BalancedBezoutPlanV2Error("execution boundary changed")
    if plan.get("acceptance") != {
        "both_sources_must_compile": True,
        "fresh_kernel_imports_required": 2,
        "both_targets_audited_per_import": True,
        "rows_must_match_by_target": True,
        "axiom_footprints_must_be_empty": True,
        "forbidden_dependencies_must_be_absent": True,
        "failed_compilation_or_first_import_ends_increment": True,
        "specialization_authorized_in_this_increment": False,
    }:
        raise BalancedBezoutPlanV2Error("acceptance changed")
    if plan.get("budget") != {
        "max_source_copies": 2, "max_source_compilations": 2, "max_exporter_invocations": 1,
        "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0,
        "max_new_theorem_submissions": 4, "max_exact_fibonacci_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise BalancedBezoutPlanV2Error("budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False, "upstream_proof_sources_readable_by_model": False,
        "preexisting_files_may_be_opened_by_model": False, "preexisting_files_may_be_changed_or_removed": False,
        "generic_balanced_bezout_credit_requires_acceptance": True, "target_specialization_credit": 0,
        "cancellation_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0,
    }:
        raise BalancedBezoutPlanV2Error("authority changed")
    if (
        plan.get("next_on_accept") != "Preregister checked target specialization with the existing empty-footprint Nat.gcd_zero_left and Nat.gcd_succ declarations."
        or plan.get("output") != "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v2.json"
        or plan.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan-v2.py"
        or plan.get("limitations") != "V2 may establish only the two generic theorems. It grants no closed target specialization, cancellation, Fibonacci target, receipt, evaluation, fact, or ledger credit."
    ):
        raise BalancedBezoutPlanV2Error("successor or limitation changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_PLAN_V2_OK|targets=2|compilations=0/2|exports=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutPlanV2Error) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-plan-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
