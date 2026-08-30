#!/usr/bin/env python3
"""Verify the generic official-gcd balanced-Bezout reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v1.json"
INPUTS = {
    "private_joint_invariant_result": (
        "artifacts/autogenesis/euclidean-joint-div-mod-local-subtraction-replacement-result-v1.json",
        "3c181eb4c14a37cdb0046c915e3bf04e96f7c6f48f2688448a7a61a871c2dfb1",
    ),
    "private_joint_invariant_source": (
        "scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean",
        "d6daa848bea4fe5a86e9d180f2256a8b0851d44b3dd9c7245ab0c71d344599bf",
    ),
    "extended_gcd_route_result": (
        "artifacts/autogenesis/extended-gcd-novel-dependency-audit-result-v1.json",
        "15ae23fb0107b76e59905eb2c58f8988db45a406f1e8cc178fb24ec704fa1cb9",
    ),
    "native_cancellation_result": (
        "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-support-result-v2.json",
        "62aaba46d9aadaa378c0f0efdc847030d5f801794d926d67432a626d44e2b3e2",
    ),
    "authored_source": (
        "scripts/lean/autogenesis_official_gcd_balanced_bezout.lean",
        "55597bafc9e3bc8f732d5504a8177bbd075067713f63caee709cdcbf52344c20",
    ),
}
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
FORBIDDEN = [
    "Nat.div_add_mod",
    "Nat.div_eq",
    "Nat.mod_eq",
    "Nat.div_mod_exec",
    "Nat.gcd_zero_left",
    "Nat.gcd_succ",
    "Nat.gcd_eq_gcd_ab",
    "Nat.xgcd_val",
    "Nat.xgcd.eq_1",
]


class BalancedBezoutPlanError(RuntimeError):
    """The construction, fleet baseline, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-plan"
        or plan.get("state")
        != "preregistered-before-baseline-preserving-generic-reconstruction-no-specialization-credit"
        or plan.get("policy_version") != "official-gcd-balanced-bezout-generic-v1"
    ):
        raise BalancedBezoutPlanError("plan identity changed")
    expected_inputs = {
        key: {"path": path, "sha256": expected}
        for key, (path, expected) in INPUTS.items()
    }
    if plan.get("inputs") != expected_inputs:
        raise BalancedBezoutPlanError("bound inputs changed")
    for path, expected in INPUTS.values():
        if sha256(ROOT / path) != expected:
            raise BalancedBezoutPlanError(f"input identity changed: {path}")
    if plan.get("preexisting_status_baseline") != BASELINE:
        raise BalancedBezoutPlanError("pre-existing checkout baseline changed")
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
        raise BalancedBezoutPlanError("fixed environment changed")
    if plan.get("targets") != [
        {
            "name": "Axeyum.Autogenesis.modQuotientWitness",
            "contract": "forall m n, 0 < m -> exists q, m * q + n % m = n",
        },
        {
            "name": "Axeyum.Autogenesis.officialGcdBalancedBezout",
            "contract": "forall gcdZeroLeft gcdSucc m n, BalancedBezout m n (Nat.gcd m n)",
        },
    ]:
        raise BalancedBezoutPlanError("target contracts changed")
    construction = plan.get("construction", {})
    if (
        construction.get("coefficient_carrier")
        != "four natural positive-and-negative parts"
        or construction.get("public_quotient_used") is not False
        or construction.get("official_gcd_equation_proofs_used") is not False
        or construction.get("gcd_equations_are_explicit_specialization_parameters") is not True
        or construction.get("required_clean_interface")
        != [
            "Nat.gcd.induction",
            "Nat.mod.eq_1",
            "Nat.mod.eq_2",
            "Axeyum.Autogenesis.divModGoReconstruct",
        ]
        or construction.get("forbidden_dependencies") != FORBIDDEN
    ):
        raise BalancedBezoutPlanError("construction boundary changed")
    execution = plan.get("execution", {})
    if (
        execution.get("evidence_pack")
        != "/nas3/data/axeyum/autogenesis/reference-packs/72bbf331d-official-gcd-balanced-bezout-v1"
        or execution.get("remote_support_source")
        != "/home/mjbommar/lean-import-scale/mathlib4/autogenesis_div_mod_go_reconstruct_v2.lean"
        or execution.get("remote_main_source")
        != "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisOfficialGcdBalancedBezout.lean"
        or execution.get("temporary_output_stems")
        != [
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/autogenesis_div_mod_go_reconstruct_v2",
            "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisOfficialGcdBalancedBezout",
        ]
        or any(
            execution.get(key) is not True
            for key in [
                "all_temporary_paths_must_be_absent_before_copy",
                "status_must_equal_exact_baseline_before_copy",
                "status_must_equal_exact_baseline_after_cleanup",
                "cleanup_scope_is_exactly_the_two_sources_and_four_outputs",
                "export_only_after_successful_compilation",
            ]
        )
        or execution.get("proof_terms_types_or_values_may_be_rendered") is not False
    ):
        raise BalancedBezoutPlanError("execution or cleanup boundary changed")
    if plan.get("acceptance") != {
        "both_sources_must_compile": True,
        "fresh_kernel_imports_required": 2,
        "both_targets_audited_per_import": True,
        "all_four_audit_rows_must_match_by_target": True,
        "axiom_footprints_must_be_empty": True,
        "forbidden_dependencies_must_be_absent": True,
        "failed_compilation_or_first_import_ends_increment": True,
        "specialization_authorized_in_this_increment": False,
    }:
        raise BalancedBezoutPlanError("acceptance rule changed")
    if plan.get("budget") != {
        "max_source_copies": 2,
        "max_source_compilations": 2,
        "max_exporter_invocations": 1,
        "max_importer_runs": 2,
        "max_proof_bearing_stream_reads": 2,
        "max_retries": 0,
        "max_new_theorem_submissions": 4,
        "max_exact_fibonacci_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise BalancedBezoutPlanError("execution budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "upstream_proof_sources_readable_by_model": False,
        "preexisting_files_may_be_opened_by_model": False,
        "preexisting_files_may_be_changed_or_removed": False,
        "generic_balanced_bezout_credit_requires_acceptance": True,
        "target_specialization_credit": 0,
        "cancellation_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise BalancedBezoutPlanError("authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-plan.py"
        or plan.get("next_on_accept")
        != "Preregister checked specialization with the existing empty-footprint target Nat.gcd_zero_left and Nat.gcd_succ declarations, then reconstruct cancellation before any Fibonacci target submission."
        or plan.get("limitations")
        != "This increment may establish only the generic target-owned quotient witness and balanced Bezout theorem. It grants no closed target specialization, cancellation, Fibonacci target, receipt, evaluation, fact, or ledger credit."
    ):
        raise BalancedBezoutPlanError("output or authority prose changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_PLAN_OK|targets=2|"
            "compilations=0/2|exports=0/1|imports=0/2|specializations=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        BalancedBezoutPlanError,
    ) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
