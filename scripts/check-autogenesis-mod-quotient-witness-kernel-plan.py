#!/usr/bin/env python3
"""Verify the pointwise public-remainder quotient-witness plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mod-quotient-witness-kernel-plan-v1.json"
INPUTS = {
    "v3_decline": ("artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v3.json", "ad2081a083c3c6b78facb490ca136d9d02377e7fb3f7b7dee586cdce96458b1c"),
    "private_joint_invariant_source": ("scripts/lean/autogenesis_div_mod_go_reconstruct_v2.lean", "d6daa848bea4fe5a86e9d180f2256a8b0851d44b3dd9c7245ab0c71d344599bf"),
    "authored_source": ("scripts/lean/autogenesis_mod_quotient_witness_v4.lean", "6197ec88dd8fc726898e78e42fa616c54b70c579ba64d9d68dec26b7fcb11e5c"),
}
BASELINE = [
    {"path": "AxeyumFibGeneric.lean", "status": "untracked", "bytes": 1595, "mode": "0664", "sha256": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be"},
    {"path": "AxeyumNatFibRecurrencePointwise.lean", "status": "untracked", "bytes": 632, "mode": "0664", "sha256": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5"},
    {"path": "AxeyumNatGcdFixEq.lean", "status": "untracked", "bytes": 3603, "mode": "0664", "sha256": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"},
]
FORBIDDEN = ["funext", "propext", "Nat.div_add_mod", "Nat.div_eq", "Nat.mod_eq", "Mathlib.Tactic.Ring.Common", "Mathlib.Tactic.Ring.of_eq"]


class ModQuotientWitnessPlanError(RuntimeError):
    """The pointwise construction, execution, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ModQuotientWitnessPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (1, "axeyum-autogenesis-mod-quotient-witness-kernel-plan", "preregistered-pointwise-transport-source-before-compilation-no-theorem-credit", "mod-quotient-witness-pointwise-v1"):
        raise ModQuotientWitnessPlanError("plan identity changed")
    expected_inputs = {key: {"path": path, "sha256": digest} for key, (path, digest) in INPUTS.items()}
    if plan.get("inputs") != expected_inputs:
        raise ModQuotientWitnessPlanError("inputs changed")
    for path, digest in INPUTS.values():
        if sha256(ROOT / path) != digest:
            raise ModQuotientWitnessPlanError(f"input identity changed: {path}")
    if plan.get("construction") != {"target": "Axeyum.Autogenesis.modQuotientWitnessV4", "contract": "forall m n, 0 < m -> exists q, m * q + Nat.mod n m = n", "method": "constructor cases and pointwise congrArg equality transport only", "required_dependencies": ["Axeyum.Autogenesis.divModGoReconstruct", "Nat.mod.eq_1", "Nat.mod.eq_2"], "forbidden_dependencies": FORBIDDEN, "public_quotient_used": False, "rewrite_under_binder_used": False, "ring_normalization_used": False}:
        raise ModQuotientWitnessPlanError("construction changed")
    if plan.get("preexisting_status_baseline") != BASELINE:
        raise ModQuotientWitnessPlanError("baseline changed")
    if plan.get("fixed_environment") != {"ssh_alias": "s5", "hostname": "server5", "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4", "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f", "lean_version": "4.30.0", "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622", "lake_binary": "/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lake", "lake_binary_sha256": "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b", "lean4export_binary": "/home/mjbommar/lean-import-scale/lean4export/.lake/build/bin/lean4export", "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"}:
        raise ModQuotientWitnessPlanError("environment changed")
    execution = plan.get("execution", {})
    if execution.get("evidence_pack") != "/nas3/data/axeyum/autogenesis/reference-packs/eb061c9bf-mod-quotient-witness-v4-v1" or execution.get("remote_support_source") != "/home/mjbommar/lean-import-scale/mathlib4/autogenesis_div_mod_go_reconstruct_v2.lean" or execution.get("remote_main_source") != "/home/mjbommar/lean-import-scale/mathlib4/AxeyumAutogenesisModQuotientWitnessV4.lean" or execution.get("temporary_output_stems") != ["/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/autogenesis_div_mod_go_reconstruct_v2", "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/AxeyumAutogenesisModQuotientWitnessV4"] or any(execution.get(key) is not True for key in ["all_temporary_paths_must_be_absent_before_copy", "status_must_equal_exact_baseline_before_copy", "status_must_equal_exact_baseline_after_cleanup", "cleanup_scope_is_exactly_the_two_sources_and_four_outputs"]) or execution.get("proof_terms_types_or_values_may_be_rendered") is not False:
        raise ModQuotientWitnessPlanError("execution changed")
    if plan.get("acceptance") != {"both_sources_must_compile": True, "fresh_kernel_imports_required": 2, "rows_must_match": True, "axiom_footprints_must_be_empty": True, "forbidden_dependencies_must_be_absent": True, "failed_compilation_or_first_import_ends_increment": True}:
        raise ModQuotientWitnessPlanError("acceptance changed")
    if plan.get("budget") != {"max_source_copies": 2, "max_source_compilations": 2, "max_exporter_invocations": 1, "max_importer_runs": 2, "max_proof_bearing_stream_reads": 2, "max_retries": 0, "max_new_theorem_submissions": 2, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}:
        raise ModQuotientWitnessPlanError("budget changed")
    if plan.get("authority") != {"proof_bodies_readable_by_model": False, "upstream_proof_sources_readable_by_model": False, "preexisting_files_may_be_opened_by_model": False, "preexisting_files_may_be_changed_or_removed": False, "quotient_witness_credit_requires_acceptance": True, "balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise ModQuotientWitnessPlanError("authority changed")
    if plan.get("next_on_accept") != "Preregister an explicit clean balanced Euclidean update over the four-Nat carrier, without Mathlib ring normalization." or plan.get("output") != "artifacts/autogenesis/mod-quotient-witness-kernel-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-mod-quotient-witness-kernel-plan.py" or plan.get("limitations") != "This increment may establish only the public-remainder existential quotient witness. It grants no balanced Bezout, target specialization, cancellation, Fibonacci target, receipt, evaluation, fact, or ledger credit.":
        raise ModQuotientWitnessPlanError("successor boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_MOD_QUOTIENT_WITNESS_PLAN_OK|targets=1|compilations=0/2|exports=0/1|imports=0/2|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ModQuotientWitnessPlanError) as error:
        print(f"autogenesis-mod-quotient-witness-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
