#!/usr/bin/env python3
"""Verify the Fibonacci coprimality premise plan and composition blocker."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-fib-coprime-premise-plan-v1.json"


class PlanError(RuntimeError):
    """The frozen plan, evidence, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PlanError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = load(MANIFEST) if manifest is None else manifest
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-coprime-premise-plan"
        or manifest.get("state")
        != "proof-plan-frozen-canonical-acc-library-slice-compatible"
    ):
        raise PlanError("manifest identity changed")
    source = manifest["source"]
    if sha256(pathlib.Path(source["stream"])) != source["stream_sha256"]:
        raise PlanError("source stream changed")
    implementation = manifest["implementation"]
    if (
        implementation["evidence_commit"]
        != "3d466b45cc34435702db09604f47d0362eb9d17b"
        or implementation["bool_order_commit"]
        != "772646c0d1a0c6ebca302c37a42cf2bb2f5030ee"
        or implementation["bool_constructor_order"]
        != ["Bool.false", "Bool.true"]
        or sha256(ROOT / implementation["logic_prelude"])
        != implementation["logic_prelude_sha256"]
        or implementation["nat_mod_lt_commit"]
        != "a5a1114989077b7254a5dec0daa048aa5d2793ba"
        or implementation["nat_mod_lt_contract"]
        != "forall x y, 0 < y -> Nat.mod x y < y"
        or len(implementation["nat_mod_lt_sources"]) != 4
        or any(
            sha256(ROOT / row["path"]) != row["sha256"]
            for row in implementation["nat_mod_lt_sources"]
        )
        or implementation["acc_package_commit"]
        != "3d466b45cc34435702db09604f47d0362eb9d17b"
        or implementation["acc_package"]["family"] != "Acc"
        or implementation["acc_package"]["constructor"] != "Acc.intro"
        or implementation["acc_package"]["recursor"] != "Acc.rec"
    ):
        raise PlanError("native alignment implementation identity changed")
    probe = manifest["composition_probe"]
    if sha256(ROOT / probe["tool"]) != probe["tool_sha256"]:
        raise PlanError("composition probe changed")
    if sha256(ROOT / probe["api"]) != probe["api_sha256"]:
        raise PlanError("composition API changed")
    observation_path = pathlib.Path(probe["observation"])
    if (
        sha256(observation_path) != probe["observation_sha256"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_path.parent.stat().st_mode) != 0o555
    ):
        raise PlanError("composition observation changed or is mutable")
    observation = load(observation_path)
    required = manifest["proof_plan"]["required_native_declarations"]
    presence = observation["source"]["required_declarations_present"]
    if (
        observation["source"]["stream_sha256"] != source["stream_sha256"]
        or observation["source"]["axioms"] != []
        or observation["source"]["declarations_before"]
        != probe["imported_declarations"]
        or observation["source"]["theorems_before"] != probe["imported_theorems"]
        or observation["result"]["outcome"] != probe["outcome"]
        or observation["result"]["conflicting_name"] != probe["first_conflict"]
        or observation["source"]["native_declarations"]
        != probe["native_declarations"]
        or len(observation["source"]["exact_overlap_names"])
        != probe["exact_overlaps"]
        or len(
            observation["source"][
                "alpha_type_compatible_content_mismatched_names"
            ]
        )
        != probe["alpha_type_compatible_content_mismatches"]
        or len(
            observation["source"][
                "kernel_type_shape_compatible_content_mismatched_names"
            ]
        )
        != probe["kernel_type_shape_compatible_content_mismatches"]
        or len(observation["source"]["type_mismatched_overlaps"])
        != probe["unresolved_type_overlaps"]
        or any(presence[name] for name in required)
        or not presence["Nat.rec"]
        or manifest["proof_plan"]["required_present_in_import"] != []
        or manifest["proof_plan"]["already_present_in_import"] != ["Nat.rec"]
    ):
        raise PlanError("composition observation semantics changed")
    categories = [
        observation["source"]["exact_overlap_names"],
        observation["source"]["alpha_type_compatible_content_mismatched_names"],
        observation["source"][
            "kernel_type_shape_compatible_content_mismatched_names"
        ],
        [row["name"] for row in observation["source"]["type_mismatched_overlaps"]],
    ]
    flattened = [name for category in categories for name in category]
    exact_bool_package = {"Bool", "Bool.false", "Bool.rec", "Bool.true"}
    if (
        len(flattened) != 43
        or len(set(flattened)) != len(flattened)
        or any(category != sorted(category) for category in categories)
        or not exact_bool_package.issubset(categories[0])
        or any(
            exact_bool_package.intersection(category) for category in categories[1:]
        )
        or observation["authority"]
        != {
            "proof_bodies_displayed": False,
            "proof_search_invocations": 0,
            "kernel_submissions": 24,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("composition overlap partition or authority changed")
    mod_lt_compatibility = observation["source"]["mod_lt_compatibility_control"]
    mod_lt_result = manifest["nat_mod_lt_compatibility_result"]
    mod_lt_overlap = next(
        (
            row
            for row in observation["source"]["type_mismatched_overlaps"]
            if row["name"] == "Nat.mod_lt"
        ),
        None,
    )
    if (
        mod_lt_compatibility != mod_lt_result
        or mod_lt_overlap is None
        or mod_lt_overlap["native_content_sha256"]
        != mod_lt_result["source_declaration_sha256"]
        or mod_lt_overlap["imported_content_sha256"]
        != mod_lt_result["target_declaration_sha256"]
        or mod_lt_overlap["native_kernel_type_shape_sha256"]
        != mod_lt_result["source_type_shape_sha256"]
        or mod_lt_overlap["imported_kernel_type_shape_sha256"]
        != mod_lt_result["target_type_shape_sha256"]
        or mod_lt_result["compatibility"] != "translated-definitional-equality"
    ):
        raise PlanError("Nat.mod_lt checked compatibility changed")
    closures = observation["source"]["required_native_theorem_dependency_closures"]
    for row in closures:
        closure_categories = [
            row["missing_dependency_names"],
            row["exact_dependency_names"],
            row["alpha_type_compatible_dependency_names"],
            row["kernel_type_shape_compatible_dependency_names"],
            row["type_mismatched_dependency_names"],
        ]
        closure_names = [name for category in closure_categories for name in category]
        if (
            len(closure_names) != row["native_dependency_count"]
            or len(set(closure_names)) != len(closure_names)
            or any(category != sorted(category) for category in closure_categories)
        ):
            raise PlanError(f"invalid dependency closure partition for {row['theorem']}")
    closure_census = manifest["closure_census"]
    unblocked = [
        row for row in closures if not row["type_mismatched_dependency_names"]
    ]
    blocked = sorted(
        row["theorem"] for row in closures if row["type_mismatched_dependency_names"]
    )
    if (
        len(closures) != closure_census["required_theorems"]
        or len(unblocked) != 1
        or unblocked[0]["theorem"]
        != closure_census["first_structurally_unblocked_theorem"]
        or unblocked[0]["native_dependency_count"]
        != closure_census["first_dependency_count"]
        or unblocked[0]["missing_dependency_names"]
        != closure_census["first_missing_dependencies"]
        or blocked != closure_census["structurally_blocked_theorems"]
    ):
        raise PlanError("required theorem closure census changed")
    composed = observation["source"]["composition_control"]
    negative = observation["source"]["structural_mismatch_control"]
    composition_result = manifest["composition_result"]
    reused_receipts = composed["reused_declaration_receipts"]
    reused_names = [row["name"] for row in reused_receipts]
    exact_reused = sum(
        row["source_declaration_sha256"] == row["target_declaration_sha256"]
        for row in reused_receipts
    )
    type_shape_only_reused = len(reused_receipts) - exact_reused
    compatibility_counts = {
        kind: sum(row["compatibility"] == kind for row in reused_receipts)
        for kind in [
            "kernel-type-shape",
            "translated-definitional-equality",
        ]
    }
    if (
        composed["roots"] != [composition_result["root"]]
        or composed["source_closure"] != composition_result["source_closure"]
        or composed["source_closure"][-1] != composition_result["root"]
        or composed["outcome"] != composition_result["outcome"]
        or composed["receipt_schema"] != composition_result["receipt_schema"]
        or composed["receipt_sha256"] != composition_result["receipt_sha256"]
        or len(composed["reused_dependency_names"])
        != composition_result["reused_dependencies"]
        or reused_names != composed["reused_dependency_names"]
        or len(reused_receipts) != composition_result["reused_dependencies"]
        or exact_reused != composition_result["reused_exact_declarations"]
        or type_shape_only_reused
        != composition_result["reused_type_shape_compatible_content_mismatches"]
        or compatibility_counts != composition_result["reused_compatibility"]
        or any(
            row["source_type_shape_sha256"] != row["target_type_shape_sha256"]
            for row in reused_receipts
        )
        or composed["added_theorem_names"]
        != composition_result["added_theorem_names"]
        or composed["added_definitions"]
        != composition_result["added_definitions"]
        or composed["added_singleton_inductives"]
        != composition_result["added_singleton_inductives"]
        or composed["declarations_absent_before"]
        != composition_result["added_theorem_names"]
        or composed["added_declaration_sha256"]
        != composition_result["added_declaration_sha256"]
        or composed["added_axiom_footprints"]
        != composition_result["added_axiom_footprints"]
        or composed["environment_sha256_before"]
        != composition_result["environment_sha256_before"]
        or composed["environment_sha256_after"]
        != composition_result["environment_sha256_after"]
        or composed["environment_sha256_before"]
        == composed["environment_sha256_after"]
        or negative["root"] != composition_result["negative_control_root"]
        or negative["error"] != composition_result["negative_control_error"]
        or composition_result["negative_control_first_rejected"]
        not in negative["error"]
        or composition_result["negative_control_error_kind"]
        not in negative["error"]
        or negative["environment_sha256_before"]
        != composition_result["negative_control_environment_sha256"]
        or negative["environment_sha256_after"]
        != composition_result["negative_control_environment_sha256"]
        or (negative["environment_sha256_before"] == negative["environment_sha256_after"])
        != composition_result["negative_control_environment_unchanged"]
    ):
        raise PlanError("native theorem composition result changed")
    singleton = observation["source"]["singleton_inductive_control"]
    singleton_result = manifest["singleton_inductive_result"]
    if (
        singleton["roots"] != [singleton_result["root"]]
        or singleton["outcome"] != singleton_result["outcome"]
        or singleton["receipt_schema"] != singleton_result["receipt_schema"]
        or singleton["receipt_sha256"] != singleton_result["receipt_sha256"]
        or singleton["added_theorem_names"]
        != singleton_result["added_theorem_names"]
        or singleton["added_axiom_footprints"]
        != singleton_result["added_axiom_footprints"]
        or singleton["added_singleton_inductives"]
        != singleton_result["added_singleton_inductives"]
        or singleton["environment_sha256_before"]
        != singleton_result["environment_sha256_before"]
        or singleton["environment_sha256_after"]
        != singleton_result["environment_sha256_after"]
        or singleton["environment_sha256_before"]
        == singleton["environment_sha256_after"]
    ):
        raise PlanError("singleton inductive composition result changed")
    for package in singleton["added_singleton_inductives"]:
        expected_names = [package["family"], *package["constructors"], package["recursor"]]
        if (
            sorted(package["source_declaration_sha256"]) != sorted(expected_names)
            or package["source_declaration_sha256"]
            != package["target_declaration_sha256"]
        ):
            raise PlanError("singleton inductive identity changed")
    acc = observation["source"]["acc_inductive_control"]
    acc_result = manifest["acc_inductive_result"]
    if (
        acc["roots"] != [acc_result["root"]]
        or acc["outcome"] != acc_result["outcome"]
        or acc["receipt_schema"] != acc_result["receipt_schema"]
        or acc["receipt_sha256"] != acc_result["receipt_sha256"]
        or acc["added_theorem_names"] != acc_result["added_theorem_names"]
        or acc["added_axiom_footprints"]
        != acc_result["added_axiom_footprints"]
        or acc["added_singleton_inductives"]
        != acc_result["added_singleton_inductives"]
        or acc["environment_sha256_before"]
        != acc_result["environment_sha256_before"]
        or acc["environment_sha256_after"]
        != acc_result["environment_sha256_after"]
        or acc["environment_sha256_before"] == acc["environment_sha256_after"]
        or acc["added_axiom_footprints"] != {"Acc.inv": []}
        or len(acc["added_singleton_inductives"]) != 1
    ):
        raise PlanError("Acc inductive composition result changed")
    acc_package = acc["added_singleton_inductives"][0]
    if (
        acc_package["family"] != "Acc"
        or acc_package["constructors"] != ["Acc.intro"]
        or acc_package["recursor"] != "Acc.rec"
        or acc_package["source_declaration_sha256"]
        != implementation["acc_package"]["source_declaration_sha256"]
        or acc_package["source_declaration_sha256"]
        != acc_package["target_declaration_sha256"]
    ):
        raise PlanError("Acc inductive identity changed")
    definition = observation["source"]["definition_control"]
    definition_result = manifest["definition_result"]
    definition_reuse_counts = {
        kind: sum(
            row["compatibility"] == kind
            for row in definition["reused_declaration_receipts"]
        )
        for kind in ["kernel-type-shape", "translated-definitional-equality"]
    }
    if (
        definition["roots"] != [definition_result["root"]]
        or definition["source_closure"] != definition_result["source_closure"]
        or definition["source_closure"][-1] != definition_result["root"]
        or definition["outcome"] != definition_result["outcome"]
        or definition["receipt_schema"] != definition_result["receipt_schema"]
        or definition["receipt_sha256"] != definition_result["receipt_sha256"]
        or definition["added_definitions"]
        != definition_result["added_definitions"]
        or [row["name"] for row in definition["added_definitions"]]
        != ["Nat.mul", "Nat.dvd"]
        or any(
            row["source_declaration_sha256"]
            != row["target_declaration_sha256"]
            for row in definition["added_definitions"]
        )
        or definition["added_theorem_names"]
        != definition_result["added_theorem_names"]
        or definition["added_axiom_footprints"]
        != definition_result["added_axiom_footprints"]
        or any(definition["added_axiom_footprints"].values())
        or [
            row["family"] for row in definition["added_singleton_inductives"]
        ]
        != definition_result["added_singleton_inductive_families"]
        or definition["added_singleton_inductives"]
        != singleton_result["added_singleton_inductives"]
        or definition_reuse_counts != definition_result["reused_compatibility"]
        or definition["environment_sha256_before"]
        != definition_result["environment_sha256_before"]
        or definition["environment_sha256_after"]
        != definition_result["environment_sha256_after"]
        or definition["environment_sha256_before"]
        == definition["environment_sha256_after"]
    ):
        raise PlanError("definition composition result changed")
    if (
        manifest["target"]["fact_id"]
        != "F:ml430-nat-fib-coprime-fib-succ-162fc738"
        or manifest["target"]["sole_admitted_theorem_premise"]
        != "F:ml430-nat-fib-add-two-b86e0c82"
    ):
        raise PlanError("target premise boundary changed")
    if manifest["authority"] != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_displayed": False,
        "proof_search_invocations": 0,
        "kernel_submissions": 24,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PlanError("plan authority changed")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_NAT_FIB_COPRIME_PREMISE_PLAN_OK|"
            f"required={len(manifest['proof_plan']['required_native_declarations'])}|"
            "present=0|exact=11|compatible=Nat.mod_lt,Acc|next=Nat.div_mod_exec|"
            "submissions=24|evaluation=0|writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-nat-fib-coprime-premise-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
