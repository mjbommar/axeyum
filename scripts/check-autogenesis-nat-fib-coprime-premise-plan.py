#!/usr/bin/env python3
"""Verify the Fibonacci coprimality premise plan and composition blocker."""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import stat
import subprocess
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


def git_blob_sha256(revision: str, path: str) -> str:
    """Hash one tracked file at the evidence-producing revision.

    Immutable evidence binds the tool that produced it, not every future
    version of the same path. Reading the pinned blob keeps historical packs
    verifiable while allowing the current implementation to evolve.
    """
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise PlanError("historical tool revision is not a full Git object ID")
    relative = pathlib.PurePosixPath(path)
    if relative.is_absolute() or ".." in relative.parts:
        raise PlanError("historical tool path is not repository-relative")
    completed = subprocess.run(
        ["git", "show", f"{revision}:{relative.as_posix()}"],
        cwd=ROOT,
        check=False,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise PlanError("historical tool blob is unavailable")
    return hashlib.sha256(completed.stdout).hexdigest()


def validate_official_support_audit(manifest: dict[str, Any]) -> None:
    audit = manifest["official_support_audit"]
    audit_path = pathlib.Path(audit["manifest"])
    audit_dir = audit_path.parent
    if (
        sha256(audit_path) != audit["manifest_sha256"]
        or stat.S_IMODE(audit_dir.stat().st_mode) != 0o555
        or stat.S_IMODE(audit_path.stat().st_mode) != 0o444
    ):
        raise PlanError("official support audit changed or is mutable")
    external = load(audit_path)
    if (
        external.get("schema_version") != 1
        or external.get("kind") != "axeyum-lean430-nat-division-support-audit"
        or external.get("lean_version") != audit["lean_version"]
        or external.get("lean_githash") != audit["lean_githash"]
        or external.get("lean4export_commit") != audit["lean4export_commit"]
        or external.get("audit_commit") != audit["audit_commit"]
        or external.get("audit_tool_sha256")
        != git_blob_sha256(
            audit["audit_commit"],
            "crates/axeyum-lean-import/examples/lean4export_import.rs",
        )
        or external.get("authority")
        != {
            "proof_search_invocations": 0,
            "imported_declarations_admitted": 719,
            "admitted_by_artifact": {
                "Nat.dvd_mod_iff": 395,
                "Nat.mod_add_div": 324,
            },
            "ledger_writes": 0,
        }
    ):
        raise PlanError("official support audit identity or authority changed")
    artifacts = external.get("artifacts")
    if not isinstance(artifacts, list) or len(artifacts) != 2:
        raise PlanError("official support audit artifact set changed")
    expected_theorems = audit["theorems"]
    if sorted(row.get("root") for row in artifacts) != sorted(expected_theorems):
        raise PlanError("official support audit theorem set changed")
    for row in artifacts:
        root = row["root"]
        stream_path = audit_dir / row["stream"]
        report_path = audit_dir / row["audit"]
        expected = expected_theorems[root]
        if (
            sha256(stream_path) != row["stream_sha256"]
            or sha256(report_path) != row["audit_sha256"]
            or stat.S_IMODE(stream_path.stat().st_mode) != 0o444
            or stat.S_IMODE(report_path.stat().st_mode) != 0o444
            or row["declaration_sha256"] != expected["declaration_sha256"]
            or row["axiom_footprint"] != expected["axiom_footprint"]
            or row["axiom_footprint"] != ["propext"]
        ):
            raise PlanError(f"official support audit changed for {root}")
        report = report_path.read_text()
        if (
            f"name={root}|identity={row['declaration_sha256']}|axiom_free=false|"
            not in report
            or "|axiom_footprint=propext|" not in report
        ):
            raise PlanError(f"official support audit report changed for {root}")


def validate_official_equation_pack(manifest: dict[str, Any]) -> None:
    pack = manifest["official_equation_pack"]
    manifest_path = pathlib.Path(pack["manifest"])
    pack_dir = manifest_path.parent
    if (
        sha256(manifest_path) != pack["manifest_sha256"]
        or stat.S_IMODE(pack_dir.stat().st_mode) != 0o555
        or stat.S_IMODE(manifest_path.stat().st_mode) != 0o444
    ):
        raise PlanError("official equation pack changed or is mutable")
    external = load(manifest_path)
    source = external["source"]
    audit = external["audit"]
    composition = external["composition"]
    source_path = pack_dir / source["path"]
    audit_path = pack_dir / audit["path"]
    receipt_path = pack_dir / composition["receipt"]
    if (
        external.get("schema_version") != 1
        or external.get("kind") != "axeyum-lean430-nat-mod-equation-pack"
        or external.get("lean_version") != "4.30.0"
        or external.get("lean_githash")
        != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or external.get("composition_tool_commit") != pack["implementation_commit"]
        or external.get("composition_tool_sha256")
        != git_blob_sha256(pack["implementation_commit"], external["composition_tool"])
        or external.get("generation")
        != {
            "module": "Init",
            "roots": ["Nat.mod.eq_2", "Nat.modCore.go.eq_1"],
        }
        or source["sha256"] != pack["source_stream_sha256"]
        or sha256(source_path) != source["sha256"]
        or source["declarations_admitted"] != 183
        or source["axioms"] != []
        or sha256(audit_path) != audit["sha256"]
        or sha256(receipt_path) != composition["receipt_file_sha256"]
        or stat.S_IMODE(source_path.stat().st_mode) != 0o444
        or stat.S_IMODE(audit_path.stat().st_mode) != 0o444
        or stat.S_IMODE(receipt_path.stat().st_mode) != 0o444
        or external["target"]["sha256"] != manifest["source"]["stream_sha256"]
        or external["target"]["axioms"] != []
        or composition["receipt_sha256"] != pack["composition_receipt_sha256"]
        or composition["source_closure_count"] != pack["source_closure_count"]
        or composition["source_closure_count"] != 183
        or composition["reused_declarations"] != pack["reused_declarations"]
        or composition["reused_declarations"] != 181
        or composition["added_theorems"] != list(pack["added_theorems"])
        or composition["added_axiom_footprints"]
        != {name: [] for name in pack["added_theorems"]}
        or external["authority"]
        != {
            "proof_bodies_displayed": False,
            "proof_search_invocations": 0,
            "imported_declarations_admitted": 444,
            "composed_theorem_admissions_including_replay": 4,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("official equation pack identity or authority changed")
    receipt = load(receipt_path)
    if (
        receipt["schema_version"] != composition["receipt_schema"]
        or receipt["roots"] != external["generation"]["roots"]
        or receipt["receipt_sha256"] != composition["receipt_sha256"]
        or len(receipt["source_closure"]) != composition["source_closure_count"]
        or len(receipt["reused_declarations"]) != composition["reused_declarations"]
        or [row["name"] for row in receipt["added_theorems"]]
        != composition["added_theorems"]
        or receipt["target_environment_sha256_before"]
        != composition["target_environment_sha256_before"]
        or receipt["target_environment_sha256_after"]
        != composition["target_environment_sha256_after"]
    ):
        raise PlanError("official equation pack receipt changed")
    for row in receipt["added_theorems"]:
        expected = pack["added_theorems"][row["name"]]
        if (
            row["source_declaration_sha256"] != expected["declaration_sha256"]
            or row["target_declaration_sha256"] != expected["declaration_sha256"]
            or row["axiom_footprint"] != expected["axiom_footprint"]
            or row["axiom_footprint"] != []
        ):
            raise PlanError(f"official equation theorem changed for {row['name']}")


def validate_nat_mod_invariant_pack(manifest: dict[str, Any]) -> None:
    pack = manifest["nat_mod_invariant_pack"]
    manifest_path = pathlib.Path(pack["manifest"])
    pack_dir = manifest_path.parent
    expected_files = {
        "autogenesis_nat_mod_invariant.lean",
        "manifest.json",
        "nat-mod-invariant.ndjson",
        "specialization.json",
        "theorem-audit.txt",
    }
    if (
        sha256(manifest_path) != pack["manifest_sha256"]
        or stat.S_IMODE(pack_dir.stat().st_mode) != 0o555
        or {path.name for path in pack_dir.iterdir()} != expected_files
        or any(
            stat.S_IMODE((pack_dir / name).stat().st_mode) != 0o444
            for name in expected_files
        )
    ):
        raise PlanError("Nat.mod invariant pack changed or is mutable")

    external = load(manifest_path)
    authored = external["authored_source"]
    export = external["export"]
    audit = external["audit"]
    target = external["target"]
    tool = external["specialization_tool"]
    result = external["result"]
    authored_path = pack_dir / authored["pack_path"]
    export_path = pack_dir / export["path"]
    audit_path = pack_dir / audit["path"]
    result_path = pack_dir / result["path"]
    if (
        external.get("schema_version") != 1
        or external.get("kind")
        != "axeyum-lean430-nat-mod-invariant-specialization-pack"
        or external.get("lean_version") != manifest["source"]["lean_version"]
        or external.get("lean_githash") != manifest["source"]["lean_githash"]
        or external.get("repository_commit")
        != pack["implementation_commit"][:12]
        or authored["repository_path"]
        != "scripts/lean/autogenesis_nat_mod_invariant.lean"
        or authored["module"] != "AutogenesisNatModInvariant"
        or authored["root"] != "Axeyum.Autogenesis.modSucc_dvd_iff"
        or authored["sha256"] != pack["authored_source_sha256"]
        or sha256(authored_path) != authored["sha256"]
        or git_blob_sha256(pack["implementation_commit"], authored["repository_path"])
        != authored["sha256"]
        or authored["bytes"] != authored_path.stat().st_size
        or authored["lines"] != len(authored_path.read_text().splitlines())
        or export["sha256"] != pack["source_stream_sha256"]
        or sha256(export_path) != export["sha256"]
        or export["bytes"] != export_path.stat().st_size
        or export["lines"] != len(export_path.read_bytes().splitlines())
        or export["declarations_admitted"] != 211
        or export["axioms"] != []
        or audit["tool"]
        != "crates/axeyum-lean-import/examples/lean4export_import.rs"
        or audit["tool_sha256"]
        != git_blob_sha256(pack["implementation_commit"], audit["tool"])
        or sha256(audit_path) != audit["sha256"]
        or target["sha256"] != manifest["source"]["stream_sha256"]
        or sha256(pathlib.Path(target["path"])) != target["sha256"]
        or target["declarations_admitted"] != 261
        or target["axioms"] != []
        or tool["path"]
        != "crates/axeyum-lean-import/examples/nat_mod_invariant_specialization.rs"
        or tool["sha256"] != pack["specialization_tool_sha256"]
        or git_blob_sha256(pack["implementation_commit"], tool["path"])
        != tool["sha256"]
        or tool["library_path"]
        != "crates/axeyum-lean-import/src/theorem_specialization.rs"
        or tool["library_sha256"] != pack["specialization_library_sha256"]
        or git_blob_sha256(pack["implementation_commit"], tool["library_path"])
        != tool["library_sha256"]
        or sha256(result_path) != result["sha256"]
        or external["authority"]
        != {
            "proof_source_authored_by_searcher": True,
            "proof_source_is_trusted": False,
            "proof_terms_independently_admitted": True,
            "specialization_independently_admitted": True,
            "native_type_compatibility_checked": True,
            "proof_import_declarations_admitted": 211,
            "target_import_declarations_admitted": 261,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("Nat.mod invariant pack identity or authority changed")

    expected_theorems = {
        "Axeyum.Autogenesis.modCoreGo_invariant": (
            "d2c5b7f22ba8be2944cf3a4a864250b40410de6bda746b026023f555efa66b14"
        ),
        "Axeyum.Autogenesis.modSucc_invariant": (
            "3edbf74b7eb077da928a8ca499823419449791a72e654b885e1920e15df2952e"
        ),
        "Axeyum.Autogenesis.modSucc_dvd_iff": (
            "cc6cb4ce64e5c30b3f8ff36cbc5c6c14f19dae1b57c51a6df095a07e9851a43e"
        ),
    }
    audit_text = audit_path.read_text()
    if set(audit["theorems"]) != set(expected_theorems):
        raise PlanError("Nat.mod invariant theorem set changed")
    for theorem, identity in expected_theorems.items():
        row = audit["theorems"][theorem]
        if (
            row != {"declaration_sha256": identity, "axiom_footprint": []}
            or f"name={theorem}|identity={identity}|axiom_free=true|"
            not in audit_text
            or "|axiom_footprint=none|" not in audit_text
        ):
            raise PlanError(f"Nat.mod invariant theorem changed for {theorem}")
    if audit_text.count("|axioms=none|") != 3 or "axiom_free=false" in audit_text:
        raise PlanError("Nat.mod invariant audit coverage changed")

    observed = load(result_path)
    specialization = observed["specialization"]
    tracked_target = pack["target"]
    if (
        observed.get("schema_version") != 1
        or observed.get("kind") != "axeyum-nat-mod-invariant-specialization"
        or observed.get("lean_version") != manifest["source"]["lean_version"]
        or observed["generic_composition"]["receipt_sha256"]
        != pack["generic_composition_receipt_sha256"]
        or observed["generic_composition"]["source_closure"] != 211
        or observed["generic_composition"]["added_theorems"] != 16
        or observed["helper_composition"]["receipt_sha256"]
        != pack["helper_composition_receipt_sha256"]
        or observed["helper_composition"]["roots"]
        != ["Nat.dvd_add_iff_right", "Nat.sub_add_cancel", "Nat.add_comm"]
        or observed["helper_composition"]["source_closure"] != 49
        or observed["helper_composition"]["added_theorems"] != 21
        or specialization["source"]
        != "Axeyum.Autogenesis.modSucc_dvd_iff"
        or specialization["arguments"]
        != [
            "Nat.dvd",
            "Nat.dvd_add_iff_right",
            "Nat.sub_add_cancel",
            "Nat.add_comm",
        ]
        or specialization["target"] != tracked_target["name"]
        or specialization["target_sha256"]
        != tracked_target["declaration_sha256"]
        or specialization["specialized_type_shape_sha256"]
        != tracked_target["type_shape_sha256"]
        or specialization["native_type_shape_sha256"]
        != tracked_target["native_type_shape_sha256"]
        or specialization["native_type_compatibility"] != "kernel-type-shape"
        or specialization["axiom_footprint"] != tracked_target["axiom_footprint"]
        or specialization["axiom_footprint"] != []
        or specialization["receipt_sha256"]
        != pack["specialization_receipt_sha256"]
    ):
        raise PlanError("Nat.mod invariant specialization result changed")


def validate(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = load(MANIFEST) if manifest is None else manifest
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-coprime-premise-plan"
        or manifest.get("state")
        != "target-nat-dvd-mod-iff-specialized-axiom-free"
    ):
        raise PlanError("manifest identity changed")
    source = manifest["source"]
    if sha256(pathlib.Path(source["stream"])) != source["stream_sha256"]:
        raise PlanError("source stream changed")
    implementation = manifest["implementation"]
    if (
        implementation["evidence_commit"]
        != "f099a4a37d58b0d976d73a564cb13245462c8b11"
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
    evidence_commit = implementation["evidence_commit"]
    if git_blob_sha256(evidence_commit, probe["tool"]) != probe["tool_sha256"]:
        raise PlanError("composition probe changed")
    if git_blob_sha256(evidence_commit, probe["api"]) != probe["api_sha256"]:
        raise PlanError("composition API changed")
    observation_path = pathlib.Path(probe["observation"])
    if (
        sha256(observation_path) != probe["observation_sha256"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_path.parent.stat().st_mode) != 0o555
    ):
        raise PlanError("composition observation changed or is mutable")
    observation = load(observation_path)
    expected_division_names = [
        "HMod",
        "HMod.hMod",
        "HMod.mk",
        "HMod.rec",
        "Nat.div.go.match_1",
        "Nat.div_rec_fuel_lemma",
        "Nat.div_rec_lemma",
        "Nat.instMod",
        "Nat.mod",
        "Nat.mod.match_1",
        "Nat.modCore",
        "Nat.modCore.go",
        "Nat.modCore.go._f",
        "Nat.modCoreGo_lt",
        "Nat.modCore_lt",
        "Nat.mod_lt",
    ]
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
        or probe["imported_division_declaration_names"] != expected_division_names
        or observation["source"]["imported_division_declaration_names"]
        != expected_division_names
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
        or hashlib.sha256(negative["error"].encode()).hexdigest()
        != composition_result["negative_control_error_sha256"]
        or composition_result["negative_control_first_rejected"]
        not in negative["error"]
        or composition_result["negative_control_error_kind"]
        not in negative["error"]
        or "ExprId" in negative["error"]
        or any(
            marker not in negative["error"]
            for marker in [
                "expected:",
                "got:",
                "expected_whnf:",
                "got_whnf:",
                "first_expected:",
                "first_got:",
            ]
        )
        or negative["source_closure_count"]
        != composition_result["negative_control_source_closure_count"]
        or negative["source_closure_count"] != 92
        or negative["reused_nat_div_mod_exec_direct_consumers"]
        != composition_result[
            "negative_control_reused_nat_div_mod_exec_direct_consumers"
        ]
        or negative["reused_nat_div_mod_exec_direct_consumers"] != ["Nat.mod_lt"]
        or negative["missing_nat_div_mod_exec_direct_consumers"]
        != composition_result[
            "negative_control_missing_nat_div_mod_exec_direct_consumers"
        ]
        or negative["missing_nat_div_mod_exec_direct_consumers"]
        != ["Nat.dvd_mod_iff"]
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
    validate_official_support_audit(manifest)
    validate_official_equation_pack(manifest)
    validate_nat_mod_invariant_pack(manifest)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_NAT_FIB_COPRIME_PREMISE_PLAN_OK|"
            f"required={len(manifest['proof_plan']['required_native_declarations'])}|"
            "present=0|exact=11|compatible=Nat.mod_lt,Acc,Nat.dvd_mod_iff|"
            "next=target-leaf-cut|"
            "submissions=24|evaluation=0|writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, PlanError) as error:
        print(f"autogenesis-nat-fib-coprime-premise-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
