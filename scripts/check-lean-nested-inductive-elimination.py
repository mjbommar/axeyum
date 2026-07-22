#!/usr/bin/env python3
"""Validate the TL2.14 M0 nested-inductive source/wire freeze fail closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-nested-inductive-elimination-v1.json"
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

from prototype_lean4export_census import census_bytes  # noqa: E402


SCHEMA = "axeyum-lean-nested-inductive-elimination-v1"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "decision",
    "plan",
    "baseline",
    "pins",
    "resource_policy",
    "commands",
    "semantic_contract",
    "positive_source",
    "negative_source",
    "streams",
    "case_ids",
    "mutation_ids",
    "generated_grammar",
    "mandatory_controls",
    "stop_condition_ids",
    "claim_limits",
    "next",
}
EXPECTED_PINS = {
    "lean": {
        "toolchain": "leanprover/lean4:v4.30.0",
        "version": "4.30.0",
        "git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
    },
    "lean4export": {
        "version": "v4.30.0",
        "git_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "format": "3.1.0",
    },
}
EXPECTED_RESOURCES = {
    "runner": "systemd-run --user --scope",
    "memory_high": "3G",
    "memory_max": "4G",
    "memory_swap_max": "512M",
    "lean_jobs": 1,
    "rust_jobs": 1,
    "rust_test_threads": 1,
    "per_stream_max_bytes": 1_048_576,
    "aggregate_stream_max_bytes": 2_097_152,
}
EXPECTED_RUNNER = [
    "systemd-run",
    "--user",
    "--scope",
    "--quiet",
    "-p",
    "MemoryHigh=3G",
    "-p",
    "MemoryMax=4G",
    "-p",
    "MemorySwapMax=512M",
]
EXPECTED_POSITIVE_COMPILE = [
    "/usr/bin/time",
    "-v",
    "<pinned-lean>",
    "-j1",
    "-o",
    "target/tl214-m0-run<1|2>/AxeyumNestedInductiveComputation.olean",
    "docs/plan/fixtures/lean-v4.30-nested-inductive-computation.lean",
]
EXPECTED_NEGATIVE_COMPILE = [
    "/usr/bin/time",
    "-v",
    "<pinned-lean>",
    "-j1",
    "docs/plan/fixtures/lean-v4.30-nested-inductive-negative.lean",
]
EXPECTED_EXPORT = [
    "/usr/bin/time",
    "-v",
    "env",
    "PATH=<pinned-lean-bin>:$PATH",
    "LEAN_PATH=<run-directory>",
    "<pinned-lean4export>",
    "AxeyumNestedInductiveComputation",
    "--",
    "<selected-root>",
]
EXPECTED_SEMANTICS = {
    "discovery_head": (
        "an already admitted inductive constant applied to at least its full "
        "parameter prefix"
    ),
    "discovery_occurrence": (
        "at least one container parameter structurally contains an original or "
        "queued auxiliary family"
    ),
    "local_variable_rule": (
        "every nested container parameter has zero loose bound variables"
    ),
    "deduplication": (
        "structural equality after replacing reopened outer parameters"
    ),
    "container_copy": (
        "copy every family and constructor in the existing container mutual group"
    ),
    "fixed_point": (
        "queue copied constructors and repeat discovery until no nested applications "
        "remain"
    ),
    "expanded_check": "one existing TL2.11-TL2.13 atomic mutual-group admission",
    "restoration": (
        "replace temporary auxiliary families, constructors, and recursor references "
        "in every published type and rule"
    ),
    "publication": (
        "original families and constructors, main recursors, and deterministic "
        "first-family .rec_N auxiliary recursors only"
    ),
    "wire_authority": (
        "derive numNested and all recursor contracts structurally before exact "
        "exporter comparison"
    ),
    "well_founded_boundary": (
        "pre-elaborated WellFounded.fix and Acc.rec terms are a passing core control; "
        "source recursion remains TL4.10"
    ),
}
EXPECTED_BASELINE = {
    "preregistration_revision": "def1000feed25f40d170a7fe95f9bbe0afa6dd21",
    "semantic_revision": "340cf7215c9371778fb08a1a2ff81ca68d10400b",
    "construct_matrix": {
        "path": "docs/plan/lean-official-construct-matrix-v1.json",
        "sha256_without_tl2_14_overlay": (
            "53ddf887ee068e4cf727bd22159f6195e7de743f3f2b4632694ed1797bfdec8f"
        ),
    },
    "nested_stream": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-construct-matrix-nested.ndjson"
        ),
        "sha256": "faabcde4553b0d597a768aedf35117d7fb4310d3dae052e2545e5b239277456e",
        "bytes": 23_418,
        "records": 409,
        "registered_outcome": (
            "ImportError::Malformed(line=248,message=single-family inductive must "
            "export one recursor)"
        ),
        "completed_import_published": False,
    },
    "well_founded_stream": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-construct-matrix-well-founded.ndjson"
        ),
        "sha256": "c1fc14097f9be381625846f13277edfd8294afd93c8e9cadd72c54d71e48e3c6",
        "bytes": 49_140,
        "records": 920,
        "registered_outcome": (
            "CompletedImport(names=160,levels=5,expressions=731,records=23,"
            "declarations=35,axioms=0)"
        ),
    },
    "declaration_identity_version": "axeyum-lean-declaration-identity-v1",
}
EXPECTED_POSITIVE_SOURCE = {
    "path": "docs/plan/fixtures/lean-v4.30-nested-inductive-computation.lean",
    "sha256": "c5cadeaf11302d5ca9b5a60b2a3b72998ad994e7eb176ddc5de40ebfc05c475d",
    "bytes": 2_917,
    "lines": 98,
    "module": "AxeyumNestedInductiveComputation",
    "compile_runs": 2,
    "compile_exit_statuses": [0, 0],
    "compile_elapsed_ms": [290, 240],
    "compile_max_rss_kib": [462_832, 462_920],
    "olean_sha256": "d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2",
}
EXPECTED_ROOTS = [
    {
        "id": "auxiliary-recursion-computation",
        "selected_root": (
            "AxeyumNestedInductiveComputation.roseAuxiliaryRecursorComputes"
        ),
        "consumer": "AxeyumNestedInductiveComputation.roseSize",
        "transition": "Rose.rec -> Rose.rec_1 -> Rose.rec -> Rose.rec_1",
        "expected_normal_form": (
            "MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))"
        ),
    },
    {
        "id": "indexed-container-computation",
        "selected_root": (
            "AxeyumNestedInductiveComputation.indexedAuxiliaryRecursorComputes"
        ),
        "consumer": "AxeyumNestedInductiveComputation.indexedRoseSize",
        "transition": (
            "IndexedRose.rec -> IndexedRose.rec_1 -> IndexedRose.rec -> "
            "IndexedRose.rec_1"
        ),
        "expected_normal_form": (
            "MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))"
        ),
    },
    {
        "id": "repeated-container-reuse-computation",
        "selected_root": (
            "AxeyumNestedInductiveComputation."
            "repeatedContainerReusesAuxiliaryRecursor"
        ),
        "consumer": "AxeyumNestedInductiveComputation.repeatRoseSize",
        "transition": (
            "RepeatRose.rec -> one reused RepeatRose.rec_1 -> RepeatRose.rec on "
            "both heads"
        ),
        "expected_normal_form": (
            "MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ "
            "(MiniNat.succ MiniNat.zero))))"
        ),
    },
]
EXPECTED_NEGATIVE_SOURCE = {
    "path": "docs/plan/fixtures/lean-v4.30-nested-inductive-negative.lean",
    "sha256": "aedb42cf5d4b8eccb24252ffeaab33ce10cdd5a21bf1ad36290e1ab87387e398",
    "bytes": 260,
    "lines": 11,
    "compile_runs": 2,
    "compile_exit_statuses": [1, 1],
    "compile_elapsed_ms": [150, 150],
    "compile_max_rss_kib": [445_964, 445_780],
    "diagnostic_line": 8,
    "diagnostic": (
        "(kernel) invalid nested inductive datatype "
        "'AxeyumNestedInductiveNegative.Box', nested inductive datatypes "
        "parameters cannot contain local variables."
    ),
}
PREFIX = "AxeyumNestedInductiveComputation."


def _family(name: str, constructor: str) -> list[dict[str, Any]]:
    return [
        {
            "name": PREFIX + name,
            "num_params": 1,
            "num_indices": 0,
            "num_nested": 1,
            "is_rec": True,
            "is_reflexive": False,
            "constructors": [PREFIX + constructor],
        }
    ]


def _recursor(
    name: str,
    indices: int,
    constructors: list[str],
    nfields: list[int],
) -> dict[str, Any]:
    return {
        "name": PREFIX + name,
        "num_params": 1,
        "num_indices": indices,
        "num_motives": 2,
        "num_minors": 3,
        "rule_constructors": [PREFIX + item for item in constructors],
        "rule_nfields": nfields,
    }


EXPECTED_STREAMS = {
    "auxiliary-recursion-computation": {
        "path": (
            "docs/plan/fixtures/lean4export-v4.30-nested-aux-computation.ndjson"
        ),
        "selected_root": PREFIX + "roseAuxiliaryRecursorComputes",
        "sha256": "36fb9c6f85a99a7d6d1f6329a2cfe5265b148f0138e979d6d391d9e8879e07de",
        "bytes": 36_706,
        "records": 642,
        "elapsed_ms": [1_110, 320],
        "max_rss_kib": [668_176, 672_492],
        "counts": (122, 8, 494, 17),
        "blockers": ["expr-projection", "inductive-nested"],
        "family_order": [PREFIX + "Rose"],
        "families": _family("Rose", "Rose.node"),
        "wire_recursor_order": [PREFIX + "Rose.rec_1", PREFIX + "Rose.rec"],
        "recursors": [
            _recursor(
                "Rose.rec_1",
                0,
                ["NestList.nil", "NestList.cons"],
                [0, 2],
            ),
            _recursor("Rose.rec", 0, ["Rose.node"], [2]),
        ],
    },
    "indexed-container-computation": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-nested-indexed-computation.ndjson"
        ),
        "selected_root": PREFIX + "indexedAuxiliaryRecursorComputes",
        "sha256": "a14ca423410c4f0a86c2a2cea193e5a76bd91428e348402b3dd32e1603481429",
        "bytes": 40_119,
        "records": 714,
        "elapsed_ms": [330, 310],
        "max_rss_kib": [672_208, 674_308],
        "counts": (134, 8, 554, 17),
        "blockers": [
            "expr-projection",
            "inductive-nested",
            "inductive-recursive-indexed",
        ],
        "family_order": [PREFIX + "IndexedRose"],
        "families": _family("IndexedRose", "IndexedRose.node"),
        "wire_recursor_order": [
            PREFIX + "IndexedRose.rec_1",
            PREFIX + "IndexedRose.rec",
        ],
        "recursors": [
            _recursor(
                "IndexedRose.rec_1",
                1,
                ["NestVec.nil", "NestVec.cons"],
                [0, 3],
            ),
            _recursor("IndexedRose.rec", 0, ["IndexedRose.node"], [3]),
        ],
    },
    "repeated-container-reuse-computation": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-nested-repeated-container-computation.ndjson"
        ),
        "selected_root": PREFIX + "repeatedContainerReusesAuxiliaryRecursor",
        "sha256": "af369edb2d9e0346a5457ba4c9cde6f3030ca08002dc931c5fb26709e0f74344",
        "bytes": 37_771,
        "records": 666,
        "elapsed_ms": [290, 330],
        "max_rss_kib": [674_520, 673_784],
        "counts": (122, 8, 518, 17),
        "blockers": ["expr-projection", "inductive-nested"],
        "family_order": [PREFIX + "RepeatRose"],
        "families": _family("RepeatRose", "RepeatRose.node"),
        "wire_recursor_order": [
            PREFIX + "RepeatRose.rec",
            PREFIX + "RepeatRose.rec_1",
        ],
        "recursors": [
            _recursor("RepeatRose.rec", 0, ["RepeatRose.node"], [3]),
            _recursor(
                "RepeatRose.rec_1",
                0,
                ["NestList.nil", "NestList.cons"],
                [0, 2],
            ),
        ],
    },
}
EXPECTED_CASE_IDS = (
    "one-family-list-container",
    "repeated-identical-container",
    "distinct-container-parameters",
    "container-mutual-group",
    "outer-mutual-self-cross-nested",
    "zero-one-two-outer-parameters",
    "zero-one-two-container-indices",
    "higher-order-nested-result",
    "one-level-expansion",
    "two-level-expansion",
    "type-result",
    "prop-result-restricted",
    "empty-container-family",
    "mixed-recursive-owner",
    "incomplete-parameter-prefix",
    "loose-container-parameter",
    "negative-container-parameter-occurrence",
    "fresh-name-collision",
    "late-restoration-failure",
)
EXPECTED_MUTATION_IDS = (
    "container-family-order",
    "specialized-parameter",
    "auxiliary-reuse-duplicate",
    "fresh-name-index",
    "copied-constructor-owner",
    "copied-constructor-index",
    "copied-constructor-type",
    "motive-order",
    "minor-order",
    "recursive-target",
    "restored-recursor-reference",
    "restored-rule-constructor",
    "rule-nfields",
    "num-nested",
    "recursor-count",
    "recursor-order",
    "recursor-name",
    "index-count",
    "universe-parameters",
    "unsafe-k-flags",
    "late-publication",
)
EXPECTED_GRAMMAR = {
    "seed_policy": "fixed and committed at M3 before the first generated run",
    "minimum_unique_cases": 640,
    "outer_group_sizes": "1..3",
    "container_group_sizes": "1..3",
    "outer_parameters": "0..2 including dependent pairs",
    "container_parameters": "1..3",
    "container_indices": "0..2",
    "constructors_per_family": "0..3",
    "fields_per_constructor": "0..5",
    "nested_applications": "1..3 repeated or structurally distinct",
    "nested_depth": "1..2",
    "recursive_targets": ["self", "outer-sibling", "container-auxiliary"],
    "result_sorts": ["Type", "Prop-restricted"],
    "classifications": ["accepted", "typed-reject"],
    "required_repetitions": 2,
    "summary_identity": "byte-identical",
}
EXPECTED_CONTROLS = {
    "mutual_manifest": "docs/plan/lean-mutual-inductive-groups-v1.json",
    "mutual_generated_cases": 720,
    "recursive_manifest": "docs/plan/lean-recursive-induction-hypotheses-v1.json",
    "recursive_generated_cases": 768,
    "strict_positivity_manifest": "docs/plan/lean-strict-positivity-v1.json",
    "strict_positivity_generated_cases": 840,
    "official_construct_matrix": "docs/plan/lean-official-construct-matrix-v1.json",
    "well_founded_admitted_declarations": 35,
    "well_founded_axioms": 0,
    "transactional_import": "CompletedImport only after full-stream success",
    "declaration_identity_version": "axeyum-lean-declaration-identity-v1",
}
EXPECTED_STOP_IDS = (
    "lean-kernel-boundary-disagreement",
    "nested-discovery-rule-disagreement",
    "container-group-copy-incomplete",
    "expanded-group-needs-second-checker",
    "restoration-trusts-exporter-metadata",
    "temporary-auxiliary-leaks",
    "restored-surface-does-not-infer",
    "identity-v1-must-change",
    "official-stream-not-reproducible",
    "auxiliary-recursor-not-computed",
    "failure-publishes-environment-or-import",
    "generated-summary-invalid",
    "retained-control-drift",
    "resource-cap-exceeded-or-killed",
    "unrelated-dirty-overlap",
)
EXPECTED_CLAIMS = {
    "positive_official_source": "accepted-twice",
    "negative_official_source": "diagnostic-matched-twice",
    "olean_reproducibility": "byte-identical-twice",
    "official_export": "byte-identical-twice-per-root",
    "official_wire_inventory": "frozen",
    "axeyum_import_new_streams": "not-run",
    "axeyum_admission_new_streams": "not-run",
    "axeyum_computation_new_streams": "not-run",
    "nested_kernel_support": "not-yet-implemented",
    "well_founded_source_elaboration": "not-implemented",
    "full_lean_kernel_parity": "not-claimed",
    "lean_ecosystem_parity": "not-claimed",
}
EXPECTED_NEXT = (
    "M1: correct nested recursor-count diagnostic preflight without admission or "
    "product credit"
)


def sha256(path: Path) -> str:
    """Return one file's SHA-256."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def construct_matrix_baseline_sha256(path: Path) -> str:
    """Hash the M0 matrix view while permitting a later TL2.14 overlay."""

    registration = json.loads(path.read_text(encoding="utf-8"))
    registration.pop("tl2_14_update", None)
    encoded = (json.dumps(registration, indent=2) + "\n").encode()
    return hashlib.sha256(encoded).hexdigest()


def load_manifest() -> dict[str, Any]:
    """Load the committed M0 manifest."""

    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def _find_group(inventory: dict[str, Any], family_order: list[str]) -> dict[str, Any]:
    for group in inventory["inductive_groups"]:
        if [row["name"] for row in group["types"]] == family_order:
            return group
    return {}


def _observed_families(group: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "name": row["name"],
            "num_params": row["num_params"],
            "num_indices": row["num_indices"],
            "num_nested": row["num_nested"],
            "is_rec": row["is_rec"],
            "is_reflexive": row["is_reflexive"],
            "constructors": row["constructor_names"],
        }
        for row in group.get("types", [])
    ]


def _observed_recursors(group: dict[str, Any]) -> list[dict[str, Any]]:
    keys = (
        "name",
        "num_params",
        "num_indices",
        "num_motives",
        "num_minors",
        "rule_constructors",
        "rule_nfields",
    )
    return [{key: row[key] for key in keys} for row in group.get("recursors", [])]


def _validate_file_registration(
    row: dict[str, Any], expected: dict[str, Any], label: str, failures: list[str]
) -> None:
    if row != expected:
        failures.append(f"{label} registration drift")
    path = ROOT / str(row.get("path", ""))
    if not path.is_file():
        failures.append(f"{label} missing")
        return
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != row.get("sha256"):
        failures.append(f"{label} hash drift")
    if len(raw) != row.get("bytes"):
        failures.append(f"{label} byte count drift")
    if len(raw.splitlines()) != row.get("lines"):
        failures.append(f"{label} line count drift")


def _validate_construct_outcomes(path: Path, failures: list[str]) -> None:
    try:
        matrix = json.loads(path.read_text(encoding="utf-8"))
        outcomes = matrix["tl2_12_update"]["outcomes"]
    except (KeyError, TypeError, json.JSONDecodeError, OSError):
        failures.append("construct matrix outcome overlay missing or malformed")
        return
    if "tl2_14_update" not in matrix:
        failures.append("construct matrix TL2.14 update missing")
    nested = outcomes.get("nested")
    expected_nested = {
        "variant": "Malformed",
        "runs": 2,
        "report": None,
        "line": 248,
        "code": None,
        "message": "single-family inductive must export one recursor",
    }
    if nested != expected_nested:
        failures.append("registered nested baseline outcome drift")
    well_founded = outcomes.get("well-founded")
    if not isinstance(well_founded, dict):
        failures.append("registered well-founded baseline outcome missing")
        return
    report = well_founded.get("report")
    expected_report = {
        "names": 160,
        "levels": 5,
        "expressions": 731,
        "declaration_records": 23,
        "admitted_declarations": 35,
        "axioms": 0,
        "axiom_identities": 0,
        "declaration_identities": 35,
    }
    if (
        well_founded.get("variant") != "CompletedImport"
        or well_founded.get("runs") != 2
        or report != expected_report
        or any(well_founded.get(key) is not None for key in ("line", "code", "message"))
    ):
        failures.append("registered well-founded baseline outcome drift")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    """Return every fail-closed TL2.14 M0 registration violation."""

    failures: list[str] = []
    if set(data) != TOP_LEVEL_KEYS:
        failures.append("top-level fields drift or premature product observation")
    if data.get("schema") != SCHEMA:
        failures.append("schema drift")
    if data.get("stage") != "source-wire-frozen":
        failures.append("M0 stage must remain source-wire-frozen")
    if data.get("date") != "2026-07-22":
        failures.append("registration date drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0355-preregister-lean-nested-inductive-elimination.md"
    ):
        failures.append("decision path drift")
    if data.get("plan") != (
        "docs/plan/lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md"
    ):
        failures.append("plan path drift")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("tool pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")
    if data.get("semantic_contract") != EXPECTED_SEMANTICS:
        failures.append("semantic contract drift")
    if data.get("claim_limits") != EXPECTED_CLAIMS:
        failures.append("claim limits drift or premature product credit")

    commands = data.get("commands", {})
    if commands.get("resource_runner_argv") != EXPECTED_RUNNER:
        failures.append("resource runner argv drift")
    if commands.get("positive_compile_argv") != EXPECTED_POSITIVE_COMPILE:
        failures.append("positive Lean compile argv drift")
    if commands.get("negative_compile_argv") != EXPECTED_NEGATIVE_COMPILE:
        failures.append("negative Lean compile argv drift")
    if commands.get("lean4export_argv_template") != EXPECTED_EXPORT:
        failures.append("lean4export argv drift")
    if set(commands) != {
        "working_directory",
        "resource_runner_argv",
        "positive_compile_argv",
        "negative_compile_argv",
        "lean4export_argv_template",
    }:
        failures.append("command fields drift")

    baseline = data.get("baseline", {})
    if baseline != EXPECTED_BASELINE:
        failures.append("baseline identity/outcome contract drift")
    matrix_row = baseline.get("construct_matrix", {})
    matrix_path = ROOT / str(matrix_row.get("path", ""))
    if not matrix_path.is_file():
        failures.append("baseline artifact missing: construct_matrix")
    else:
        if construct_matrix_baseline_sha256(matrix_path) != matrix_row.get(
            "sha256_without_tl2_14_overlay"
        ):
            failures.append("baseline artifact hash drift: construct_matrix")
        _validate_construct_outcomes(matrix_path, failures)
    for key in ("nested_stream", "well_founded_stream"):
        row = baseline.get(key, {})
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"baseline artifact missing: {key}")
            continue
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != row.get("sha256"):
            failures.append(f"baseline artifact hash drift: {key}")
        if len(raw) != row.get("bytes"):
            failures.append(f"baseline artifact byte count drift: {key}")
        if len(raw.splitlines()) != row.get("records"):
            failures.append(f"baseline artifact record count drift: {key}")

    positive = data.get("positive_source", {})
    if set(positive) != {*EXPECTED_POSITIVE_SOURCE, "roots"}:
        failures.append("positive source fields drift")
    _validate_file_registration(
        {key: positive.get(key) for key in EXPECTED_POSITIVE_SOURCE},
        EXPECTED_POSITIVE_SOURCE,
        "positive source",
        failures,
    )
    if positive.get("roots") != EXPECTED_ROOTS:
        failures.append("positive source roots or normal forms drift")
    negative = data.get("negative_source", {})
    _validate_file_registration(
        negative, EXPECTED_NEGATIVE_SOURCE, "negative source", failures
    )

    streams = data.get("streams", {})
    if tuple(streams) != tuple(EXPECTED_STREAMS):
        failures.append("stream population/order drift")
    total_bytes = 0
    for stream_id, expected in EXPECTED_STREAMS.items():
        row = streams.get(stream_id, {})
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"stream missing: {stream_id}")
            continue
        raw = path.read_bytes()
        observed = json.loads(json.dumps(census_bytes(raw, label=stream_id)))
        total_bytes += len(raw)
        for key in ("path", "selected_root", "sha256", "bytes", "records"):
            if row.get(key) != expected[key]:
                failures.append(f"stream {key} drift: {stream_id}")
        if observed["sha256"] != expected["sha256"]:
            failures.append(f"stream hash drift: {stream_id}")
        if observed["bytes"] != expected["bytes"]:
            failures.append(f"stream byte count drift: {stream_id}")
        if observed["records"] != expected["records"]:
            failures.append(f"stream record count drift: {stream_id}")
        if (
            not observed["declaration_names"]
            or observed["declaration_names"][-1] != expected["selected_root"]
        ):
            failures.append(f"selected root is not final declaration: {stream_id}")
        if row.get("export_runs") != 2 or row.get("byte_identical") is not True:
            failures.append(f"stream reproduction drift: {stream_id}")
        if row.get("elapsed_ms") != expected["elapsed_ms"]:
            failures.append(f"stream elapsed observation drift: {stream_id}")
        if row.get("max_rss_kib") != expected["max_rss_kib"]:
            failures.append(f"stream resource observation drift: {stream_id}")

        registered = row.get("inventory", {})
        observed_counts = tuple(
            observed[key] for key in ("names", "levels", "exprs", "decls")
        )
        registered_counts = tuple(
            registered.get(key)
            for key in ("names", "levels", "expressions", "declaration_records")
        )
        if observed_counts != expected["counts"] or registered_counts != expected[
            "counts"
        ]:
            failures.append(f"inventory count drift: {stream_id}")
        for key in ("format", "lean", "lean_githash"):
            if registered.get(key) != observed[key]:
                failures.append(f"inventory {key} drift: {stream_id}")
        if (
            registered.get("blockers") != expected["blockers"]
            or observed["blockers"] != expected["blockers"]
        ):
            failures.append(f"blocker inventory drift: {stream_id}")
        if registered.get("family_order") != expected["family_order"]:
            failures.append(f"family order drift: {stream_id}")
        group = _find_group(observed, expected["family_order"])
        if not group:
            failures.append(f"target nested group missing: {stream_id}")
        else:
            if _observed_families(group) != expected["families"]:
                failures.append(f"target family metadata drift: {stream_id}")
            if _observed_recursors(group) != expected["recursors"]:
                failures.append(f"target recursor metadata/order drift: {stream_id}")
        if registered.get("families") != expected["families"]:
            failures.append(f"registered family metadata drift: {stream_id}")
        if registered.get("wire_recursor_order") != expected["wire_recursor_order"]:
            failures.append(f"registered wire recursor order drift: {stream_id}")
        if registered.get("recursors") != expected["recursors"]:
            failures.append(f"registered recursor metadata drift: {stream_id}")

    if any(
        row.get("bytes", EXPECTED_RESOURCES["per_stream_max_bytes"] + 1)
        > EXPECTED_RESOURCES["per_stream_max_bytes"]
        for row in streams.values()
    ):
        failures.append("per-stream retention bound exceeded")
    if total_bytes > EXPECTED_RESOURCES["aggregate_stream_max_bytes"]:
        failures.append("aggregate retention bound exceeded")

    case_ids = tuple(data.get("case_ids", ()))
    if case_ids != EXPECTED_CASE_IDS:
        failures.append("case population/order drift")
    if len(case_ids) != len(set(case_ids)):
        failures.append("case IDs must be unique")
    mutation_ids = tuple(data.get("mutation_ids", ()))
    if mutation_ids != EXPECTED_MUTATION_IDS:
        failures.append("mutation population/order drift")
    if len(mutation_ids) != len(set(mutation_ids)):
        failures.append("mutation IDs must be unique")
    if data.get("generated_grammar") != EXPECTED_GRAMMAR:
        failures.append("generated grammar contract drift")
    if data.get("mandatory_controls") != EXPECTED_CONTROLS:
        failures.append("mandatory control contract drift")
    for key in (
        "mutual_manifest",
        "recursive_manifest",
        "strict_positivity_manifest",
        "official_construct_matrix",
    ):
        if not (ROOT / str(data.get("mandatory_controls", {}).get(key, ""))).is_file():
            failures.append(f"mandatory control missing: {key}")
    if tuple(data.get("stop_condition_ids", ())) != EXPECTED_STOP_IDS:
        failures.append("stop-condition population/order drift")
    if data.get("next") != EXPECTED_NEXT:
        failures.append("next milestone drift")
    return failures


def main() -> int:
    """CLI entry point."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed bytes")
    parser.parse_args()
    try:
        failures = validate_manifest(load_manifest())
    except (OSError, json.JSONDecodeError, UnicodeDecodeError) as error:
        print(f"lean nested inductive M0 invalid: {error}", file=sys.stderr)
        return 1
    if failures:
        for failure in failures:
            print(f"lean nested inductive M0 invalid: {failure}", file=sys.stderr)
        return 1
    print(
        "lean nested inductive M0 source/wire freeze valid: "
        "3 roots, 114596 bytes, exact negative diagnostic, "
        "no Axeyum product observations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
