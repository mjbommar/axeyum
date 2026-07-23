#!/usr/bin/env python3
"""Validate and render the offline TL0.6.5 normalization-contract authority."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-u2-normalization-contracts-v3.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-u2-normalization-contracts.md"
EXECUTION_EVIDENCE = ROOT / "docs" / "plan" / "lean-execution-evidence-v1.json"

CONTRACT_DOMAIN = "axeyum-lean-normalization-contract-v3"
PROJECTION_DOMAIN = "axeyum-lean-normalized-observation-v3"
AXIS_IDS = tuple(f"A{index}" for index in range(12))
CONTRACT_IDS = (
    "lean-process-harness-v3",
    "lean-parser-macro-v3",
    "lean-elaboration-v3",
    "lean-kernel-assurance-v3",
    "lean-module-cache-v3",
    "lean-tactic-v3",
    "lean-compiler-runtime-v3",
    "lean-server-rpc-v3",
    "lean-lake-project-v3",
    "lean-mathlib-ecosystem-v3",
)
TERMINATION_CLASSES = (
    "exited",
    "signaled",
    "wall-timeout",
    "cpu-timeout",
    "memory-limit",
    "pids-limit",
    "disk-limit",
    "cancelled",
    "runner-lost",
    "launch-failed",
    "preflight-invalid",
    "unknown-termination",
)
ADMISSION_CLASSES = ("admitted", "rejected", "declined")
IGNORED_SCHEMAS = (
    ("collector_sequence", "nonnegative-integer"),
    ("evidence_storage_path", "nonempty-string"),
)


def sha256_fields(*names: str) -> tuple[tuple[str, str, tuple[str, ...]], ...]:
    return tuple((name, "sha256", ()) for name in names)


def enum_field(
    name: str, values: tuple[str, ...]
) -> tuple[str, str, tuple[str, ...]]:
    return (name, "enum", values)


EXPECTED_CONTRACTS = {
    "lean-process-harness-v3": {
        "layer": "process-harness",
        "applicable_axes": ("A0", "A11"),
        "compared_fields": sha256_fields(
            "cleanup_state_sha256",
            "completion_state_sha256",
            "declared_effects_sha256",
            "expected_exit_policy_sha256",
            "stderr_bytes_sha256",
            "stdout_bytes_sha256",
        )
        + (enum_field("termination_class", TERMINATION_CLASSES),),
    },
    "lean-parser-macro-v3": {
        "layer": "parser-macro",
        "applicable_axes": ("A3",),
        "compared_fields": sha256_fields(
            "macro_expansion_sha256",
            "recovery_nodes_sha256",
            "scope_hygiene_sha256",
            "source_spans_sha256",
            "syntax_tree_sha256",
        ),
    },
    "lean-elaboration-v3": {
        "layer": "elaboration",
        "applicable_axes": ("A4",),
        "compared_fields": sha256_fields(
            "core_terms_sha256",
            "declarations_sha256",
            "diagnostics_sha256",
            "environment_extensions_sha256",
            "inferred_types_sha256",
            "info_trees_sha256",
        ),
    },
    "lean-kernel-assurance-v3": {
        "layer": "kernel-assurance",
        "applicable_axes": ("A1", "A9"),
        "compared_fields": (
            enum_field("admission_class", ADMISSION_CLASSES),
        )
        + sha256_fields(
            "axiom_trust_closure_sha256",
            "declaration_identity_sha256",
            "definitional_equality_sha256",
            "dependency_identity_sha256",
            "independent_replay_sha256",
            "inferred_type_sha256",
            "normal_form_sha256",
        ),
    },
    "lean-module-cache-v3": {
        "layer": "module-cache",
        "applicable_axes": ("A2", "A6", "A9"),
        "compared_fields": sha256_fields(
            "artifact_identity_sha256",
            "effective_import_closure_sha256",
            "environment_parts_sha256",
            "initialization_sha256",
            "invalidation_sha256",
            "raw_import_closure_sha256",
            "visibility_sha256",
        ),
    },
    "lean-tactic-v3": {
        "layer": "tactic",
        "applicable_axes": ("A5",),
        "compared_fields": sha256_fields(
            "diagnostics_sha256",
            "final_goals_sha256",
            "independent_admission_sha256",
            "initial_goals_sha256",
            "metavariable_state_sha256",
            "theorem_term_sha256",
        ),
    },
    "lean-compiler-runtime-v3": {
        "layer": "compiler-runtime",
        "applicable_axes": ("A8",),
        "compared_fields": sha256_fields(
            "exception_sha256",
            "execution_route_sha256",
            "ffi_abi_sha256",
            "filesystem_effects_sha256",
            "frontend_result_sha256",
            "load_initialization_sha256",
            "stderr_bytes_sha256",
            "stdout_bytes_sha256",
        )
        + (enum_field("termination_class", TERMINATION_CLASSES),)
        + sha256_fields("value_sha256"),
    },
    "lean-server-rpc-v3": {
        "layer": "server-rpc",
        "applicable_axes": ("A7",),
        "compared_fields": sha256_fields(
            "cancellation_sha256",
            "diagnostics_sha256",
            "document_versions_sha256",
            "restart_sha256",
            "snapshots_sha256",
            "stale_result_suppression_sha256",
            "transcript_sha256",
            "widgets_sha256",
            "worker_watchdog_sha256",
        ),
    },
    "lean-lake-project-v3": {
        "layer": "lake-project",
        "applicable_axes": ("A6", "A11"),
        "compared_fields": sha256_fields(
            "artifacts_sha256",
            "cache_state_sha256",
            "command_exits_sha256",
            "incremental_offline_sha256",
            "manifests_sha256",
            "materialization_sha256",
            "network_policy_sha256",
            "revisions_sha256",
            "targets_facets_jobs_sha256",
            "workspace_graph_sha256",
        ),
    },
    "lean-mathlib-ecosystem-v3": {
        "layer": "mathlib-ecosystem",
        "applicable_axes": ("A10",),
        "compared_fields": sha256_fields(
            "axiom_trust_closure_sha256",
            "build_outcomes_sha256",
            "declaration_closure_sha256",
            "failure_classification_sha256",
            "module_outcomes_sha256",
            "runtime_tests_sha256",
            "tactic_results_sha256",
            "test_outcomes_sha256",
        ),
    },
}

TOP_LEVEL_FIELDS = {
    "schema",
    "target",
    "status",
    "implementation",
    "contracts",
    "summary",
    "claims",
}
CONTRACT_FIELDS = {
    "id",
    "layer",
    "applicable_axes",
    "compared_fields",
    "ignored_fields",
    "contract_sha256",
}
FIELD_NAME = re.compile(r"^[a-z][a-z0-9]*(?:_[a-z0-9]+)*$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class ObservationError(ValueError):
    """A selected observation violates its registered projection contract."""


def load_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_execution_evidence() -> dict[str, Any]:
    with EXECUTION_EVIDENCE.open(encoding="utf-8") as handle:
        return json.load(handle)


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def canonical_json_digest(domain: str, value: Any) -> str:
    digest = hashlib.sha256()
    digest.update(domain.encode("ascii"))
    digest.update(b"\0")
    digest.update(canonical_json_bytes(value))
    return digest.hexdigest()


def normalization_contract_digest(contract: dict[str, Any]) -> str:
    payload = {
        key: value for key, value in contract.items() if key != "contract_sha256"
    }
    return canonical_json_digest(CONTRACT_DOMAIN, payload)


def contract_map(data: dict[str, Any]) -> dict[str, dict[str, Any]]:
    contracts = data.get("contracts")
    if not isinstance(contracts, list):
        return {}
    return {
        str(contract.get("id")): contract
        for contract in contracts
        if isinstance(contract, dict)
    }


def field_schema_tuple(field: Any) -> tuple[Any, Any, tuple[Any, ...]]:
    if not isinstance(field, dict):
        return (None, None, ())
    values = field.get("values")
    return (
        field.get("field"),
        field.get("kind"),
        tuple(values) if isinstance(values, list) else (),
    )


def validate_observation_value(
    contract_id: str, field: dict[str, Any], value: Any
) -> None:
    name = str(field.get("field"))
    kind = field.get("kind")
    owner = f"{contract_id}.{name}"
    if kind == "sha256":
        if not isinstance(value, str) or not HEX64.fullmatch(value):
            raise ObservationError(f"{owner}: expected lowercase 64-hex SHA-256")
        return
    if kind == "enum":
        values = field.get("values")
        if not isinstance(value, str) or value not in values:
            raise ObservationError(f"{owner}: value is outside the registered enum")
        return
    if kind == "nonnegative-integer":
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ObservationError(f"{owner}: expected nonnegative JSON integer")
        return
    if kind == "nonempty-string":
        if not isinstance(value, str) or not value:
            raise ObservationError(f"{owner}: expected nonempty string")
        return
    raise ObservationError(f"{owner}: unknown registered field kind {kind!r}")


def normalize_observation(
    data: dict[str, Any], normalization_id: str, observation: Any
) -> dict[str, Any]:
    contract = contract_map(data).get(normalization_id)
    if contract is None:
        raise ObservationError(f"unknown normalization id {normalization_id!r}")
    if not isinstance(observation, dict):
        raise ObservationError("observation must be an object")
    compared = tuple(item["field"] for item in contract["compared_fields"])
    ignored = tuple(item["field"] for item in contract["ignored_fields"])
    expected = set(compared) | set(ignored)
    actual = set(observation)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing or extra:
        raise ObservationError(
            f"observation fields must be exact; missing={missing}, extra={extra}"
        )
    schemas = {
        item["field"]: item
        for item in contract["compared_fields"] + contract["ignored_fields"]
    }
    for field, value in observation.items():
        validate_observation_value(normalization_id, schemas[field], value)
    return {
        "schema": PROJECTION_DOMAIN,
        "normalization_id": normalization_id,
        "fields": {field: observation[field] for field in compared},
    }


def normalized_observation_digest(
    data: dict[str, Any], normalization_id: str, observation: Any
) -> str:
    projection = normalize_observation(data, normalization_id, observation)
    return canonical_json_digest(PROJECTION_DOMAIN, projection)


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if set(data) != TOP_LEVEL_FIELDS:
        failures.append("top-level fields must be exact")
    if data.get("schema") != "axeyum-lean-u2-normalization-contracts-v3":
        failures.append("schema drift")
    if data.get("target") != {
        "lean_version": "4.30.0",
        "lean_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
    }:
        failures.append("target must match pinned Lean v4.30.0")
    if data.get("status") != "bounded-contract-only":
        failures.append("status must remain bounded-contract-only")
    if data.get("implementation") != {
        "canonicalization_schema": PROJECTION_DOMAIN,
        "contract_digest_domain": CONTRACT_DOMAIN,
        "projection_digest_domain": PROJECTION_DOMAIN,
        "encoding": "utf8-sorted-object-keys-original-array-order-compact-json",
        "unknown_field_policy": "reject",
        "numeric_policy": "integers-only-no-floats",
        "array_policy": "order-is-semantic",
        "value_schema_policy": "validate-before-project",
    }:
        failures.append("implementation contract drift")

    contracts = data.get("contracts")
    if not isinstance(contracts, list):
        failures.append("contracts must be a list")
        contracts = []
    ids = tuple(
        contract.get("id") for contract in contracts if isinstance(contract, dict)
    )
    if ids != CONTRACT_IDS:
        failures.append(f"contract ids/order must be {CONTRACT_IDS!r}")
    for contract in contracts:
        if not isinstance(contract, dict):
            failures.append("every contract must be an object")
            continue
        contract_id = str(contract.get("id", "<unknown>"))
        if set(contract) != CONTRACT_FIELDS:
            failures.append(f"{contract_id}: contract fields must be exact")
        expected = EXPECTED_CONTRACTS.get(contract_id)
        if expected is None:
            failures.append(f"{contract_id}: unregistered contract")
            continue
        if contract.get("layer") != expected["layer"]:
            failures.append(f"{contract_id}: layer drift")
        applicable_axes = contract.get("applicable_axes")
        if not isinstance(applicable_axes, list):
            failures.append(f"{contract_id}: applicable_axes must be a list")
            applicable_axes = []
        if tuple(applicable_axes) != expected["applicable_axes"]:
            failures.append(f"{contract_id}: applicable axes drift")
        if (
            not applicable_axes
            or any(axis not in AXIS_IDS for axis in applicable_axes)
            or applicable_axes
            != sorted(applicable_axes, key=lambda axis: int(axis[1:]))
            or len(applicable_axes) != len(set(applicable_axes))
        ):
            failures.append(
                f"{contract_id}: applicable axes must be known, unique, and sorted"
            )
        compared = contract.get("compared_fields")
        if not isinstance(compared, list):
            failures.append(f"{contract_id}: compared_fields must be a list")
            compared = []
        compared_tuples = tuple(field_schema_tuple(field) for field in compared)
        if compared_tuples != expected["compared_fields"]:
            failures.append(f"{contract_id}: compared field schemas/order drift")
        compared_names: list[Any] = []
        for field in compared:
            if not isinstance(field, dict):
                failures.append(f"{contract_id}: compared field must be an object")
                continue
            name = field.get("field")
            kind = field.get("kind")
            compared_names.append(name)
            expected_keys = {"field", "kind", "values"} if kind == "enum" else {
                "field",
                "kind",
            }
            if set(field) != expected_keys:
                failures.append(
                    f"{contract_id}.{name}: field schema keys must be exact"
                )
            if not FIELD_NAME.fullmatch(str(name)):
                failures.append(f"{contract_id}: compared field must be snake_case")
            if kind not in {"sha256", "enum"}:
                failures.append(f"{contract_id}.{name}: invalid compared field kind")
            if kind == "enum":
                values = field.get("values")
                if (
                    not isinstance(values, list)
                    or not values
                    or any(not isinstance(value, str) or not value for value in values)
                    or len(values) != len(set(values))
                ):
                    failures.append(
                        f"{contract_id}.{name}: enum values must be nonempty unique strings"
                    )
        names_are_strings = all(isinstance(name, str) for name in compared_names)
        if (
            not names_are_strings
            or compared_names != sorted(compared_names)
            or len(compared_names) != len(set(compared_names))
        ):
            failures.append(
                f"{contract_id}: compared fields must be unique and sorted"
            )
        ignored = contract.get("ignored_fields")
        if not isinstance(ignored, list):
            failures.append(f"{contract_id}: ignored_fields must be a list")
            ignored = []
        ignored_names: list[Any] = []
        ignored_schemas: list[tuple[Any, Any]] = []
        for rule in ignored:
            if not isinstance(rule, dict) or set(rule) != {"field", "kind", "reason"}:
                failures.append(
                    f"{contract_id}: ignored rules must contain field/kind/reason"
                )
                continue
            ignored_names.append(rule.get("field"))
            ignored_schemas.append((rule.get("field"), rule.get("kind")))
            if not isinstance(rule.get("reason"), str) or not rule["reason"].strip():
                failures.append(f"{contract_id}: ignored rule reason is required")
        if tuple(ignored_schemas) != IGNORED_SCHEMAS:
            failures.append(f"{contract_id}: ignored field schemas/order drift")
        if all(isinstance(name, str) for name in ignored_names) and set(
            compared_names
        ) & set(ignored_names):
            failures.append(f"{contract_id}: compared and ignored fields overlap")
        seal = contract.get("contract_sha256")
        if not HEX64.fullmatch(str(seal or "")):
            failures.append(f"{contract_id}: contract_sha256 must be lowercase 64-hex")
        elif seal != normalization_contract_digest(contract):
            failures.append(f"{contract_id}: contract_sha256 does not match content")

    covered_axes = {
        axis
        for contract in contracts
        if isinstance(contract, dict)
        for axis in contract.get("applicable_axes", [])
        if isinstance(axis, str)
    }
    if covered_axes != set(AXIS_IDS):
        failures.append("normalization contracts must cover exactly A0-A11")
    field_schemas = [
        field
        for contract in contracts
        if isinstance(contract, dict)
        for collection in ("compared_fields", "ignored_fields")
        for field in contract.get(collection, [])
        if isinstance(field, dict)
    ]
    schema_counts = {
        kind: sum(field.get("kind") == kind for field in field_schemas)
        for kind in ("enum", "nonempty-string", "nonnegative-integer", "sha256")
    }
    summary = {
        "contracts": len(contracts),
        "compared_fields": sum(
            len(contract.get("compared_fields", []))
            for contract in contracts
            if isinstance(contract, dict)
        ),
        "ignored_rules": sum(
            len(contract.get("ignored_fields", []))
            for contract in contracts
            if isinstance(contract, dict)
        ),
        "covered_axes": len(covered_axes),
        "axis_contract_occurrences": sum(
            len(contract.get("applicable_axes", []))
            for contract in contracts
            if isinstance(contract, dict)
        ),
        "typed_field_occurrences": len(field_schemas),
        "value_schema_counts": schema_counts,
        "raw_extractors_implemented": 0,
        "semantic_canonicalizers_implemented": 0,
        "official_outcomes": 0,
        "axeyum_outcomes": 0,
        "paired_cells": 0,
        "parity_credit": 0,
    }
    if data.get("summary") != summary:
        failures.append("summary must equal derived zero-credit contract totals")
    execution_evidence = load_execution_evidence()
    if tuple(
        execution_evidence.get("taxonomies", {}).get("termination_classes", ())
    ) != TERMINATION_CLASSES:
        failures.append("termination classes drift from execution-evidence authority")
    if data.get("claims") != {
        "parents_complete": False,
        "obligation_authority_complete": False,
        "raw_extractors_implemented": False,
        "semantic_canonicalizers_implemented": False,
        "external_process_observed": False,
        "lean_complete_parity": False,
    }:
        failures.append("claims must preserve the offline non-credit boundary")
    return failures


def render_markdown(data: dict[str, Any]) -> str:
    summary = data["summary"]
    lines = [
        "# Lean U2 normalization-contract authority",
        "",
        "> **Generated; do not edit by hand.** Regenerate with "
        "`python3 scripts/lean_u2_normalization_contracts.py`; validate with "
        "`--check`.",
        "",
        "> **Status: bounded contract/projection evidence only.** Raw extractors, "
        "semantic canonicalizers, official/native outcomes, paired cells, and parity "
        "credit remain zero.",
        "",
        f"Pinned target: Lean `{data['target']['lean_version']}` at "
        f"`{data['target']['lean_commit']}`.",
        "",
        "| Normalization | Layer | Axes | Compared fields | Ignored rules | Contract seal |",
        "|---|---|---|---:|---:|---|",
    ]
    for contract in data["contracts"]:
        axes = ", ".join(f"`{axis}`" for axis in contract["applicable_axes"])
        lines.append(
            f"| `{contract['id']}` | `{contract['layer']}` | {axes} | "
            f"{len(contract['compared_fields'])} | {len(contract['ignored_fields'])} | "
            f"`{contract['contract_sha256']}` |"
        )
    lines.extend(
        [
            "",
            f"Totals: **{summary['contracts']} contracts**, "
            f"**{summary['compared_fields']} compared fields**, and "
            f"**{summary['ignored_rules']} explicit ignored-field rules**, for "
            f"**{summary['typed_field_occurrences']} typed field occurrences**. "
            f"The registry covers **{summary['covered_axes']} axes** through "
            f"**{summary['axis_contract_occurrences']} contract/axis occurrences**. "
            "The sealed kinds are "
            f"**{summary['value_schema_counts']['sha256']} SHA-256**, "
            f"**{summary['value_schema_counts']['enum']} enum**, "
            f"**{summary['value_schema_counts']['nonnegative-integer']} "
            "nonnegative-integer**, and "
            f"**{summary['value_schema_counts']['nonempty-string']} nonempty-string**.",
            "",
            "The projection kernel validates each typed value before projection and "
            "rejects missing or unknown fields, malformed digests, values outside a "
            "registered enum, negative or Boolean collector sequences, empty storage "
            "paths, unregistered normalizers, cross-layer reuse, and stale contract "
            "seals. No field schema admits an array or object. The only ignored fields "
            "are `collector_sequence` and `evidence_storage_path`; their types and "
            "reasons are sealed per contract.",
            "",
            "This authority does not establish that raw Lean or Axeyum artifacts can "
            "yet be transformed into these fields. That layer-specific extraction and "
            "semantic canonicalization remains open TL0.6.5 M1 work after the required "
            "parents and M0 obligation authority exist.",
            "",
        ]
    )
    return "\n".join(lines)


def write_or_check(path: Path, content: str, check: bool) -> list[str]:
    if check:
        if not path.is_file():
            return [f"missing generated file {path.relative_to(ROOT)}"]
        if path.read_text(encoding="utf-8") != content:
            return [f"stale generated file {path.relative_to(ROOT)}"]
        return []
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return []


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-seals", action="store_true")
    args = parser.parse_args()
    data = load_manifest()
    if args.print_seals:
        for contract in data.get("contracts", []):
            print(f"{contract['id']}={normalization_contract_digest(contract)}")
        return 0
    failures = validate_manifest(data)
    if not failures:
        failures.extend(write_or_check(OUT_MD, render_markdown(data), args.check))
    if failures:
        for failure in failures:
            print(f"LEAN_U2_NORMALIZATION_ERROR|{failure}", file=sys.stderr)
        return 1
    summary = data["summary"]
    print(
        "LEAN_U2_NORMALIZATION|"
        f"contracts={summary['contracts']}|"
        f"compared_fields={summary['compared_fields']}|"
        f"ignored_rules={summary['ignored_rules']}|"
        f"covered_axes={summary['covered_axes']}|"
        f"axis_contracts={summary['axis_contract_occurrences']}|"
        f"typed_fields={summary['typed_field_occurrences']}|"
        f"sha256={summary['value_schema_counts']['sha256']}|"
        f"enum={summary['value_schema_counts']['enum']}|"
        f"nonnegative_integer={summary['value_schema_counts']['nonnegative-integer']}|"
        f"nonempty_string={summary['value_schema_counts']['nonempty-string']}|"
        "raw_extractors=0|semantic_canonicalizers=0|paired_cells=0|parity_credit=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
