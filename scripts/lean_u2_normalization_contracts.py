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
MANIFEST = ROOT / "docs" / "plan" / "lean-u2-normalization-contracts-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-u2-normalization-contracts.md"

CONTRACT_DOMAIN = "axeyum-lean-normalization-contract-v1"
PROJECTION_DOMAIN = "axeyum-lean-normalized-observation-v1"
CONTRACT_IDS = (
    "lean-process-harness-v1",
    "lean-parser-macro-v1",
    "lean-elaboration-v1",
    "lean-kernel-assurance-v1",
    "lean-module-cache-v1",
    "lean-tactic-v1",
    "lean-compiler-runtime-v1",
    "lean-server-rpc-v1",
    "lean-lake-project-v1",
)
IGNORED_FIELDS = ("collector_sequence", "evidence_storage_path")
EXPECTED_CONTRACTS = {
    "lean-process-harness-v1": {
        "layer": "process-harness",
        "applicable_axes": ("A0", "A11"),
        "compared_fields": (
            "cleanup_state",
            "completion_state",
            "declared_effects_sha256",
            "expected_exit_policy",
            "stderr_bytes_sha256",
            "stdout_bytes_sha256",
            "termination_class",
        ),
    },
    "lean-parser-macro-v1": {
        "layer": "parser-macro",
        "applicable_axes": ("A3",),
        "compared_fields": (
            "macro_expansion_sha256",
            "recovery_nodes_sha256",
            "scope_hygiene_sha256",
            "source_spans_sha256",
            "syntax_tree_sha256",
        ),
    },
    "lean-elaboration-v1": {
        "layer": "elaboration",
        "applicable_axes": ("A4",),
        "compared_fields": (
            "core_terms_sha256",
            "declarations_sha256",
            "diagnostics_sha256",
            "environment_extensions_sha256",
            "inferred_types_sha256",
            "info_trees_sha256",
        ),
    },
    "lean-kernel-assurance-v1": {
        "layer": "kernel-assurance",
        "applicable_axes": ("A1", "A9"),
        "compared_fields": (
            "admission_class",
            "axiom_trust_closure_sha256",
            "declaration_identity_sha256",
            "definitional_equality_sha256",
            "dependency_identity_sha256",
            "independent_replay_sha256",
            "inferred_type_sha256",
            "normal_form_sha256",
        ),
    },
    "lean-module-cache-v1": {
        "layer": "module-cache",
        "applicable_axes": ("A2", "A6", "A9"),
        "compared_fields": (
            "artifact_identity_sha256",
            "effective_import_closure_sha256",
            "environment_parts_sha256",
            "initialization_sha256",
            "invalidation_sha256",
            "raw_import_closure_sha256",
            "visibility_sha256",
        ),
    },
    "lean-tactic-v1": {
        "layer": "tactic",
        "applicable_axes": ("A5",),
        "compared_fields": (
            "diagnostics_sha256",
            "final_goals_sha256",
            "independent_admission_sha256",
            "initial_goals_sha256",
            "metavariable_state_sha256",
            "theorem_term_sha256",
        ),
    },
    "lean-compiler-runtime-v1": {
        "layer": "compiler-runtime",
        "applicable_axes": ("A8",),
        "compared_fields": (
            "exception_sha256",
            "execution_route",
            "ffi_abi_sha256",
            "filesystem_effects_sha256",
            "frontend_result_sha256",
            "load_initialization_sha256",
            "stderr_bytes_sha256",
            "stdout_bytes_sha256",
            "termination_class",
            "value_sha256",
        ),
    },
    "lean-server-rpc-v1": {
        "layer": "server-rpc",
        "applicable_axes": ("A7",),
        "compared_fields": (
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
    "lean-lake-project-v1": {
        "layer": "lake-project",
        "applicable_axes": ("A6", "A11"),
        "compared_fields": (
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


def _validate_json_value(value: Any, path: str) -> None:
    if value is None or isinstance(value, (bool, int, str)):
        return
    if isinstance(value, float):
        raise ObservationError(f"{path}: floating-point values are forbidden")
    if isinstance(value, list):
        for index, item in enumerate(value):
            _validate_json_value(item, f"{path}[{index}]")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            if not isinstance(key, str):
                raise ObservationError(f"{path}: object keys must be strings")
            _validate_json_value(item, f"{path}.{key}")
        return
    raise ObservationError(f"{path}: unsupported JSON value {type(value).__name__}")


def normalize_observation(
    data: dict[str, Any], normalization_id: str, observation: Any
) -> dict[str, Any]:
    contract = contract_map(data).get(normalization_id)
    if contract is None:
        raise ObservationError(f"unknown normalization id {normalization_id!r}")
    if not isinstance(observation, dict):
        raise ObservationError("observation must be an object")
    compared = tuple(contract["compared_fields"])
    ignored = tuple(item["field"] for item in contract["ignored_fields"])
    expected = set(compared) | set(ignored)
    actual = set(observation)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing or extra:
        raise ObservationError(
            f"observation fields must be exact; missing={missing}, extra={extra}"
        )
    for field, value in observation.items():
        _validate_json_value(value, field)
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
    if data.get("schema") != "axeyum-lean-u2-normalization-contracts-v1":
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
        if tuple(contract.get("applicable_axes", ())) != expected["applicable_axes"]:
            failures.append(f"{contract_id}: applicable axes drift")
        compared = contract.get("compared_fields")
        compared_tuple = tuple(compared) if isinstance(compared, list) else ()
        if compared_tuple != expected["compared_fields"]:
            failures.append(f"{contract_id}: compared fields/order drift")
            compared = []
        if len(compared) != len(set(compared)) or any(
            not FIELD_NAME.fullmatch(str(field)) for field in compared
        ):
            failures.append(f"{contract_id}: compared fields must be unique snake_case")
        ignored = contract.get("ignored_fields")
        if not isinstance(ignored, list):
            failures.append(f"{contract_id}: ignored_fields must be a list")
            ignored = []
        ignored_names: list[Any] = []
        for rule in ignored:
            if not isinstance(rule, dict) or set(rule) != {"field", "reason"}:
                failures.append(f"{contract_id}: ignored rules must contain field/reason")
                continue
            ignored_names.append(rule.get("field"))
            if not isinstance(rule.get("reason"), str) or not rule["reason"].strip():
                failures.append(f"{contract_id}: ignored rule reason is required")
        if tuple(ignored_names) != IGNORED_FIELDS:
            failures.append(f"{contract_id}: ignored fields/order drift")
        if set(compared) & set(ignored_names):
            failures.append(f"{contract_id}: compared and ignored fields overlap")
        seal = contract.get("contract_sha256")
        if not HEX64.fullmatch(str(seal or "")):
            failures.append(f"{contract_id}: contract_sha256 must be lowercase 64-hex")
        elif seal != normalization_contract_digest(contract):
            failures.append(f"{contract_id}: contract_sha256 does not match content")

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
        "raw_extractors_implemented": 0,
        "semantic_canonicalizers_implemented": 0,
        "official_outcomes": 0,
        "axeyum_outcomes": 0,
        "paired_cells": 0,
        "parity_credit": 0,
    }
    if data.get("summary") != summary:
        failures.append("summary must equal derived zero-credit contract totals")
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
            f"**{summary['ignored_rules']} explicit ignored-field rules**.",
            "",
            "The projection kernel rejects missing or unknown fields, floating-point "
            "values, unregistered normalizers, cross-layer reuse, and stale contract "
            "seals. The only ignored fields are `collector_sequence` and "
            "`evidence_storage_path`; their reasons are sealed per contract. Array "
            "order remains semantic.",
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
        "raw_extractors=0|semantic_canonicalizers=0|paired_cells=0|parity_credit=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
