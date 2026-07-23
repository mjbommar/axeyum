#!/usr/bin/env python3
"""Generate TL0.6.4 M2.0's empty, non-crediting U2 dependency contract."""

from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

MANIFEST = ROOT / "docs/plan/lean-u2-native-dependency-v1.json"
OUT_JSON = ROOT / "docs/plan/generated/lean-u2-native-dependency.json"
OUT_MD = ROOT / "docs/plan/generated/lean-u2-native-dependency.md"
M1_PATH = ROOT / "docs/plan/lean-u2-native-surface-content-v1.json"
M1_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-native-surface-content.py"
PROFILE_PATH = ROOT / "docs/plan/lean-u2-official-ci-profiles-v1.json"
PROFILE_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-official-ci-profiles.py"
EXECUTION_PATH = ROOT / "docs/plan/lean-execution-evidence-v1.json"
EXECUTION_VALIDATOR_PATH = ROOT / "scripts/gen-lean-execution-evidence.py"
PLAN_PATH = ROOT / "docs/plan/lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md"

SCHEMA = "axeyum-lean-u2-native-dependency-v1"
REPORT_SCHEMA = "axeyum-lean-u2-native-dependency-report-v1"
AS_OF = "2026-07-23"
SOURCE_HASHES = {
    "docs/plan/lean-u2-native-surface-content-v1.json": (
        "c83d10ce0f0619d4327dbbd7544bd584360cb080d35778ca7798a5f7da17560f"
    ),
    "scripts/gen-lean-u2-native-surface-content.py": (
        "107d699e3ab372ee78e686affcb7cbd940d6ff4ae3446dc29f90d1cd6927fb05"
    ),
    "docs/plan/lean-u2-official-ci-profiles-v1.json": (
        "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548"
    ),
    "scripts/gen-lean-u2-official-ci-profiles.py": (
        "4b4b2d0fca8acaee1f90e8a7f143067db6596e6aa7d558e9a877639db878e246"
    ),
    "docs/plan/lean-execution-evidence-v1.json": (
        "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a"
    ),
    "scripts/gen-lean-execution-evidence.py": (
        "025f935111b83e1a3bbc78af50a4ad5671baa370bda02fe94756481e54f55418"
    ),
    "docs/plan/lean-u2-native-surface-classification-tl0.6.4-m2-plan-2026-07-23.md": (
        "a03fccc1beb59b075eab798e3f5b2f4e92b403d947bc13c95b2920714777ced5"
    ),
}
EXPECTED_M1_RECORD_SHA256 = (
    "d10f350d2c01d116538c9b52dcef71f38c473c81a36b3b41f75da4f39b889887"
)
EXPECTED_M1_CASE_ROWS_SHA256 = (
    "40190bb4aa7ea1160d5789ff4a98bc81716a51d6ea72f36839e0a43a3268b415"
)

NODE_DOMAIN = "axeyum-lean-u2-native-dependency-node-type-v1"
EDGE_DOMAIN = "axeyum-lean-u2-native-dependency-edge-type-v1"
STATE_DOMAIN = "axeyum-lean-u2-native-dependency-evidence-state-v1"
RESOLVER_DOMAIN = "axeyum-lean-u2-native-dependency-resolver-v1"
SELECTION_DOMAIN = "axeyum-lean-u2-native-dependency-selection-v1"
VARIANT_DOMAIN = "axeyum-lean-u2-native-dependency-provider-variant-v1"
CASE_DOMAIN = "axeyum-lean-u2-native-dependency-case-v1"

NODE_TYPES: tuple[dict[str, Any], ...] = (
    {"id": "source", "identity": ["path", "mode", "git_blob", "bytes", "sha256", "universe"]},
    {"id": "lean-module", "identity": ["module", "package", "source", "artifact"]},
    {"id": "generated-file", "identity": ["generator", "configuration", "substitutions", "output"]},
    {"id": "build-artifact", "identity": ["facet", "path", "bytes", "sha256", "producer"]},
    {"id": "package-project", "identity": ["root", "configuration", "manifest", "package_id"]},
    {"id": "executable-tool", "identity": ["realpath", "bytes", "sha256", "version", "commit", "target"]},
    {"id": "library-plugin", "identity": ["logical_name", "path", "bytes", "sha256", "role"]},
    {"id": "request-document", "identity": ["method", "payload", "uri", "version", "content"]},
    {"id": "runtime-file-effect", "identity": ["path_or_class", "before", "after"]},
    {"id": "external-network", "identity": ["endpoint", "protocol", "pin", "cache_policy"]},
    {"id": "platform-profile", "identity": ["context", "provider", "os", "arch", "tier", "configuration", "lane"]},
)

EDGE_TYPES: tuple[dict[str, Any], ...] = tuple(
    {"id": edge_id, "requires_observation": observed}
    for edge_id, observed in (
        ("header-import", False),
        ("resolved-source", False),
        ("resolved-olean", False),
        ("transitive-import", False),
        ("extra-module-use", False),
        ("configures", False),
        ("sources", False),
        ("executes", True),
        ("reads", True),
        ("writes", True),
        ("generates", True),
        ("package-dependency", False),
        ("target-facet", False),
        ("artifact-input", False),
        ("cache-input", False),
        ("links-static", False),
        ("links-dynamic", False),
        ("loads-dynlib", True),
        ("loads-plugin", True),
        ("ffi-abi", False),
        ("request-document", False),
        ("request-project", False),
        ("edit-version", True),
        ("cancels", True),
        ("runtime-input", True),
        ("runtime-output", True),
        ("runtime-effect", True),
        ("network-edge", True),
        ("conditional-on-profile", False),
        ("conditional-on-platform", False),
        ("conditional-on-branch", False),
    )
)

EVIDENCE_STATES: tuple[dict[str, Any], ...] = (
    {"id": "declared-static", "complete_for_edge": False},
    {"id": "resolved-static", "complete_for_edge": True},
    {"id": "configured", "complete_for_edge": True},
    {"id": "observed-runtime", "complete_for_edge": True},
    {"id": "conditional-not-taken", "complete_for_edge": False},
    {"id": "provider-unavailable", "complete_for_edge": False},
    {"id": "intentionally-online", "complete_for_edge": False},
    {"id": "declined", "complete_for_edge": True},
    {"id": "unresolved", "complete_for_edge": False},
)

RESOLVERS: tuple[dict[str, Any], ...] = (
    {
        "id": "m2.1-lean-header-v1",
        "milestone": "M2.1",
        "owner": "TL0.6.4",
        "command_surface": "pinned lean --deps-json",
        "edge_classes": ["header-import"],
        "state": "not-run",
    },
    {
        "id": "m2.2-lean-path-v1",
        "milestone": "M2.2",
        "owner": "TL0.6.4/TL7",
        "command_surface": "pinned lean --deps/--src-deps plus sealed module universe",
        "edge_classes": ["resolved-source", "resolved-olean", "transitive-import", "extra-module-use"],
        "state": "not-run",
    },
    {
        "id": "m2.3-runner-generated-v1",
        "milestone": "M2.3",
        "owner": "TL0.6.4/TL7/TL9",
        "command_surface": "configured CMake wrapper plus retained script evidence",
        "edge_classes": ["configures", "sources", "executes", "reads", "writes", "generates"],
        "state": "not-run",
    },
    {
        "id": "m2.4-lake-project-v1",
        "milestone": "M2.4",
        "owner": "TL7",
        "command_surface": "pinned lake query/setup-file in isolated evidence lane",
        "edge_classes": ["package-dependency", "target-facet", "artifact-input", "cache-input", "links-static", "links-dynamic", "loads-dynlib", "loads-plugin"],
        "state": "not-run",
    },
    {
        "id": "m2.5-runtime-ffi-v1",
        "milestone": "M2.5",
        "owner": "TL9/TL9.10",
        "command_surface": "retained compiler/interpreter/link/load/runtime evidence",
        "edge_classes": ["ffi-abi", "runtime-input", "runtime-output", "runtime-effect", "network-edge"],
        "state": "not-run",
    },
    {
        "id": "m2.6-editor-rpc-v1",
        "milestone": "M2.6",
        "owner": "TL8",
        "command_surface": "retained server request/project transcript evidence",
        "edge_classes": ["request-document", "request-project", "edit-version", "cancels"],
        "state": "not-run",
    },
    {
        "id": "m2.7-variant-merge-v1",
        "milestone": "M2.7",
        "owner": "TL0.6.4",
        "command_surface": "offline full-graph merge and residual review projection",
        "edge_classes": ["conditional-on-profile", "conditional-on-platform", "conditional-on-branch"],
        "state": "not-run",
    },
)

CLAIMS = {
    "graph_contract_frozen": True,
    "all_m1_cases_projected": True,
    "official_variants_factored": True,
    "provider_identity_bound": False,
    "header_graph_complete": False,
    "source_artifact_resolution_complete": False,
    "runner_generated_closure_complete": False,
    "lake_project_closure_complete": False,
    "runtime_ffi_closure_complete": False,
    "editor_rpc_closure_complete": False,
    "all_case_profile_closures_complete": False,
    "native_execution_observed": False,
    "matched_pair_formed": False,
    "tl0_6_4_complete": False,
    "lean_parity_established": False,
}
ZERO_CREDITS = {
    "official_outcomes": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}
RESIDUAL = [
    "M2.1 must retain exact pinned --deps-json header-import evidence for every applicable Lean source.",
    "M2.2-M2.6 must resolve source/artifact, generated runner, Lake/project, runtime/FFI, and editor/RPC edges per provider variant.",
    "M2.7 must merge every case/profile graph with no unresolved or provider-unavailable required edge before M3 review.",
    "No M2.0 row is an execution, support, pair, performance, population, axis, gate, or parity result.",
]


class DependencyError(RuntimeError):
    """Fail-closed M2 dependency authority error."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def seal(record: dict[str, Any], domain: str) -> dict[str, Any]:
    result = copy.deepcopy(record)
    result["record_sha256"] = domain_digest(
        domain, {key: value for key, value in result.items() if key != "record_sha256"}
    )
    return result


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise DependencyError(f"cannot read canonical JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise DependencyError(f"top-level JSON must be an object: {path}")
    return value


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise DependencyError(f"cannot import validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@functools.lru_cache(maxsize=1)
def _validated_parents() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    for relative, expected in SOURCE_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise DependencyError(f"frozen source or plan drift: {relative}")
    m1 = load_json(M1_PATH)
    m1_validator = load_script("lean_u2_dependency_m1_validator", M1_VALIDATOR_PATH)
    failures = m1_validator.validate_authority(m1)
    if failures:
        raise DependencyError("invalid frozen M1 authority: " + "; ".join(failures))
    profiles = load_json(PROFILE_PATH)
    profile_validator = load_script(
        "lean_u2_dependency_profile_validator", PROFILE_VALIDATOR_PATH
    )
    failures = profile_validator.validate_manifest(profiles)
    if failures:
        raise DependencyError("invalid frozen profile authority: " + "; ".join(failures))
    execution = load_json(EXECUTION_PATH)
    execution_validator = load_script(
        "lean_u2_dependency_execution_validator", EXECUTION_VALIDATOR_PATH
    )
    failures = execution_validator.validate_authority(execution)
    if failures:
        raise DependencyError("invalid frozen execution authority: " + "; ".join(failures))
    if m1.get("record_sha256") != EXPECTED_M1_RECORD_SHA256:
        raise DependencyError("frozen M1 record seal drift")
    if m1.get("case_rows_sha256") != EXPECTED_M1_CASE_ROWS_SHA256:
        raise DependencyError("frozen M1 case-row seal drift")
    return m1, profiles, execution


def validated_parents() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    return tuple(copy.deepcopy(value) for value in _validated_parents())  # type: ignore[return-value]


def sealed_registry(rows: tuple[dict[str, Any], ...], domain: str) -> list[dict[str, Any]]:
    return [seal(row, domain) for row in rows]


def build_selection_rows(profiles: dict[str, Any]) -> list[dict[str, Any]]:
    attempts_by_selection: dict[str, list[str]] = {
        row["id"]: [] for row in profiles["selection_sets"]
    }
    for attempt in profiles["attempts"]:
        attempts_by_selection[attempt["selection_set_id"]].append(attempt["id"])
    return [
        seal(
            {
                "selection_set_id": selection["id"],
                "source_selection_sha256": selection["sha256"],
                "profile": selection["profile"],
                "selected_count": selection["selected_count"],
                "selected_ids_sha256": selection["selected_ids_sha256"],
                "provider_variant_ids": attempts_by_selection[selection["id"]],
            },
            SELECTION_DOMAIN,
        )
        for selection in profiles["selection_sets"]
    ]


def build_variant_rows(profiles: dict[str, Any]) -> list[dict[str, Any]]:
    contexts = {row["id"]: row for row in profiles["contexts"]}
    cells = {row["id"]: row for row in profiles["cells"]}
    selections = {row["id"]: row for row in profiles["selection_sets"]}
    rows = []
    for attempt in profiles["attempts"]:
        cell = cells[attempt["cell_id"]]
        context = contexts[cell["context_id"]]
        selection = selections[attempt["selection_set_id"]]
        rows.append(
            seal(
                {
                    "variant_id": attempt["id"],
                    "source_attempt_sha256": attempt["sha256"],
                    "context_id": context["id"],
                    "event": context["event"],
                    "job_id": cell["job_id"],
                    "job_name": cell["job_name"],
                    "phase": attempt["phase"],
                    "target_stage": attempt["target_stage"],
                    "preset": attempt["preset"],
                    "ctest_options": attempt["ctest_options"],
                    "selection_set_id": attempt["selection_set_id"],
                    "selected_count": selection["selected_count"],
                    "selected_ids_sha256": selection["selected_ids_sha256"],
                    "command": attempt["command"],
                    "provider_identity": None,
                    "platform_identity": None,
                    "configuration_identity": None,
                    "resource_lane": None,
                    "provider_state": "unbound",
                    "dependency_state": "not-run",
                    "attempt_state": "not-run",
                },
                VARIANT_DOMAIN,
            )
        )
    return rows


def build_case_rows(
    m1: dict[str, Any], profiles: dict[str, Any], selection_rows: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    selections = {row["id"]: row for row in profiles["selection_sets"]}
    variants_per_selection = {
        row["selection_set_id"]: len(row["provider_variant_ids"])
        for row in selection_rows
    }
    rows = []
    empty_graph_sha = domain_digest(
        "axeyum-lean-u2-native-dependency-empty-case-graph-v1", {"nodes": [], "edges": []}
    )
    for source in m1["case_rows"]:
        applicable = [
            selection["id"]
            for selection in profiles["selection_sets"]
            if source["case_id"] in selection["selected_case_ids"]
        ]
        variant_count = sum(variants_per_selection[selection_id] for selection_id in applicable)
        rows.append(
            seal(
                {
                    "case_id": source["case_id"],
                    "m1_case_sha256": source["record_sha256"],
                    "family": source["family"],
                    "kind": source["kind"],
                    "m1_direct_surfaces": source["direct_surfaces"],
                    "m1_surface_closure": source["surface_closure"],
                    "applicable_selection_set_ids": applicable,
                    "provider_variant_count": variant_count,
                    "variant_factoring": "selection-set-reference",
                    "graph_root_node_ids": [],
                    "node_count": 0,
                    "edge_count": 0,
                    "graph_sha256": empty_graph_sha,
                    "evidence_state_counts": {"not-run": variant_count},
                    "resolver_states": {resolver["id"]: "not-run" for resolver in RESOLVERS},
                    "dependency_state": "not-run",
                    "unresolved": ["M2.1-M2.7-not-run"],
                    "declines": [],
                    "native_outcome": "not-run",
                    "execution_credit": 0,
                    "pairing_credit": 0,
                },
                CASE_DOMAIN,
            )
        )
    return rows


def list_counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for row in rows:
        counts.update(row[field])
    return dict(sorted(counts.items()))


def build_authority() -> dict[str, Any]:
    m1, profiles, execution = validated_parents()
    node_types = sealed_registry(NODE_TYPES, NODE_DOMAIN)
    edge_types = sealed_registry(EDGE_TYPES, EDGE_DOMAIN)
    evidence_states = sealed_registry(EVIDENCE_STATES, STATE_DOMAIN)
    resolvers = sealed_registry(RESOLVERS, RESOLVER_DOMAIN)
    selection_rows = build_selection_rows(profiles)
    variant_rows = build_variant_rows(profiles)
    case_rows = build_case_rows(m1, profiles, selection_rows)
    case_variant_occurrences = sum(row["selected_count"] for row in variant_rows)
    authority: dict[str, Any] = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "m2.0-contract-complete-all-dependency-resolution-not-run",
        "scope": "full-u2-dependency-graph-contract-empty-non-crediting",
        "target": m1["target"],
        "policy": {
            "case_population_required": 3723,
            "official_variants_factored_by_selection_set": True,
            "provider_identity_required_before_process": True,
            "typed_nodes_and_edges_required": True,
            "lexical_signal_is_not_reachability": True,
            "static_resolution_is_not_runtime_observation": True,
            "variant_ownership_preserved": True,
            "all_processes_source_first": True,
            "m2_0_external_processes": 0,
            "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
            "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
        },
        "source_authorities": [
            {"path": relative, "physical_sha256": digest}
            for relative, digest in SOURCE_HASHES.items()
        ],
        "parent_logical_seals": {
            "m1_record_sha256": m1["record_sha256"],
            "m1_file_rows_sha256": m1["file_rows_sha256"],
            "m1_case_rows_sha256": m1["case_rows_sha256"],
            "profile_contexts_sha256": profiles["contexts_sha256"],
            "profile_cells_sha256": profiles["cells_sha256"],
            "profile_selection_sets_sha256": profiles["selection_sets_sha256"],
            "profile_attempts_sha256": profiles["attempts_sha256"],
            "execution_schema": execution["schema"],
        },
        "node_types_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-node-types-v1", node_types
        ),
        "node_types": node_types,
        "edge_types_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-edge-types-v1", edge_types
        ),
        "edge_types": edge_types,
        "evidence_states_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-evidence-states-v1", evidence_states
        ),
        "evidence_states": evidence_states,
        "resolvers_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-resolvers-v1", resolvers
        ),
        "resolvers": resolvers,
        "selection_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-selections-v1", selection_rows
        ),
        "selection_rows": selection_rows,
        "provider_variants_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-provider-variants-v1", variant_rows
        ),
        "provider_variants": variant_rows,
        "nodes_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-nodes-v1", []
        ),
        "nodes": [],
        "edges_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-edges-v1", []
        ),
        "edges": [],
        "case_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-dependency-cases-v1", case_rows
        ),
        "case_rows": case_rows,
        "summary": {
            "registration_cases": len(case_rows),
            "selection_sets": len(selection_rows),
            "provider_variants": len(variant_rows),
            "case_variant_occurrences": case_variant_occurrences,
            "provider_state_counts": dict(
                sorted(Counter(row["provider_state"] for row in variant_rows).items())
            ),
            "variant_dependency_state_counts": dict(
                sorted(Counter(row["dependency_state"] for row in variant_rows).items())
            ),
            "case_dependency_state_counts": dict(
                sorted(Counter(row["dependency_state"] for row in case_rows).items())
            ),
            "nodes": 0,
            "edges": 0,
            "resolved_case_closures": 0,
            "m1_direct_surface_counts": list_counts(case_rows, "m1_direct_surfaces"),
            "m1_closure_surface_counts": list_counts(case_rows, "m1_surface_closure"),
            "external_processes": 0,
            "native_outcomes": 0,
            "paired_cells": 0,
        },
        "claims": CLAIMS,
        "credits": ZERO_CREDITS,
        "residual": RESIDUAL,
        "record_sha256": "",
    }
    authority["record_sha256"] = domain_digest(
        SCHEMA, {key: value for key, value in authority.items() if key != "record_sha256"}
    )
    return authority


def validate_record_seals(rows: Any, domain: str, label: str) -> list[str]:
    failures: list[str] = []
    if not isinstance(rows, list):
        return [f"{label} must be a list"]
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            failures.append(f"{label} {index} must be an object")
            continue
        expected = domain_digest(
            domain, {key: value for key, value in row.items() if key != "record_sha256"}
        )
        if row.get("record_sha256") != expected:
            failures.append(f"{label} {index} record seal drift")
    return failures


def validate_authority(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    try:
        expected = build_authority()
    except DependencyError as error:
        return [str(error)]
    fixed_fields = (
        "schema",
        "as_of",
        "status",
        "scope",
        "target",
        "policy",
        "source_authorities",
        "parent_logical_seals",
        "claims",
        "credits",
        "residual",
    )
    for field in fixed_fields:
        if data.get(field) != expected[field]:
            failures.append(f"{field} drift")
    registries = (
        ("node_types", NODE_DOMAIN),
        ("edge_types", EDGE_DOMAIN),
        ("evidence_states", STATE_DOMAIN),
        ("resolvers", RESOLVER_DOMAIN),
        ("selection_rows", SELECTION_DOMAIN),
        ("provider_variants", VARIANT_DOMAIN),
        ("case_rows", CASE_DOMAIN),
    )
    for field, domain in registries:
        rows = data.get(field)
        failures.extend(validate_record_seals(rows, domain, field))
        if rows != expected[field]:
            failures.append(f"{field} semantic or order drift")
        seal_field = {
            "node_types": "node_types_sha256",
            "edge_types": "edge_types_sha256",
            "evidence_states": "evidence_states_sha256",
            "resolvers": "resolvers_sha256",
            "selection_rows": "selection_rows_sha256",
            "provider_variants": "provider_variants_sha256",
            "case_rows": "case_rows_sha256",
        }[field]
        list_domain = {
            "node_types": "axeyum-lean-u2-native-dependency-node-types-v1",
            "edge_types": "axeyum-lean-u2-native-dependency-edge-types-v1",
            "evidence_states": "axeyum-lean-u2-native-dependency-evidence-states-v1",
            "resolvers": "axeyum-lean-u2-native-dependency-resolvers-v1",
            "selection_rows": "axeyum-lean-u2-native-dependency-selections-v1",
            "provider_variants": "axeyum-lean-u2-native-dependency-provider-variants-v1",
            "case_rows": "axeyum-lean-u2-native-dependency-cases-v1",
        }[field]
        if data.get(seal_field) != domain_digest(list_domain, rows):
            failures.append(f"{field} list seal drift")
    for field, domain in (
        ("nodes", "axeyum-lean-u2-native-dependency-nodes-v1"),
        ("edges", "axeyum-lean-u2-native-dependency-edges-v1"),
    ):
        if data.get(field) != []:
            failures.append(f"M2.0 {field} must be empty")
        if data.get(field + "_sha256") != domain_digest(domain, data.get(field)):
            failures.append(f"{field} list seal drift")
    if data.get("summary") != expected["summary"]:
        failures.append("summary drift")
    if data.get("record_sha256") != domain_digest(
        SCHEMA, {key: value for key, value in data.items() if key != "record_sha256"}
    ):
        failures.append("top-level record seal drift")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "as_of": data["as_of"],
        "target": data["target"],
        "verdict": "M2.0 graph and provider contract frozen; all dependency resolution and Lean parity remain not run",
        "summary": data["summary"],
        "claims": data["claims"],
        "credits": data["credits"],
        "residual": data["residual"],
        "authority_record_sha256": data["record_sha256"],
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Generated Lean U2 native dependency contract",
        "",
        "> Generated by `scripts/gen-lean-u2-native-dependency.py`; do not edit by hand.",
        "",
        f"- Verdict: **{report['verdict']}**.",
        f"- Registered cases: **{summary['registration_cases']:,}**.",
        f"- Factored selection sets / official provider variants: **{summary['selection_sets']} / {summary['provider_variants']}**.",
        f"- Case/provider occurrences represented without expansion: **{summary['case_variant_occurrences']:,}**.",
        f"- Resolved nodes / edges / case closures: **{summary['nodes']} / {summary['edges']} / {summary['resolved_case_closures']}**.",
        f"- External processes, native outcomes, and paired cells: **{summary['external_processes']} / {summary['native_outcomes']} / {summary['paired_cells']}**.",
        "",
        "## M2.0 state",
        "",
        "All 111 official variants are `provider_state = unbound` and `dependency_state = not-run`. All 3,723 case closures are `not-run`. Selection-set factoring preserves exact applicability without storing hundreds of thousands of duplicate case rows.",
        "",
        "## Non-crediting boundary",
        "",
        "The node, edge, assurance, resolver, selection, provider-variant, and case schemas are frozen, but the canonical node and edge lists are empty. This authority does not parse an import, resolve a path, materialize a wrapper, query Lake, observe runtime behavior, or establish native support.",
        "",
        "## Required continuation",
        "",
    ]
    lines.extend(f"- {item}" for item in report["residual"])
    return "\n".join(lines) + "\n"


def write_outputs(authority: dict[str, Any]) -> None:
    MANIFEST.write_text(json_text(authority), encoding="utf-8")
    report = summarize(authority)
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_outputs() -> None:
    if not MANIFEST.is_file():
        raise DependencyError(f"missing committed authority: {MANIFEST.relative_to(ROOT)}")
    data = load_json(MANIFEST)
    failures = validate_authority(data)
    if failures:
        raise DependencyError("invalid M2.0 authority: " + "; ".join(failures))
    report = summarize(data)
    if not OUT_JSON.is_file() or OUT_JSON.read_text(encoding="utf-8") != json_text(report):
        raise DependencyError(f"stale generated report: {OUT_JSON.relative_to(ROOT)}")
    if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != render_markdown(report):
        raise DependencyError(f"stale generated report: {OUT_MD.relative_to(ROOT)}")
    print(
        "LEAN_U2_NATIVE_DEPENDENCY|"
        f"cases={data['summary']['registration_cases']}|"
        f"variants={data['summary']['provider_variants']}|"
        f"occurrences={data['summary']['case_variant_occurrences']}|"
        "nodes=0|edges=0|resolved=0|processes=0|native=0|paired=0|parity=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.check:
            check_outputs()
        else:
            authority = build_authority()
            write_outputs(authority)
            print(
                f"lean-u2-native-dependency: wrote {authority['summary']['registration_cases']} "
                "empty case graphs; processes/native/pair/parity zero"
            )
    except DependencyError as error:
        print(f"lean-u2-native-dependency: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
