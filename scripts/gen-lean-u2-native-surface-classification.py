#!/usr/bin/env python3
"""Derive the non-crediting TL0.6.4 M0 U2 native-surface harness floor."""

from __future__ import annotations

import argparse
import copy
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

MANIFEST = ROOT / "docs/plan/lean-u2-native-surface-classification-v1.json"
OUT_JSON = ROOT / "docs/plan/generated/lean-u2-native-surface-classification.json"
OUT_MD = ROOT / "docs/plan/generated/lean-u2-native-surface-classification.md"
U2_PATH = ROOT / "docs/plan/lean-u2-test-authority-v1.json"
U2_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-test-authority.py"

SCHEMA = "axeyum-lean-u2-native-surface-classification-v1"
REPORT_SCHEMA = "axeyum-lean-u2-native-surface-classification-report-v1"
AS_OF = "2026-07-23"
SOURCE_HASHES = {
    "docs/plan/lean-u2-test-authority-v1.json": (
        "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e"
    ),
}
VALIDATOR_HASHES = {
    "scripts/gen-lean-u2-test-authority.py": (
        "2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba"
    ),
}
EXPECTED_CASES_SHA256 = (
    "37050cfb25f0ecfa2256ccb9516124092fc611af5d7be94cce1e9e0745745cd3"
)
EXPECTED_CONTENT_FILES_SHA256 = (
    "f2c8b9c9276ac85dfef7d8e4fc32abe2350a3ae9e659a9a5795cba7f0390631f"
)

SURFACE_DOMAIN = "axeyum-lean-u2-native-surface-v1"
RULE_DOMAIN = "axeyum-lean-u2-native-surface-family-rule-v1"
OVERRIDE_DOMAIN = "axeyum-lean-u2-native-surface-override-v1"
CASE_DOMAIN = "axeyum-lean-u2-native-surface-case-v1"

SURFACES: tuple[dict[str, Any], ...] = (
    {
        "id": "kernel-import",
        "description": "checked core declarations, reductions, imports, and serialization",
        "owner_tasks": ["TL1", "TL2"],
        "axes": ["A1", "A2", "A9"],
        "dependencies": [],
        "capability_state": "partial",
        "decline_code": "native-surface/kernel-import",
    },
    {
        "id": "parser-macro",
        "description": "source parsing, syntax extensions, and macro expansion",
        "owner_tasks": ["TL6"],
        "axes": ["A3"],
        "dependencies": [],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/parser-macro",
    },
    {
        "id": "elaborator",
        "description": "elaboration, unification, commands, and diagnostics",
        "owner_tasks": ["TL4"],
        "axes": ["A4"],
        "dependencies": ["parser-macro", "kernel-import"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/elaborator",
    },
    {
        "id": "tactic-meta",
        "description": "goals, tactics, metaprograms, and generated proof terms",
        "owner_tasks": ["TL5", "TL9.11"],
        "axes": ["A5", "A9"],
        "dependencies": ["elaborator"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/tactic-meta",
    },
    {
        "id": "modules-lake",
        "description": "modules, artifacts, packages, dependency caches, and Lake",
        "owner_tasks": ["TL7"],
        "axes": ["A2", "A6", "A11"],
        "dependencies": ["elaborator"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/modules-lake",
    },
    {
        "id": "editor-rpc",
        "description": "server snapshots, LSP and RPC requests, cancellation, and stale-state behavior",
        "owner_tasks": ["TL8"],
        "axes": ["A7"],
        "dependencies": ["modules-lake", "elaborator"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/editor-rpc",
    },
    {
        "id": "compiler-runtime",
        "description": "evaluation, code generation, linking, execution, and effects",
        "owner_tasks": ["TL9"],
        "axes": ["A8", "A11"],
        "dependencies": ["elaborator"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/compiler-runtime",
    },
    {
        "id": "ffi",
        "description": "extern declarations, ABI linkage, and native library interaction",
        "owner_tasks": ["TL9.10"],
        "axes": ["A8", "A11"],
        "dependencies": ["compiler-runtime"],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/ffi",
    },
    {
        "id": "toolchain-cli",
        "description": "native command, installation, and packaging workflow behavior",
        "owner_tasks": ["TL0", "TL7", "TL9", "TL10"],
        "axes": ["A11"],
        "dependencies": [],
        "capability_state": "not-implemented-native",
        "decline_code": "native-surface/toolchain-cli",
    },
    {
        "id": "adversarial",
        "description": "expected rejection, malformed input, resource, or stale-state dimension",
        "owner_tasks": ["U8", "component-owner"],
        "axes": ["A0-A11-as-applicable"],
        "dependencies": [],
        "capability_state": "partial-cross-cutting",
        "decline_code": "native-surface/adversarial",
    },
)

FAMILY_RULES: tuple[dict[str, Any], ...] = (
    {"id": "bench-directory-v1", "family": "bench", "kind": "directory", "direct_surfaces": ["tactic-meta"]},
    {"id": "compile-pile-v1", "family": "compile", "kind": "pile", "direct_surfaces": ["compiler-runtime"]},
    {"id": "compile-bench-pile-v1", "family": "compile_bench", "kind": "pile", "direct_surfaces": ["compiler-runtime"]},
    {"id": "doc-examples-pile-v1", "family": "doc-examples", "kind": "pile", "direct_surfaces": ["elaborator"]},
    {"id": "docparse-pile-v1", "family": "docparse", "kind": "pile", "direct_surfaces": ["parser-macro", "compiler-runtime"]},
    {"id": "elab-pile-v1", "family": "elab", "kind": "pile", "direct_surfaces": ["elaborator"]},
    {"id": "elab-bench-pile-v1", "family": "elab_bench", "kind": "pile", "direct_surfaces": ["elaborator"]},
    {"id": "elab-fail-pile-v1", "family": "elab_fail", "kind": "pile", "direct_surfaces": ["elaborator", "adversarial"]},
    {"id": "lake-directory-v1", "family": "lake", "kind": "lake-directory", "direct_surfaces": ["modules-lake"]},
    {"id": "lint-v1", "family": "lint", "kind": "lint", "direct_surfaces": ["toolchain-cli"]},
    {"id": "misc-pile-v1", "family": "misc", "kind": "pile", "direct_surfaces": ["toolchain-cli"]},
    {"id": "pkg-directory-v1", "family": "pkg", "kind": "directory", "direct_surfaces": ["modules-lake"]},
    {"id": "server-pile-v1", "family": "server", "kind": "pile", "direct_surfaces": ["editor-rpc"]},
    {"id": "server-interactive-pile-v1", "family": "server_interactive", "kind": "pile", "direct_surfaces": ["editor-rpc"]},
)

CASE_OVERRIDES: tuple[dict[str, Any], ...] = (
    {
        "id": "doc-examples-compiler-directory-v1",
        "case_id": "../doc/examples/compiler",
        "family": "doc-examples",
        "kind": "directory",
        "source_case_sha256": "68fc7b38cb61803ba543bc11f9cfb6f10e7462585af142f399c9882ff74c603e",
        "direct_surfaces": ["compiler-runtime"],
    },
    {
        "id": "misc-plugin-directory-v1",
        "case_id": "misc_dir/plugin",
        "family": "misc_dir",
        "kind": "directory",
        "source_case_sha256": "ac4096fea6be5fc4ed969f0d6b93ad5e74bea708dc3995d9f5322eef883db8cb",
        "direct_surfaces": ["modules-lake", "tactic-meta"],
    },
    {
        "id": "misc-server-project-directory-v1",
        "case_id": "misc_dir/server_project",
        "family": "misc_dir",
        "kind": "directory",
        "source_case_sha256": "d7b7c180195bd80614a0516cbb759b6e0844a61a76e96ddb45bd29c0518e9767",
        "direct_surfaces": ["modules-lake", "editor-rpc"],
    },
)

CLAIMS = {
    "all_registration_cases_have_harness_floor": True,
    "family_kind_population_closed": True,
    "surface_dependency_closure_derived": True,
    "pinned_content_refined": False,
    "module_dependency_closure_complete": False,
    "native_execution_observed": False,
    "matched_pair_formed": False,
    "performance_measured": False,
    "u2_complete": False,
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
    "M1 must inspect every pinned primary, sidecar, runner, hook, and directory support closure.",
    "M2 must derive exact module, generated-artifact, runtime, library, FFI, request, and project dependency closures.",
    "M3 must review the full case authority and resolve every provisional field before TL0.6.4 acceptance.",
    "TL0.6.5 may form matched native rows only after complete official execution and accepted TL0.6.4 classification evidence.",
]


class ClassificationError(RuntimeError):
    """A fail-closed U2 classification derivation or validation failure."""


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
        raise ClassificationError(f"cannot read canonical JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ClassificationError(f"top-level JSON must be an object: {path}")
    return value


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ClassificationError(f"cannot import validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_frozen_input() -> dict[str, Any]:
    for relative, expected in SOURCE_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ClassificationError(f"frozen source authority drift: {relative}")
    for relative, expected in VALIDATOR_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ClassificationError(f"frozen validator source drift: {relative}")
    u2 = load_json(U2_PATH)
    validator = load_script("lean_u2_surface_u2_validator", U2_VALIDATOR_PATH)
    failures = validator.validate_manifest(u2)
    if failures:
        raise ClassificationError("invalid frozen U2 authority: " + "; ".join(failures))
    if u2.get("cases_sha256") != EXPECTED_CASES_SHA256:
        raise ClassificationError("frozen U2 case-list seal drift")
    if u2.get("content_files_sha256") != EXPECTED_CONTENT_FILES_SHA256:
        raise ClassificationError("frozen U2 content-list seal drift")
    return u2


def validate_surface_definitions(surfaces: list[dict[str, Any]]) -> list[str]:
    failures: list[str] = []
    ids = [item.get("id") for item in surfaces]
    if len(ids) != len(set(ids)):
        failures.append("duplicate surface ID")
    known = set(ids)
    for item in surfaces:
        surface_id = item.get("id", "<missing>")
        dependencies = item.get("dependencies")
        if not isinstance(dependencies, list):
            failures.append(f"surface {surface_id}: dependencies must be a list")
            continue
        if len(dependencies) != len(set(dependencies)):
            failures.append(f"surface {surface_id}: duplicate dependency")
        for dependency in dependencies:
            if dependency not in known:
                failures.append(f"surface {surface_id}: unknown dependency {dependency}")

    by_id = {item.get("id"): item for item in surfaces}
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(surface_id: str) -> None:
        if surface_id in visiting:
            failures.append(f"surface dependency cycle at {surface_id}")
            return
        if surface_id in visited or surface_id not in by_id:
            return
        visiting.add(surface_id)
        for dependency in by_id[surface_id].get("dependencies", []):
            visit(dependency)
        visiting.remove(surface_id)
        visited.add(surface_id)

    for surface_id in ids:
        if isinstance(surface_id, str):
            visit(surface_id)
    return failures


def surface_closure(direct: list[str], surfaces: list[dict[str, Any]]) -> list[str]:
    failures = validate_surface_definitions(surfaces)
    if failures:
        raise ClassificationError("invalid surface registry: " + "; ".join(failures))
    order = [item["id"] for item in surfaces]
    by_id = {item["id"]: item for item in surfaces}
    if len(direct) != len(set(direct)):
        raise ClassificationError("duplicate direct surface")
    if unknown := [item for item in direct if item not in by_id]:
        raise ClassificationError(f"unknown direct surface(s): {', '.join(unknown)}")
    included: set[str] = set()

    def add(surface_id: str) -> None:
        if surface_id in included:
            return
        included.add(surface_id)
        for dependency in by_id[surface_id]["dependencies"]:
            add(dependency)

    for surface_id in direct:
        add(surface_id)
    return [surface_id for surface_id in order if surface_id in included]


def rule_for_case(case: dict[str, Any]) -> tuple[dict[str, Any], str]:
    override_matches = [row for row in CASE_OVERRIDES if row["case_id"] == case["id"]]
    if len(override_matches) > 1:
        raise ClassificationError(f"{case['id']}: overlapping case overrides")
    if override_matches:
        override = override_matches[0]
        expected = {
            "family": override["family"],
            "kind": override["kind"],
            "sha256": override["source_case_sha256"],
        }
        observed = {
            "family": case["family"],
            "kind": case["kind"],
            "sha256": case["sha256"],
        }
        if observed != expected:
            raise ClassificationError(f"{case['id']}: override identity drift")
        return override, "override"
    matches = [
        row
        for row in FAMILY_RULES
        if row["family"] == case["family"] and row["kind"] == case["kind"]
    ]
    if len(matches) != 1:
        raise ClassificationError(
            f"{case['id']}: expected one family rule, observed {len(matches)}"
        )
    return matches[0], "family-rule"


def counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counter = Counter(row[field] for row in rows)
    return dict(sorted(counter.items()))


def list_counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counter: Counter[str] = Counter()
    for row in rows:
        counter.update(row[field])
    return dict(sorted(counter.items()))


def build_authority() -> dict[str, Any]:
    u2 = validate_frozen_input()
    surfaces = [seal(item, SURFACE_DOMAIN) for item in SURFACES]
    surface_payloads = [
        {key: value for key, value in item.items() if key != "record_sha256"}
        for item in surfaces
    ]
    failures = validate_surface_definitions(surface_payloads)
    if failures:
        raise ClassificationError("invalid frozen surface registry: " + "; ".join(failures))
    rules = [seal(item, RULE_DOMAIN) for item in FAMILY_RULES]
    overrides = [seal(item, OVERRIDE_DOMAIN) for item in CASE_OVERRIDES]
    case_rows: list[dict[str, Any]] = []
    used_rules: Counter[str] = Counter()
    used_overrides: Counter[str] = Counter()
    seen_ids: set[str] = set()
    for case in u2["cases"]:
        if case["id"] in seen_ids:
            raise ClassificationError(f"duplicate parent case ID: {case['id']}")
        seen_ids.add(case["id"])
        rule, rule_kind = rule_for_case(case)
        if rule_kind == "override":
            used_overrides[rule["id"]] += 1
        else:
            used_rules[rule["id"]] += 1
        direct = list(rule["direct_surfaces"])
        closure = surface_closure(direct, surface_payloads)
        case_rows.append(
            seal(
                {
                    "case_id": case["id"],
                    "source_case_sha256": case["sha256"],
                    "profiles": case["profiles"],
                    "family": case["family"],
                    "kind": case["kind"],
                    "source_path": case["source_path"],
                    "source_sha256": case["source_sha256"],
                    "sidecars": case["sidecars"],
                    "support_scope": case["support_scope"],
                    "output_policy": case["output_policy"],
                    "expected_path": case["expected_path"],
                    "rule_kind": rule_kind,
                    "rule_id": rule["id"],
                    "direct_surfaces": direct,
                    "surface_closure": closure,
                    "classification_state": "harness-floor",
                    "content_refinement": "not-run",
                    "module_dependency_closure": "not-run",
                    "native_outcome": "not-run",
                    "execution_credit": 0,
                    "pairing_credit": 0,
                },
                CASE_DOMAIN,
            )
        )
    unused_rules = sorted(set(row["id"] for row in FAMILY_RULES) - set(used_rules))
    unused_overrides = sorted(set(row["id"] for row in CASE_OVERRIDES) - set(used_overrides))
    repeated_overrides = sorted(key for key, value in used_overrides.items() if value != 1)
    if unused_rules or unused_overrides or repeated_overrides:
        raise ClassificationError(
            "unused or non-unique classifier rule: "
            f"rules={unused_rules}, overrides={unused_overrides}, repeated={repeated_overrides}"
        )

    profile_counter: Counter[str] = Counter()
    for row in case_rows:
        profile_counter.update(row["profiles"])
    family_kind_counter = Counter(f"{row['family']}/{row['kind']}" for row in case_rows)
    authority: dict[str, Any] = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "complete-harness-floor-content-and-dependencies-not-run",
        "scope": "full-u2-native-surface-harness-floor-not-support-or-parity",
        "target": u2["target"],
        "policy": {
            "classification_level": "harness-floor",
            "all_parent_cases_required": True,
            "family_rules_exact": True,
            "case_overrides_exact": True,
            "source_content_inspected": False,
            "module_dependencies_derived": False,
            "native_execution_observed": False,
            "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
            "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
        },
        "source_authorities": [
            {
                "path": U2_PATH.relative_to(ROOT).as_posix(),
                "physical_sha256": SOURCE_HASHES[U2_PATH.relative_to(ROOT).as_posix()],
                "schema": u2["schema"],
                "logical_seals": {
                    "cases_sha256": u2["cases_sha256"],
                    "content_files_sha256": u2["content_files_sha256"],
                },
            }
        ],
        "validator_sources": [
            {"path": relative, "sha256": source_sha}
            for relative, source_sha in VALIDATOR_HASHES.items()
        ],
        "surface_registry_sha256": domain_digest(
            "axeyum-lean-u2-native-surface-registry-v1", surfaces
        ),
        "surface_registry": surfaces,
        "family_rules_sha256": domain_digest(
            "axeyum-lean-u2-native-surface-family-rules-v1", rules
        ),
        "family_rules": rules,
        "case_overrides_sha256": domain_digest(
            "axeyum-lean-u2-native-surface-overrides-v1", overrides
        ),
        "case_overrides": overrides,
        "case_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-surface-cases-v1", case_rows
        ),
        "case_rows": case_rows,
        "summary": {
            "registration_cases": len(case_rows),
            "profile_case_occurrences": dict(sorted(profile_counter.items())),
            "family_counts": counts(case_rows, "family"),
            "kind_counts": counts(case_rows, "kind"),
            "family_kind_counts": dict(sorted(family_kind_counter.items())),
            "direct_surface_counts": list_counts(case_rows, "direct_surfaces"),
            "closure_surface_counts": list_counts(case_rows, "surface_closure"),
            "direct_surface_occurrences": sum(len(row["direct_surfaces"]) for row in case_rows),
            "closure_surface_occurrences": sum(len(row["surface_closure"]) for row in case_rows),
            "classification_state_counts": counts(case_rows, "classification_state"),
            "content_refinement_counts": counts(case_rows, "content_refinement"),
            "module_dependency_closure_counts": counts(case_rows, "module_dependency_closure"),
            "native_outcome_counts": counts(case_rows, "native_outcome"),
            "family_rules_used": len(used_rules),
            "case_overrides_used": len(used_overrides),
        },
        "claims": CLAIMS,
        "credits": ZERO_CREDITS,
        "residual": RESIDUAL,
        "record_sha256": "",
    }
    authority["record_sha256"] = domain_digest(
        SCHEMA,
        {key: value for key, value in authority.items() if key != "record_sha256"},
    )
    return authority


def validate_authority(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    try:
        expected = build_authority()
    except ClassificationError as error:
        return [str(error)]

    for field in ("schema", "as_of", "status", "scope", "target", "policy"):
        if data.get(field) != expected[field]:
            failures.append(f"{field} drift")
    for field in ("source_authorities", "validator_sources"):
        if data.get(field) != expected[field]:
            failures.append(f"{field} drift")

    surfaces = data.get("surface_registry")
    if not isinstance(surfaces, list):
        failures.append("surface registry must be a list")
        surfaces = []
    surface_payloads = [
        {key: value for key, value in item.items() if key != "record_sha256"}
        for item in surfaces
        if isinstance(item, dict)
    ]
    failures.extend(validate_surface_definitions(surface_payloads))
    if surfaces != expected["surface_registry"]:
        failures.append("surface registry semantic or order drift")
    if data.get("surface_registry_sha256") != domain_digest(
        "axeyum-lean-u2-native-surface-registry-v1", surfaces
    ):
        failures.append("surface registry list seal drift")

    rules = data.get("family_rules")
    if rules != expected["family_rules"]:
        failures.append("family rule semantic or order drift")
    if not isinstance(rules, list) or data.get("family_rules_sha256") != domain_digest(
        "axeyum-lean-u2-native-surface-family-rules-v1", rules
    ):
        failures.append("family rule list seal drift")
    overrides = data.get("case_overrides")
    if overrides != expected["case_overrides"]:
        failures.append("case override semantic or order drift")
    if not isinstance(overrides, list) or data.get("case_overrides_sha256") != domain_digest(
        "axeyum-lean-u2-native-surface-overrides-v1", overrides
    ):
        failures.append("case override list seal drift")

    rows = data.get("case_rows")
    if not isinstance(rows, list):
        failures.append("case rows must be a list")
        rows = []
    expected_rows = expected["case_rows"]
    if len(rows) != len(expected_rows):
        failures.append(f"case row count drift: {len(rows)} != {len(expected_rows)}")
    for index, (observed, wanted) in enumerate(zip(rows, expected_rows, strict=False)):
        case_id = wanted["case_id"]
        if not isinstance(observed, dict):
            failures.append(f"case row {index} ({case_id}) is not an object")
            continue
        identity_fields = (
            "case_id", "source_case_sha256", "profiles", "family", "kind",
            "source_path", "source_sha256", "sidecars", "support_scope",
            "output_policy", "expected_path",
        )
        if any(observed.get(field) != wanted[field] for field in identity_fields):
            failures.append(f"case {case_id}: parent identity drift")
        rule_fields = ("rule_kind", "rule_id", "direct_surfaces", "surface_closure")
        if any(observed.get(field) != wanted[field] for field in rule_fields):
            failures.append(f"case {case_id}: classifier rule or closure drift")
        state_fields = (
            "classification_state", "content_refinement",
            "module_dependency_closure", "native_outcome",
            "execution_credit", "pairing_credit",
        )
        if any(observed.get(field) != wanted[field] for field in state_fields):
            failures.append(f"case {case_id}: non-crediting state drift")
        if observed.get("record_sha256") != seal(observed, CASE_DOMAIN).get("record_sha256"):
            failures.append(f"case {case_id}: record seal drift")
    if data.get("case_rows_sha256") != domain_digest(
        "axeyum-lean-u2-native-surface-cases-v1", rows
    ):
        failures.append("case row list seal drift")
    if data.get("summary") != expected["summary"]:
        failures.append("summary drift")
    if data.get("claims") != CLAIMS:
        failures.append("claims drift")
    if data.get("credits") != ZERO_CREDITS:
        failures.append("credit drift")
    if data.get("residual") != RESIDUAL:
        failures.append("residual drift")
    if data.get("record_sha256") != domain_digest(
        SCHEMA,
        {key: value for key, value in data.items() if key != "record_sha256"},
    ):
        failures.append("top-level record seal drift")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "generated_from": MANIFEST.relative_to(ROOT).as_posix(),
        "generated_from_sha256": sha256_file(MANIFEST) if MANIFEST.is_file() else None,
        "target": data["target"],
        "status": data["status"],
        "scope": data["scope"],
        "summary": data["summary"],
        "surface_registry": data["surface_registry"],
        "claims": data["claims"],
        "credits": data["credits"],
        "residual": data["residual"],
        "verdict": "all U2 cases have a harness floor; TL0.6.4 and Lean parity remain incomplete",
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Generated Lean U2 native-surface harness floor",
        "",
        "> Generated by `scripts/gen-lean-u2-native-surface-classification.py`; do not edit by hand.",
        "",
        f"- Verdict: **{report['verdict']}**.",
        f"- Registered cases classified exactly once: **{summary['registration_cases']:,}**.",
        f"- Classification state: **harness-floor={summary['classification_state_counts'].get('harness-floor', 0):,}**.",
        f"- Content refinement: **not-run={summary['content_refinement_counts'].get('not-run', 0):,}**.",
        f"- Exact module dependency closure: **not-run={summary['module_dependency_closure_counts'].get('not-run', 0):,}**.",
        f"- Native outcomes and paired cells: **{report['credits']['axeyum_outcomes']} / {report['credits']['paired_cells']}**.",
        "",
        "## Surface denominator",
        "",
        "| Surface | Direct cases | Closure cases | Owner | State |",
        "|---|---:|---:|---|---|",
    ]
    for surface in report["surface_registry"]:
        surface_id = surface["id"]
        lines.append(
            f"| `{surface_id}` | {summary['direct_surface_counts'].get(surface_id, 0):,} | "
            f"{summary['closure_surface_counts'].get(surface_id, 0):,} | "
            f"{', '.join(surface['owner_tasks'])} | `{surface['capability_state']}` |"
        )
    lines.extend(
        [
            "",
            "## Family denominator",
            "",
            "| Family | Cases |",
            "|---|---:|",
        ]
    )
    for family, count in summary["family_counts"].items():
        lines.append(f"| `{family}` | {count:,} |")
    lines.extend(
        [
            "",
            "## Non-crediting boundary",
            "",
            "Every row still has `content_refinement = not-run`, "
            "`module_dependency_closure = not-run`, and `native_outcome = not-run`. "
            "This report classifies the minimum harness surface only; it does not "
            "measure Axeyum support, execute a native case, or form a parity cell.",
            "",
            "## Required continuation",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["residual"])
    lines.append("")
    return "\n".join(lines)


def check_text(path: Path, expected: str) -> None:
    try:
        observed = path.read_text(encoding="utf-8")
    except OSError as error:
        raise ClassificationError(f"cannot read generated file {path}: {error}") from error
    if observed != expected:
        raise ClassificationError(
            f"stale generated file: {path.relative_to(ROOT)}; run {Path(__file__).name}"
        )


def write_outputs(authority: dict[str, Any]) -> None:
    MANIFEST.write_text(json_text(authority), encoding="utf-8")
    report = summarize(authority)
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_outputs() -> dict[str, Any]:
    data = load_json(MANIFEST)
    failures = validate_authority(data)
    if failures:
        raise ClassificationError("invalid authority: " + "; ".join(failures))
    expected = build_authority()
    if data != expected:
        raise ClassificationError("committed authority differs from deterministic derivation")
    report = summarize(data)
    check_text(OUT_JSON, json_text(report))
    check_text(OUT_MD, render_markdown(report))
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed authority and generated reports")
    args = parser.parse_args()
    try:
        if args.check:
            report = check_outputs()
        else:
            authority = build_authority()
            write_outputs(authority)
            report = summarize(authority)
    except ClassificationError as error:
        print(f"LEAN_U2_NATIVE_SURFACE_ERROR|{error}", file=sys.stderr)
        return 1
    summary = report["summary"]
    print(
        "LEAN_U2_NATIVE_SURFACE|"
        f"cases={summary['registration_cases']}|"
        f"surfaces={len(report['surface_registry'])}|"
        f"content_refined={summary['content_refinement_counts'].get('complete', 0)}|"
        f"dependency_closed={summary['module_dependency_closure_counts'].get('complete', 0)}|"
        f"native_outcomes={report['credits']['axeyum_outcomes']}|"
        f"paired={report['credits']['paired_cells']}|parity=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
