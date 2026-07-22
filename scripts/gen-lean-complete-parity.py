#!/usr/bin/env python3
"""Validate and render the terminal Lean 4 parity registry.

The registry is intentionally fail-closed.  Raw source-tree inventory, bounded
assurance rows, and selected construct evidence remain visible, but none of
them can manufacture a complete U0-U9 authority, A0-A11 axis, paired terminal
cell, or unqualified complete-parity claim.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from collections import Counter
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-complete-parity-v1.json"
OUT_JSON = ROOT / "docs" / "plan" / "generated" / "lean-complete-parity.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-complete-parity.md"
COMPATIBILITY = ROOT / "docs" / "plan" / "lean-compatibility-v1.json"
CONSTRUCT_MATRIX = ROOT / "docs" / "plan" / "lean-official-construct-matrix-v1.json"
AXIOM_LEDGER = ROOT / "docs" / "plan" / "lean-axiom-ledger-v1.json"
U2_AUTHORITY = ROOT / "docs" / "plan" / "lean-u2-test-authority-v1.json"
U2_CI_PROFILES = ROOT / "docs" / "plan" / "lean-u2-official-ci-profiles-v1.json"
EXECUTION_EVIDENCE = ROOT / "docs" / "plan" / "lean-execution-evidence-v1.json"
EXECUTION_PROCESS = ROOT / "docs" / "plan" / "lean-execution-process-v1.json"
IMPLEMENTATION_PLAN = ROOT / "docs" / "plan" / "lean-system-implementation-plan-2026-07-21.md"

POPULATION_IDS = tuple(f"U{index}" for index in range(10))
AXIS_IDS = tuple(f"A{index}" for index in range(12))
GATE_IDS = tuple(f"G{index}" for index in range(1, 11))
POPULATION_LABELS = {
    "U0": "toolchain/bootstrap",
    "U1": "kernel/core",
    "U2": "official Lean tests",
    "U3": "core libraries",
    "U4": "Lake/projects",
    "U5": "server/editor",
    "U6": "runtime/compiler",
    "U7": "mathlib",
    "U8": "adversarial/security",
    "U9": "platforms/releases",
}
AXIS_CONTRACT = {
    "A0": ("identity and measurement", POPULATION_IDS),
    "A1": ("kernel semantics", ("U1", "U8")),
    "A2": ("import and serialization", ("U1", "U2", "U3", "U7", "U8")),
    "A3": ("parser, syntax, macros", ("U2", "U3", "U7", "U8")),
    "A4": ("elaboration and declarations", ("U2", "U3", "U7", "U8")),
    "A5": ("goals, tactics, automation", ("U2", "U3", "U7", "U8")),
    "A6": ("modules, caches, Lake", ("U0", "U2", "U3", "U4", "U7", "U8", "U9")),
    "A7": ("editor and RPC", ("U2", "U5", "U8", "U9")),
    "A8": (
        "evaluator, compiler, runtime",
        ("U0", "U2", "U3", "U6", "U7", "U8", "U9"),
    ),
    "A9": ("libraries and trust closure", ("U1", "U3", "U7", "U8")),
    "A10": ("mathlib ecosystem", ("U7", "U8", "U9")),
    "A11": ("toolchain, CLI, platform, release", ("U0", "U4", "U6", "U9")),
}
GATE_LABELS = {
    "G1": "complete U0-U9 authorities",
    "G2": "complete A0-A11 axes",
    "G3": "all paired cells agree",
    "G4": "complete Lean build/test/bootstrap",
    "G5": "complete mathlib profile",
    "G6": "independent checking and trust evidence",
    "G7": "workflow failure and recovery campaigns",
    "G8": "full platform profile",
    "G9": "unified functional assurance performance evidence",
    "G10": "published release and maintenance policy",
}
POPULATION_STATES = {
    "not_registered",
    "inventory_only",
    "bounded_profile",
    "complete_authority",
}
AXIS_STATES = {"not_started", "partial", "complete"}
GATE_STATES = {"unsatisfied", "satisfied"}
OUTCOME_CLASSES = (
    "agree-success",
    "agree-reject",
    "official-only",
    "axeyum-only",
    "semantic-mismatch",
    "unadjudicated",
    "not-run",
    "invalid-run",
)
PARITY_OUTCOMES = {"agree-success", "agree-reject"}
PAIRED_CELL_FIELDS = {
    "id",
    "population",
    "axis",
    "layer",
    "outcome",
    "source_sha256",
    "dependency_sha256",
    "source_family",
    "normalization",
    "official_executable_sha256",
    "official_configuration_sha256",
    "axeyum_executable_sha256",
    "axeyum_configuration_sha256",
    "command_sha256",
    "environment_sha256",
    "platform_id",
    "resource_envelope_sha256",
    "attempt_id",
    "completed",
    "official_outcome_sha256",
    "axeyum_outcome_sha256",
    "official_assurance_sha256",
    "axeyum_assurance_sha256",
    "diagnostics_sha256",
    "official_duration_ms",
    "axeyum_duration_ms",
    "official_peak_rss_kib",
    "axeyum_peak_rss_kib",
    "official_artifact_bytes",
    "axeyum_artifact_bytes",
    "official_evidence",
    "axeyum_evidence",
}
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
CASE_ID = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
TASK_ROW = re.compile(
    r"^\|\s*([A-Z][A-Z0-9.]*[0-9])\s*\|\s*(DONE|PARTIAL|TODO|BLOCKED)\s*\|",
    re.MULTILINE,
)
AFFIRMATIVE_CLAIMS = (
    re.compile(
        r"\baxeyum\s+(?:has|achieved|reached|provides)\s+"
        r"(?:100%|complete|full)\s+lean(?:\s+4(?:\.30(?:\.0)?)?)?\s+"
        r"(?:parity|compatibility)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:100%|complete|full)\s+lean(?:\s+4(?:\.30(?:\.0)?)?)?\s+"
        r"(?:parity|compatibility)\s+"
        r"(?:is|has\s+been)\s+(?:achieved|complete|delivered|reached)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\bwe\s+(?:have\s+(?:achieved|reached)|achieved|reached)\s+"
        r"(?:100%|complete|full)\s+"
        r"lean(?:\s+4(?:\.30(?:\.0)?)?)?\s+(?:parity|compatibility)\b",
        re.IGNORECASE,
    ),
    re.compile(
        r"\blean(?:\s+4(?:\.30(?:\.0)?)?)?\s+(?:parity|compatibility)\s+"
        r"(?:is|has\s+been)\s+(?:100%|achieved|complete|delivered|reached)\b",
        re.IGNORECASE,
    ),
)
MARKDOWN_DECORATION = str.maketrans("", "", "`*_")


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_manifest() -> dict[str, Any]:
    return load_json(MANIFEST)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {relative(path)}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_evidence(
    owner: str, evidence: Any, failures: list[str], *, required: bool
) -> None:
    if not isinstance(evidence, list):
        failures.append(f"{owner}: evidence must be a list")
        return
    if required and not evidence:
        failures.append(f"{owner}: retained evidence is required")
    for index, item in enumerate(evidence):
        if not isinstance(item, dict):
            failures.append(f"{owner}: evidence[{index}] must be an object")
            continue
        if set(item) != {"path", "detail"}:
            failures.append(
                f"{owner}: evidence[{index}] fields must be path and detail"
            )
            continue
        path_text = item.get("path")
        detail = item.get("detail")
        if not isinstance(path_text, str) or not path_text:
            failures.append(f"{owner}: evidence[{index}] path is required")
            continue
        path = Path(path_text)
        if path.is_absolute() or ".." in path.parts:
            failures.append(f"{owner}: evidence path must be repository-relative")
        elif not (ROOT / path).is_file():
            failures.append(f"{owner}: missing evidence path {path_text}")
        if not isinstance(detail, str) or not detail.strip():
            failures.append(f"{owner}: evidence[{index}] detail is required")


def validate_target(data: dict[str, Any], failures: list[str]) -> None:
    expected = {
        "lean_version": "4.30.0",
        "lean_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lean4export_version": "3.1.0",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "mathlib_version": "4.30.0",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
    }
    target = data.get("target")
    if not isinstance(target, dict):
        failures.append("target must be an object")
        return
    if target != expected:
        failures.append("target must match the exact pinned Lean/exporter/mathlib tuple")
    for key in ("lean_commit", "lean4export_commit", "mathlib_commit"):
        if not HEX40.fullmatch(str(target.get(key, ""))):
            failures.append(f"target {key} must be lowercase 40-hex")


def validate_definitions(data: dict[str, Any], failures: list[str]) -> None:
    expected = {
        "population_state_definitions": POPULATION_STATES,
        "axis_state_definitions": AXIS_STATES,
    }
    for field, states in expected.items():
        definitions = data.get(field)
        if not isinstance(definitions, dict) or set(definitions) != states:
            failures.append(f"{field} must define exactly {sorted(states)}")
        elif any(not isinstance(value, str) or not value.strip() for value in definitions.values()):
            failures.append(f"{field} definitions must be non-empty strings")


def validate_populations(data: dict[str, Any], failures: list[str]) -> dict[str, Any]:
    populations = data.get("populations")
    if not isinstance(populations, list):
        failures.append("populations must be a list")
        return {}
    ids = tuple(item.get("id") for item in populations if isinstance(item, dict))
    if ids != POPULATION_IDS:
        failures.append(f"population ids/order must be {POPULATION_IDS!r}")
    result: dict[str, Any] = {}
    for item in populations:
        if not isinstance(item, dict):
            failures.append("every population must be an object")
            continue
        population_id = str(item.get("id", "<unknown>"))
        result[population_id] = item
        for field in ("label", "owner", "residual"):
            if not isinstance(item.get(field), str) or not item[field].strip():
                failures.append(f"{population_id}: non-empty {field} is required")
        state = item.get("state")
        if item.get("label") != POPULATION_LABELS.get(population_id):
            failures.append(f"{population_id}: label must match the terminal contract")
        if state not in POPULATION_STATES:
            failures.append(f"{population_id}: invalid state {state!r}")
        complete = state == "complete_authority"
        raw = item.get("raw_denominator")
        normalized = item.get("normalized_denominator")
        digest = item.get("content_digest")
        if complete:
            if not isinstance(raw, int) or isinstance(raw, bool) or raw < 1:
                failures.append(f"{population_id}: complete authority needs raw denominator")
            if not isinstance(normalized, int) or isinstance(normalized, bool) or normalized < 1:
                failures.append(
                    f"{population_id}: complete authority needs normalized denominator"
                )
            if not HEX64.fullmatch(str(digest or "")):
                failures.append(f"{population_id}: complete authority needs content digest")
        elif any(value is not None for value in (raw, normalized, digest)):
            failures.append(
                f"{population_id}: incomplete authority cannot publish terminal "
                "denominators or digest"
            )
        validate_evidence(population_id, item.get("evidence"), failures, required=True)
    return result


def validate_axes(
    data: dict[str, Any], populations: dict[str, Any], failures: list[str]
) -> dict[str, Any]:
    axes = data.get("axes")
    if not isinstance(axes, list):
        failures.append("axes must be a list")
        return {}
    ids = tuple(item.get("id") for item in axes if isinstance(item, dict))
    if ids != AXIS_IDS:
        failures.append(f"axis ids/order must be {AXIS_IDS!r}")
    result: dict[str, Any] = {}
    population_order = {value: index for index, value in enumerate(POPULATION_IDS)}
    for item in axes:
        if not isinstance(item, dict):
            failures.append("every axis must be an object")
            continue
        axis_id = str(item.get("id", "<unknown>"))
        result[axis_id] = item
        for field in ("label", "owner", "residual"):
            if not isinstance(item.get(field), str) or not item[field].strip():
                failures.append(f"{axis_id}: non-empty {field} is required")
        state = item.get("state")
        if state not in AXIS_STATES:
            failures.append(f"{axis_id}: invalid state {state!r}")
        dependencies = item.get("populations")
        if not isinstance(dependencies, list) or not dependencies:
            failures.append(f"{axis_id}: populations must be a non-empty list")
            dependencies = []
        elif dependencies != sorted(set(dependencies), key=population_order.get):
            failures.append(f"{axis_id}: populations must be unique and in U0-U9 order")
        unknown = sorted(set(dependencies) - set(POPULATION_IDS))
        if unknown:
            failures.append(f"{axis_id}: unknown populations {unknown}")
        expected_contract = AXIS_CONTRACT.get(axis_id)
        if expected_contract is not None:
            expected_label, expected_populations = expected_contract
            if item.get("label") != expected_label:
                failures.append(f"{axis_id}: label must match the terminal contract")
            if tuple(dependencies) != tuple(expected_populations):
                failures.append(
                    f"{axis_id}: population dependencies must match the terminal contract"
                )
        evidence_required = state in {"partial", "complete"}
        validate_evidence(axis_id, item.get("evidence"), failures, required=evidence_required)
        if state == "not_started" and item.get("evidence"):
            failures.append(f"{axis_id}: not_started axis cannot carry parity-credit evidence")
        if state == "complete":
            incomplete = [
                population_id
                for population_id in dependencies
                if populations.get(population_id, {}).get("state") != "complete_authority"
            ]
            if incomplete:
                failures.append(
                    f"{axis_id}: complete axis depends on incomplete populations {incomplete}"
                )
    return result


def validate_paired_cells(data: dict[str, Any], failures: list[str]) -> list[dict[str, Any]]:
    outcomes = data.get("outcome_classes")
    if (tuple(outcomes) if isinstance(outcomes, list) else None) != OUTCOME_CLASSES:
        failures.append(f"outcome_classes/order must be {OUTCOME_CLASSES!r}")
    cells = data.get("paired_cells")
    if not isinstance(cells, list):
        failures.append("paired_cells must be a list")
        return []
    ids = [cell.get("id") for cell in cells if isinstance(cell, dict)]
    if ids != sorted(ids) or len(ids) != len(set(ids)):
        failures.append("paired cell ids must be unique and sorted")
    for cell in cells:
        if not isinstance(cell, dict):
            failures.append("every paired cell must be an object")
            continue
        cell_id = str(cell.get("id", "<unknown>"))
        if set(cell) != PAIRED_CELL_FIELDS:
            failures.append(f"{cell_id}: paired cell fields must be exact")
        if not CASE_ID.fullmatch(cell_id):
            failures.append(f"{cell_id}: invalid paired cell id")
        if cell.get("population") not in POPULATION_IDS:
            failures.append(f"{cell_id}: invalid population")
        if cell.get("axis") not in AXIS_IDS:
            failures.append(f"{cell_id}: invalid axis")
        if cell.get("outcome") not in OUTCOME_CLASSES:
            failures.append(f"{cell_id}: invalid outcome")
        digest_fields = (
            "source_sha256",
            "dependency_sha256",
            "official_executable_sha256",
            "official_configuration_sha256",
            "axeyum_executable_sha256",
            "axeyum_configuration_sha256",
            "command_sha256",
            "environment_sha256",
            "resource_envelope_sha256",
            "official_outcome_sha256",
            "axeyum_outcome_sha256",
            "official_assurance_sha256",
            "axeyum_assurance_sha256",
            "diagnostics_sha256",
        )
        for field in digest_fields:
            if not HEX64.fullmatch(str(cell.get(field, ""))):
                failures.append(f"{cell_id}: {field} must be lowercase 64-hex")
        for field in (
            "layer",
            "source_family",
            "normalization",
            "platform_id",
            "attempt_id",
        ):
            if not isinstance(cell.get(field), str) or not cell[field].strip():
                failures.append(f"{cell_id}: non-empty {field} is required")
        if cell.get("completed") is not True:
            failures.append(f"{cell_id}: terminal paired cell must be completed")
        for field in (
            "official_duration_ms",
            "axeyum_duration_ms",
            "official_peak_rss_kib",
            "axeyum_peak_rss_kib",
            "official_artifact_bytes",
            "axeyum_artifact_bytes",
        ):
            value = cell.get(field)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                failures.append(f"{cell_id}: {field} must be a non-negative integer")
        for field in ("official_evidence", "axeyum_evidence"):
            validate_evidence(cell_id + "." + field, cell.get(field), failures, required=True)
    return cells


def derived_gate_states(
    populations: dict[str, Any], axes: dict[str, Any], cells: list[dict[str, Any]]
) -> dict[str, bool]:
    complete_populations = bool(populations) and all(
        item.get("state") == "complete_authority" for item in populations.values()
    )
    complete_axes = bool(axes) and all(
        item.get("state") == "complete" for item in axes.values()
    )
    paired_agreement = bool(cells) and all(
        cell.get("outcome") in PARITY_OUTCOMES for cell in cells
    )
    return {"G1": complete_populations, "G2": complete_axes, "G3": paired_agreement}


def validate_gates(
    data: dict[str, Any],
    populations: dict[str, Any],
    axes: dict[str, Any],
    cells: list[dict[str, Any]],
    failures: list[str],
) -> bool:
    gates = data.get("terminal_gates")
    if not isinstance(gates, list):
        failures.append("terminal_gates must be a list")
        return False
    ids = tuple(gate.get("id") for gate in gates if isinstance(gate, dict))
    if ids != GATE_IDS:
        failures.append(f"terminal gate ids/order must be {GATE_IDS!r}")
    derived = derived_gate_states(populations, axes, cells)
    for gate in gates:
        if not isinstance(gate, dict):
            failures.append("every terminal gate must be an object")
            continue
        gate_id = str(gate.get("id", "<unknown>"))
        state = gate.get("state")
        if state not in GATE_STATES:
            failures.append(f"{gate_id}: invalid gate state {state!r}")
        for field in ("label", "residual"):
            if not isinstance(gate.get(field), str) or not gate[field].strip():
                failures.append(f"{gate_id}: non-empty {field} is required")
        if gate.get("label") != GATE_LABELS.get(gate_id):
            failures.append(f"{gate_id}: label must match the terminal contract")
        validate_evidence(
            gate_id,
            gate.get("evidence"),
            failures,
            required=state == "satisfied",
        )
        if gate_id in derived and (state == "satisfied") != derived[gate_id]:
            failures.append(f"{gate_id}: state disagrees with derived registry evidence")
    terminal_ready = bool(gates) and all(
        isinstance(gate, dict) and gate.get("state") == "satisfied" for gate in gates
    )
    claim_enabled = data.get("terminal_claim_enabled")
    if not isinstance(claim_enabled, bool):
        failures.append("terminal_claim_enabled must be boolean")
    elif claim_enabled != terminal_ready:
        failures.append("terminal_claim_enabled must exactly equal terminal gate readiness")
    return terminal_ready


def find_forbidden_claims(text: str) -> list[tuple[int, str]]:
    matches: list[tuple[int, str]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        normalized = line.translate(MARKDOWN_DECORATION)
        for pattern in AFFIRMATIVE_CLAIMS:
            match = pattern.search(normalized)
            if match:
                matches.append((line_number, match.group(0)))
                break
    return matches


def validate_claim_surfaces(
    data: dict[str, Any], terminal_ready: bool, failures: list[str]
) -> None:
    surfaces = data.get("claim_surfaces")
    expected = [
        "README.md",
        "docs/PROJECT-STATE.md",
        "docs/plan/README.md",
        "PLAN.md",
        "STATUS.md",
    ]
    if surfaces != expected:
        failures.append(f"claim_surfaces/order must be {expected!r}")
        return
    if terminal_ready:
        return
    for path_text in surfaces:
        path = ROOT / path_text
        if not path.is_file():
            failures.append(f"missing claim surface {path_text}")
            continue
        for line_number, claim in find_forbidden_claims(path.read_text(encoding="utf-8")):
            failures.append(
                f"forbidden terminal claim in {path_text}:{line_number}: {claim!r}"
            )


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if data.get("schema") != "axeyum-lean-complete-parity-v1":
        failures.append("schema must be axeyum-lean-complete-parity-v1")
    if data.get("as_of") != "2026-07-22":
        failures.append("as_of must be 2026-07-22")
    contract = data.get("contract")
    if contract != "docs/plan/lean4-complete-parity-contract-2026-07-22.md":
        failures.append("contract path drift")
    elif not (ROOT / contract).is_file():
        failures.append("contract path is missing")
    validate_target(data, failures)
    validate_definitions(data, failures)
    populations = validate_populations(data, failures)
    axes = validate_axes(data, populations, failures)
    cells = validate_paired_cells(data, failures)
    terminal_ready = validate_gates(data, populations, axes, cells, failures)
    validate_claim_surfaces(data, terminal_ready, failures)
    return failures


def compatibility_snapshot() -> dict[str, Any]:
    data = load_json(COMPATIBILITY)
    requirements = {profile["id"]: profile["requires"] for profile in data["profiles"]}
    totals: Counter[str] = Counter()
    satisfied: Counter[str] = Counter()
    for row in data["rows"]:
        profile_id = row["profile"]
        totals[profile_id] += 1
        if all(row["states"][field] == "succeeded" for field in requirements[profile_id]):
            satisfied[profile_id] += 1
    return {
        "rows": len(data["rows"]),
        "profiles": [
            {
                "id": profile["id"],
                "satisfied": satisfied[profile["id"]],
                "total": totals[profile["id"]],
            }
            for profile in data["profiles"]
        ],
    }


def construct_snapshot() -> dict[str, Any]:
    checker = load_script(
        "lean_construct_matrix_for_complete_parity",
        ROOT / "scripts" / "check-lean-official-construct-matrix.py",
    )
    rows = checker.derive_matrix_rows(load_json(CONSTRUCT_MATRIX))
    return {
        "rows": len(rows),
        "official_accepted": sum(row["official_source"] == "accepted" for row in rows),
        "official_rejected": sum(row["official_source"] == "rejected" for row in rows),
        "independently_admitted": sum(
            row["independent_admission"] == "yes" for row in rows
        ),
        "computation_checked": sum(row["computation"] == "checked" for row in rows),
        "current_declines": sum(
            row["rust_variant"] in {"Unsupported", "Malformed", "Kernel"}
            for row in rows
        ),
        "scope": "selected-family bounded evidence; not terminal paired cells",
    }


def axiom_snapshot() -> dict[str, Any]:
    data = load_json(AXIOM_LEDGER)
    classifications = Counter(entry["classification"] for entry in data["entries"])
    discharges = Counter(entry["discharge_status"] for entry in data["entries"])
    return {
        "rows": len(data["entries"]),
        "classifications": dict(sorted(classifications.items())),
        "discharge_statuses": dict(sorted(discharges.items())),
    }


def u2_test_snapshot() -> dict[str, Any]:
    checker = load_script(
        "lean_u2_test_authority_for_complete_parity",
        ROOT / "scripts" / "gen-lean-u2-test-authority.py",
    )
    data = load_json(U2_AUTHORITY)
    failures = checker.validate_manifest(data)
    if failures:
        raise RuntimeError("invalid U2 test authority: " + "; ".join(failures))
    report = checker.summarize(data)
    return {
        "scope": data["scope"],
        "profiles": report["profiles"],
        "selection_relation": report["selection_relation"],
        "content": report["content"],
        "kind_counts": report["kind_counts"],
        "output_policy_counts": report["output_policy_counts"],
        "outcomes": report["outcomes"],
    }


def u2_ci_profile_snapshot() -> dict[str, Any]:
    checker = load_script(
        "lean_u2_ci_profiles_for_complete_parity",
        ROOT / "scripts" / "gen-lean-u2-official-ci-profiles.py",
    )
    data = load_json(U2_CI_PROFILES)
    failures = checker.validate_manifest(data)
    if failures:
        raise RuntimeError("invalid U2 CI profile authority: " + "; ".join(failures))
    report = checker.summarize(data)
    return {
        "scope": data["scope"],
        "derivation": report["derivation"],
        "selection_sets": report["selection_sets"],
        "outcomes": report["outcomes"],
    }


def execution_evidence_snapshot() -> dict[str, Any]:
    checker = load_script(
        "lean_execution_evidence_for_complete_parity",
        ROOT / "scripts" / "gen-lean-execution-evidence.py",
    )
    data = load_json(EXECUTION_EVIDENCE)
    failures = checker.validate_authority(data)
    if failures:
        raise RuntimeError("invalid Lean execution evidence authority: " + "; ".join(failures))
    report = checker.summarize(data)
    return {
        "scope": data["scope"],
        "lane_policies": len(report["lane_policies"]),
        "termination_classes": len(report["termination_classes"]),
        "synthetic_controls": len(report["synthetic_controls"]),
        "mutation_classes": len(report["mutation_classes"]),
        "all_synthetic_controls_valid": all(
            item["valid"] for item in report["synthetic_controls"]
        ),
        "observed": report["observed"],
    }


def execution_process_snapshot() -> dict[str, Any]:
    checker = load_script(
        "lean_execution_process_for_complete_parity",
        ROOT / "scripts" / "lean_execution_process.py",
    )
    data = load_json(EXECUTION_PROCESS)
    failures = checker.validate_result_authority(data)
    if failures:
        raise RuntimeError("invalid Lean execution process authority: " + "; ".join(failures))
    return {
        "scope": data["scope"],
        "registered_controls": data["summary"]["registered_controls"],
        "retained_process_attempts": data["summary"]["retained_process_attempts"],
        "classification_counts": data["summary"]["classification_counts"],
        "retained_files": data["summary"]["retained_files"],
        "raw_artifacts": data["summary"]["raw_artifacts"],
        "case_records": data["summary"]["case_records"],
        "completion_records": data["summary"]["completion_records"],
        "credits": data["credits"],
    }


def task_snapshot() -> dict[str, Any]:
    rows = TASK_ROW.findall(IMPLEMENTATION_PLAN.read_text(encoding="utf-8"))
    counts = Counter(status for _, status in rows)
    return {
        "rows": len(rows),
        "status_counts": {
            status: counts[status] for status in ("DONE", "PARTIAL", "TODO", "BLOCKED")
        },
    }


def report_source_paths(data: dict[str, Any]) -> list[Path]:
    paths = {
        MANIFEST,
        COMPATIBILITY,
        CONSTRUCT_MATRIX,
        AXIOM_LEDGER,
        U2_AUTHORITY,
        U2_CI_PROFILES,
        EXECUTION_EVIDENCE,
        EXECUTION_PROCESS,
        IMPLEMENTATION_PLAN,
        ROOT / data["contract"],
        ROOT / "scripts" / "gen-lean-complete-parity.py",
        ROOT / "scripts" / "tests" / "test_lean_complete_parity.py",
        ROOT / "scripts" / "gen-lean-u2-test-authority.py",
        ROOT / "scripts" / "tests" / "test_lean_u2_test_authority.py",
        ROOT / "scripts" / "gen-lean-u2-official-ci-profiles.py",
        ROOT / "scripts" / "tests" / "test_lean_u2_official_ci_profiles.py",
        ROOT / "scripts" / "gen-lean-execution-evidence.py",
        ROOT / "scripts" / "tests" / "test_lean_execution_evidence.py",
        ROOT / "scripts" / "lean_execution_process.py",
        ROOT / "scripts" / "tests" / "test_lean_execution_process.py",
    }
    for collection in (data["populations"], data["axes"], data["terminal_gates"]):
        for item in collection:
            paths.update(ROOT / evidence["path"] for evidence in item["evidence"])
    for cell in data["paired_cells"]:
        for field in ("official_evidence", "axeyum_evidence"):
            paths.update(ROOT / evidence["path"] for evidence in cell[field])
    return sorted(paths, key=relative)


def build_report(data: dict[str, Any]) -> dict[str, Any]:
    population_counts = Counter(item["state"] for item in data["populations"])
    axis_counts = Counter(item["state"] for item in data["axes"])
    outcome_counts = Counter(cell["outcome"] for cell in data["paired_cells"])
    terminal_ready = all(gate["state"] == "satisfied" for gate in data["terminal_gates"])
    source_paths = report_source_paths(data)
    return {
        "schema": "axeyum-lean-complete-parity-report-v1",
        "generated_from": relative(MANIFEST),
        "source_identities": [
            {"path": relative(path), "sha256": sha256(path)} for path in source_paths
        ],
        "target": data["target"],
        "bounded_snapshot": {
            "compatibility": compatibility_snapshot(),
            "construct_matrix": construct_snapshot(),
            "axiom_ledger": axiom_snapshot(),
            "u2_test_authority": u2_test_snapshot(),
            "u2_ci_profile_authority": u2_ci_profile_snapshot(),
            "execution_evidence_authority": execution_evidence_snapshot(),
            "execution_process_authority": execution_process_snapshot(),
            "implementation_tasks": task_snapshot(),
        },
        "population_summary": {
            "total": len(data["populations"]),
            "state_counts": {
                state: population_counts[state]
                for state in (
                    "complete_authority",
                    "bounded_profile",
                    "inventory_only",
                    "not_registered",
                )
            },
        },
        "populations": data["populations"],
        "axis_summary": {
            "total": len(data["axes"]),
            "state_counts": {
                state: axis_counts[state]
                for state in ("complete", "partial", "not_started")
            },
        },
        "axes": data["axes"],
        "paired_summary": {
            "registered_cells": len(data["paired_cells"]),
            "required_fields": sorted(PAIRED_CELL_FIELDS),
            "outcome_counts": {
                outcome: outcome_counts[outcome] for outcome in OUTCOME_CLASSES
            },
            "terminal_population_registered": bool(data["paired_cells"]),
        },
        "paired_cells": data["paired_cells"],
        "terminal_gates": data["terminal_gates"],
        "claim_guard": {
            "surfaces": data["claim_surfaces"],
            "forbidden_claims": 0,
        },
        "terminal": {
            "ready": terminal_ready,
            "claim_enabled": data["terminal_claim_enabled"],
            "verdict": (
                "complete Lean 4.30 parity established"
                if terminal_ready
                else "complete Lean 4.30 parity not established"
            ),
        },
    }


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def evidence_links(evidence: list[dict[str, str]]) -> str:
    if not evidence:
        return "-"
    return "; ".join(
        f"[{Path(item['path']).name}](../../../{item['path']})"
        for item in evidence
    )


def render_markdown(report: dict[str, Any]) -> str:
    target = report["target"]
    bounded = report["bounded_snapshot"]
    compatibility = bounded["compatibility"]
    construct = bounded["construct_matrix"]
    axioms = bounded["axiom_ledger"]
    u2_tests = bounded["u2_test_authority"]
    u2_ci = bounded["u2_ci_profile_authority"]
    execution = bounded["execution_evidence_authority"]
    process = bounded["execution_process_authority"]
    tasks = bounded["implementation_tasks"]
    terminal = report["terminal"]
    claim_guard = report["claim_guard"]
    lines = [
        "# Lean 4 complete-parity registry",
        "",
        "> **Generated; do not edit by hand.** Sources are content-identified in the "
        "[machine-readable report](lean-complete-parity.json). Regenerate with "
        "`python3 scripts/gen-lean-complete-parity.py`; validate with `--check`.",
        "",
        f"> **Verdict: {terminal['verdict']}.** The unqualified terminal claim is "
        f"`{'enabled' if terminal['claim_enabled'] else 'disabled'}`.",
        "",
        "Inventory, a bounded profile, and a complete authority are different states. "
        "This report grants no terminal denominator, paired-cell, axis, or gate credit "
        "from file counts or selected examples.",
        "",
        "## Pinned target",
        "",
        f"- Lean `{target['lean_version']}` at `{target['lean_commit']}`.",
        f"- `lean4export` format `{target['lean4export_version']}` at "
        f"`{target['lean4export_commit']}`.",
        f"- mathlib `{target['mathlib_version']}` at `{target['mathlib_commit']}`.",
        "",
        "## Derived bounded snapshot",
        "",
        "These facts are regenerated from existing manifests. They are scoped evidence, "
        "not a terminal population denominator.",
        "",
        f"- Compatibility contract: {compatibility['rows']} rows.",
    ]
    for profile in compatibility["profiles"]:
        lines.append(
            f"  - `{profile['id']}`: {profile['satisfied']}/{profile['total']} rows "
            "satisfy that bounded profile."
        )
    lines.extend(
        [
            f"- Selected construct matrix: {construct['rows']} rows; "
            f"{construct['official_accepted']} official accepts, "
            f"{construct['official_rejected']} official rejects, "
            f"{construct['independently_admitted']} independently admitted, "
            f"{construct['computation_checked']} computation-checked, and "
            f"{construct['current_declines']} current declines.",
            f"- Axiom ledger: {axioms['rows']} rows; "
            + ", ".join(
                f"`{key}`={value}" for key, value in axioms["classifications"].items()
            )
            + ".",
            f"- U2 registration authority: "
            f"{u2_tests['profiles'][0]['registered']} default and "
            f"{u2_tests['profiles'][1]['registered']} full-Lake CTest cases; "
            f"{u2_tests['outcomes']['official_executed']} official executions, "
            f"{u2_tests['outcomes']['axeyum_executed']} Axeyum executions, and "
            f"{u2_tests['outcomes']['paired_registered']} paired cells. "
            "This is bounded registration evidence, not complete U2 authority.",
            f"- U2 official CI profiles: {u2_ci['derivation']['contexts']} contexts, "
            f"{u2_ci['derivation']['candidate_cells']} cells, "
            f"{u2_ci['derivation']['ctest_attempts']} not-run CTest attempts, and "
            f"{u2_ci['derivation']['selection_sets']} exact selection sets; "
            f"{u2_ci['outcomes']['official_executed_attempts']} official executions "
            "and zero parity credit.",
            f"- Lean execution evidence: {execution['lane_policies']} lane templates, "
            f"{execution['termination_classes']} termination classes, "
            f"{execution['synthetic_controls']} synthetic controls, and "
            f"{execution['mutation_classes']} mutation classes; "
            f"{execution['observed']['real_runs']} real runs and zero parity credit.",
            f"- Lean process controls: {process['retained_process_attempts']}/"
            f"{process['registered_controls']} retained synthetic attempts, "
            f"{process['retained_files']} exact files, and {process['raw_artifacts']} raw streams; "
            f"{process['case_records']} case records, {process['completion_records']} completion "
            f"records, {process['credits']['real_runs']} real runs, and zero parity credit.",
            f"- Implementation ledger: {tasks['rows']} rows; "
            + ", ".join(
                f"`{key}`={value}" for key, value in tasks["status_counts"].items()
            )
            + ".",
            "",
            "## U0-U9 population authorities",
            "",
            "| Population | Scope | Owner | State | Raw denominator | Normalized "
            "denominator | Evidence | Residual |",
            "|---|---|---|---|---:|---:|---|---|",
        ]
    )
    for item in report["populations"]:
        raw = "-" if item["raw_denominator"] is None else str(item["raw_denominator"])
        normalized = (
            "-" if item["normalized_denominator"] is None else str(item["normalized_denominator"])
        )
        lines.append(
            f"| `{item['id']}` | {md_escape(item['label'])} | `{item['owner']}` | "
            f"`{item['state']}` | {raw} | {normalized} | "
            f"{evidence_links(item['evidence'])} | {md_escape(item['residual'])} |"
        )
    lines.extend(
        [
            "",
            "## A0-A11 behavioral axes",
            "",
            "| Axis | Scope | Owner | State | Required populations | Evidence | Residual |",
            "|---|---|---|---|---|---|---|",
        ]
    )
    for item in report["axes"]:
        populations = ", ".join(f"`{value}`" for value in item["populations"])
        lines.append(
            f"| `{item['id']}` | {md_escape(item['label'])} | `{item['owner']}` | "
            f"`{item['state']}` | {populations} | {evidence_links(item['evidence'])} | "
            f"{md_escape(item['residual'])} |"
        )
    paired = report["paired_summary"]
    lines.extend(
        [
            "",
            "## Paired terminal cells",
            "",
            f"Registered terminal cells: **{paired['registered_cells']}**. "
            "The selected construct matrix remains bounded evidence until complete "
            "population identity, paired official/Axeyum execution, normalization, "
            "and source/dependency identity are registered.",
            "",
            "| Outcome | Count |",
            "|---|---:|",
        ]
    )
    for outcome, count in paired["outcome_counts"].items():
        lines.append(f"| `{outcome}` | {count} |")
    lines.extend(
        [
            "",
            "## Terminal gates",
            "",
            "| Gate | Requirement | State | Residual |",
            "|---|---|---|---|",
        ]
    )
    for gate in report["terminal_gates"]:
        lines.append(
            f"| `{gate['id']}` | {md_escape(gate['label'])} | `{gate['state']}` | "
            f"{md_escape(gate['residual'])} |"
        )
    lines.extend(
        [
            "",
            "## Enforced non-claims",
            "",
            "- An incomplete population cannot publish terminal raw/normalized "
            "denominators or a terminal content digest.",
            "- A complete axis cannot depend on an incomplete population.",
            "- A terminal paired cell requires exact source and dependency digests, "
            "normalization, source family, executable/configuration, command, "
            "environment, platform, resource, attempt, completion, outcome, "
            "assurance, diagnostics, timing, RSS, artifact-size, and both evidence "
            "sides.",
            "- G1-G3 are derived from population, axis, and paired-cell states; they "
            "cannot be hand-promoted.",
            "- The terminal claim switch must exactly match all ten gate states.",
            "- A satisfied terminal gate must retain evidence.",
            f"- While the terminal gate is open, {len(claim_guard['surfaces'])} "
            "live public status surfaces are scanned for affirmative complete-parity "
            "claims; the current scan found "
            f"{claim_guard['forbidden_claims']}.",
            "",
        ]
    )
    return "\n".join(lines)


def write_or_check(path: Path, content: str, check: bool, failures: list[str]) -> None:
    if check:
        if not path.is_file():
            failures.append(f"missing generated file: {relative(path)}")
        elif path.read_text(encoding="utf-8") != content:
            failures.append(
                f"stale generated file: {relative(path)}; run "
                "python3 scripts/gen-lean-complete-parity.py"
            )
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail on stale outputs")
    args = parser.parse_args()
    data = load_manifest()
    failures = validate_manifest(data)
    if failures:
        for failure in failures:
            print(f"LEAN_COMPLETE_PARITY_ERROR|{failure}", file=sys.stderr)
        return 1

    report = build_report(data)
    rendered_json = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    rendered_md = render_markdown(report)
    output_failures: list[str] = []
    write_or_check(OUT_JSON, rendered_json, args.check, output_failures)
    write_or_check(OUT_MD, rendered_md, args.check, output_failures)
    if output_failures:
        for failure in output_failures:
            print(f"LEAN_COMPLETE_PARITY_ERROR|{failure}", file=sys.stderr)
        return 1

    complete_population_count = report["population_summary"]["state_counts"][
        "complete_authority"
    ]
    print(
        "LEAN_COMPLETE_PARITY|"
        f"populations={len(data['populations'])}|"
        f"complete_populations={complete_population_count}|"
        f"axes={len(data['axes'])}|"
        f"complete_axes={report['axis_summary']['state_counts']['complete']}|"
        f"paired_cells={report['paired_summary']['registered_cells']}|"
        f"gates_satisfied={sum(gate['state'] == 'satisfied' for gate in data['terminal_gates'])}|"
        f"terminal_ready={str(report['terminal']['ready']).lower()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
