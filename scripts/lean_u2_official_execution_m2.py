#!/usr/bin/env python3
"""Validate the source-first TL0.6.3 M2 64-case execution contract offline.

This module deliberately exposes no live execution command.  It validates the
frozen inputs and implements the pure spec, harness, discovery, JUnit, artifact,
and credit projections that a later separately committed runner must use.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import re
import sys
import xml.etree.ElementTree as ET
from collections import Counter
from functools import lru_cache
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_r2 as R2  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md"
)
PREREGISTRATION_COMMIT = "16bd6f08cfd5f20e3889969f4d026a27e712fe60"
PLAN_SHA256 = "4cef4ba9c57820f5bff82e4cfdfdc524b3d0d54665a947cf2b27560767ec81dd"

U2_PATH = ROOT / "docs/plan/lean-u2-test-authority-v1.json"
PROFILES_PATH = ROOT / "docs/plan/lean-u2-official-ci-profiles-v1.json"
SHARDS_PATH = ROOT / "docs/plan/lean-u2-official-child-shards-v1.json"

REPOSITORY_INPUTS = {
    "docs/plan/lean-u2-official-child-shards-v1.json": (
        "6a2ec0b3edd353f3deb76e805052d5d2465ed1c9dd59cf221b0d175d0ce5e3e9"
    ),
    "docs/plan/lean-u2-test-authority-v1.json": (
        "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e"
    ),
    "docs/plan/lean-u2-official-ci-profiles-v1.json": (
        "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548"
    ),
    "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json": (
        "fe04cd96fb9f08c8a0e834ec11f954c3c8172912332da28fc2a92adf0cedb475"
    ),
    "docs/plan/lean-execution-evidence-v1.json": (
        "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a"
    ),
    "docs/plan/lean-execution-process-v1.json": (
        "0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf"
    ),
    "docs/plan/lean-execution-store-v1.json": (
        "e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647"
    ),
    "docs/plan/lean-execution-acceptance-v1.json": (
        "bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f"
    ),
    "scripts/lean_u2_official_execution.py": (
        "47c779d5b465e32b1ffa8faf3598472ed2ac98bd058928494e65a68d4f205fc2"
    ),
    "scripts/lean_u2_official_execution_r3.py": (
        "061a7eca2e54f274c7289de4217d80db9a02f8e6f611f31667f7f01f059d835d"
    ),
    "scripts/lean_execution_process.py": (
        "96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007"
    ),
    "scripts/lean_execution_store.py": (
        "06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679"
    ),
}

CHILD_VALIDATOR = ROOT / "scripts/gen-lean-u2-official-child-shards.py"
CHILD_VALIDATOR_SHA256 = (
    "e1f6bb869fe5fb6ec740589d6e3b0f514e6efbc5604b0010bdd9dd44e10434a3"
)

LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
PARENT_CONTEXT_ID = "release-tag-l3"
PARENT_CONTEXT_SHA256 = "a2757855ea11633699e982418e53ae86f7b8e6807764202bcc06a7eeb83463c2"
PARENT_CELL_ID = "release-tag-l3--linux-release"
PARENT_CELL_SHA256 = "4da2ce61fca4141c2b963bc3dc94610ceebd9fee9059d45607cd8a23a621519b"
PARENT_ATTEMPT_ID = "release-tag-l3--linux-release--primary"
PARENT_ATTEMPT_SHA256 = "21e8b9540f42f4ea86c0eb52985b28b09cdd2c4ebb31cd34d723eaac028a48a3"
PARENT_SELECTION_ID = "default-filtered-aec7358564e4"
PARENT_SELECTION_SHA256 = "02132086eb928c862eb19e3523b376342b869d5a159b67f2afecdf3b80db46c2"
PARENT_SELECTED_COUNT = 3_678
MEMBERSHIP_ID = (
    "membership-6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488"
)
SHARD_ID = MEMBERSHIP_ID + "--shard-0001"
SHARD_SHA256 = "642dae1bf4141647af80aa1f8be2af1903ca9e132e48fe838237395df3df82da"
SHARD_CASE_IDS_SHA256 = (
    "22fe1346f37d1ff0c5fce9730f526f62f13248558b5463c087fa3b8569531c7c"
)
SHARD_CASE_COUNT = 64
RUN_ID = "tl0.6.3-m2-release-linux-shard-0001-v1"
ATTEMPT_ID = "attempt-001"
SEQUENCE = 1
LANE_ID = "official-ctest-local-8g-lean-j1-shard64-v1"
MEMORY_LIMIT_BYTES = 8_589_934_592
WALL_TIMEOUT_MS = 3_600_000
TERMINATE_GRACE_MS = 1_000

SPEC_SCHEMA = "axeyum-lean-u2-official-execution-m2-spec-v1"
HARNESS_SCHEMA = "axeyum-lean-u2-official-execution-m2-harness-v1"
JUNIT_SCHEMA = "axeyum-lean-u2-official-execution-m2-junit-v1"
POST_SCHEMA = "axeyum-lean-u2-official-execution-m2-post-v1"
PROJECTION_SCHEMA = "axeyum-lean-u2-official-execution-m2-projection-v1"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")

ZERO_TERMINAL_CREDITS = {
    "parent_profile_completions": 0,
    "official_attempt_completions": 0,
    "official_provider_completions": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}


class M2ContractError(ValueError):
    """A frozen-input or pure M2 contract check failed."""


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise M2ContractError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_json(path: Path) -> dict[str, Any]:
    value = BASE.load_json(path)
    if not isinstance(value, dict):
        raise M2ContractError(f"top-level authority must be an object: {path}")
    return value


def validate_repository_inputs() -> list[str]:
    failures = []
    if not PLAN.is_file() or BASE.sha256_file(PLAN) != PLAN_SHA256:
        failures.append("M2 preregistration plan drift")
    for relative, expected in REPOSITORY_INPUTS.items():
        path = ROOT / relative
        if not path.is_file() or BASE.sha256_file(path) != expected:
            failures.append(f"frozen M2 repository input drift: {relative}")
    if (
        not CHILD_VALIDATOR.is_file()
        or BASE.sha256_file(CHILD_VALIDATOR) != CHILD_VALIDATOR_SHA256
    ):
        failures.append("frozen child-shard validator drift")
    return failures


@lru_cache(maxsize=1)
def validated_authorities() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    failures = validate_repository_inputs()
    if failures:
        raise M2ContractError("; ".join(failures))
    u2 = load_json(U2_PATH)
    profiles = load_json(PROFILES_PATH)
    shards = load_json(SHARDS_PATH)
    checker = load_script("lean_u2_m2_child_validator", CHILD_VALIDATOR)
    child_failures = checker.validate_authority(shards)
    if child_failures:
        raise M2ContractError("invalid M1 child-shard authority: " + "; ".join(child_failures))
    return u2, profiles, shards


def _one(rows: list[dict[str, Any]], label: str) -> dict[str, Any]:
    if len(rows) != 1:
        raise M2ContractError(f"{label} must resolve exactly once")
    return rows[0]


@lru_cache(maxsize=1)
def selected_contract() -> dict[str, Any]:
    u2, profiles, shards = validated_authorities()
    membership = _one(
        [row for row in shards["membership_plans"] if row["id"] == MEMBERSHIP_ID],
        "M2 membership",
    )
    selection = _one(
        [
            row
            for row in profiles["selection_sets"]
            if row["id"] == PARENT_SELECTION_ID
        ],
        "M2 selection",
    )
    attempt = _one(
        [row for row in profiles["attempts"] if row["id"] == PARENT_ATTEMPT_ID],
        "M2 parent attempt",
    )
    cell = _one(
        [row for row in profiles["cells"] if row["id"] == PARENT_CELL_ID],
        "M2 parent cell",
    )
    context = _one(
        [row for row in profiles["contexts"] if row["id"] == PARENT_CONTEXT_ID],
        "M2 parent context",
    )
    shard = _one(
        [row for row in shards["shards"] if row["id"] == SHARD_ID],
        "M2 shard",
    )
    eligible = [
        row
        for row in shards["shards"]
        if row["membership_plan_id"] == MEMBERSHIP_ID
        and row["historical_observation_case_ids"] == []
    ]
    if not eligible or min(row["ordinal"] for row in eligible) != shard["ordinal"]:
        raise M2ContractError("M2 shard is not the lowest-ordinal zero-history shard")
    expected_parent = {
        "context": (context["id"], context["sha256"]),
        "cell": (cell["id"], cell["sha256"]),
        "attempt": (attempt["id"], attempt["sha256"]),
        "selection": (selection["id"], selection["sha256"]),
    }
    observed_parent = {
        "context": (PARENT_CONTEXT_ID, PARENT_CONTEXT_SHA256),
        "cell": (PARENT_CELL_ID, PARENT_CELL_SHA256),
        "attempt": (PARENT_ATTEMPT_ID, PARENT_ATTEMPT_SHA256),
        "selection": (PARENT_SELECTION_ID, PARENT_SELECTION_SHA256),
    }
    if expected_parent != observed_parent:
        raise M2ContractError("M2 parent provenance identity drift")
    if (
        selection["selected_count"] != PARENT_SELECTED_COUNT
        or selection["selected_ids_sha256"] != membership["selected_ids_sha256"]
        or not isinstance(selection["selected_case_ids"], list)
        or membership["selection_set_ids"].count(PARENT_SELECTION_ID) != 1
    ):
        raise M2ContractError("M2 parent selection or membership drift")
    if (
        shard["record_sha256"] != SHARD_SHA256
        or shard["case_ids_sha256"] != SHARD_CASE_IDS_SHA256
        or shard["case_count"] != SHARD_CASE_COUNT
        or shard["ordinal"] != 1
        or shard["start_offset"] != 64
        or shard["end_offset"] != 128
        or shard["historical_observation_case_ids"] != []
        or shard["case_ids"] != selection["selected_case_ids"][64:128]
    ):
        raise M2ContractError("M2 shard identity, order, offset, or history drift")
    case_by_id = {row["id"]: row for row in u2["cases"]}
    if len(case_by_id) != len(u2["cases"]):
        raise M2ContractError("U2 case IDs are duplicated")
    try:
        cases = [case_by_id[case_id] for case_id in shard["case_ids"]]
    except KeyError as error:
        raise M2ContractError(f"M2 shard references unknown case: {error}") from error
    shape = Counter((row["family"], row["kind"], row["output_policy"]) for row in cases)
    expected_shape = Counter(
        {
            ("compile", "pile", "empty"): 2,
            ("compile", "pile", "exact"): 3,
            ("compile_bench", "pile", "empty"): 4,
            ("compile_bench", "pile", "exact"): 20,
            ("docparse", "pile", "exact"): 35,
        }
    )
    if shape != expected_shape:
        raise M2ContractError("M2 family/kind/output-policy aggregate drift")
    return {
        "target": profiles["target"],
        "context": context,
        "cell": cell,
        "attempt": attempt,
        "selection": selection,
        "membership": membership,
        "shard": shard,
        "cases": cases,
    }
def resource_envelope() -> dict[str, Any]:
    return {
        "lane_id": LANE_ID,
        "memory_limit": BASE.metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
        "memory_scope": "per-process-address-space",
        "memory_enforcement": "explicit-rlimit-as",
        "ctest_worker_limit": BASE.metric("observed", 1, "workers"),
        "ctest_worker_enforcement": "explicit-command-argument",
        "lean_shell_worker_limit": BASE.metric("observed", 1, "workers"),
        "lean_shell_worker_enforcement": "explicit-official-test-argument-array",
        "generated_runtime_worker_limit": BASE.metric("requested", 1, "workers"),
        "generated_runtime_worker_enforcement": "LEAN_NUM_THREADS",
        "os_thread_limit": BASE.metric("not-enforced", None, "threads"),
        "task_stack_limit": BASE.metric("not-observed", None, "bytes"),
        "task_stack_policy": "unmodified-Lean-default-no-s-option",
        "per_test_timeout": BASE.metric("not-enforced", None, "milliseconds"),
        "aggregate_memory_limit": BASE.metric("not-enforced", None, "bytes"),
        "pid_limit": BASE.metric("not-enforced", None, "processes"),
        "swap_limit": BASE.metric("not-enforced", None, "bytes"),
        "disk_limit": BASE.metric("not-enforced", None, "bytes"),
        "wall_timeout": BASE.metric("observed", WALL_TIMEOUT_MS, "milliseconds"),
        "terminate_grace": BASE.metric("observed", TERMINATE_GRACE_MS, "milliseconds"),
        "official_provider_claimed": False,
        "performance_credit": False,
    }


def build_spec(
    *,
    implementation_revision: str,
    source_root: Path,
    toolchain_root: Path,
    harness_build: Path,
    junit_path: Path,
) -> dict[str, Any]:
    if not HEX40.fullmatch(implementation_revision):
        raise M2ContractError("implementation revision must be a full Git hash")
    contract = selected_contract()
    source = source_root.resolve()
    toolchain = toolchain_root.resolve()
    harness = harness_build.resolve()
    junit = junit_path.resolve()
    case_refs = [
        {"id": row["id"], "registration_sha256": row["sha256"]}
        for row in contract["cases"]
    ]
    command = [
        "/usr/bin/ctest",
        "--preset",
        "release",
        "--test-dir",
        str(harness),
        "-j1",
        "--output-junit",
        str(junit),
        "-E",
        "foreign",
    ]
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "LEAN_NUM_THREADS": "1",
        "PATH": f"{toolchain / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    return BASE.seal(
        {
            "schema": SPEC_SCHEMA,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "implementation_revision": implementation_revision,
            "target_commit": LEAN_COMMIT,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "shard_id": SHARD_ID,
            "shard_sha256": SHARD_SHA256,
            "shard_case_ids_sha256": SHARD_CASE_IDS_SHA256,
            "parent": {
                "context_id": PARENT_CONTEXT_ID,
                "context_sha256": PARENT_CONTEXT_SHA256,
                "cell_id": PARENT_CELL_ID,
                "cell_sha256": PARENT_CELL_SHA256,
                "attempt_id": PARENT_ATTEMPT_ID,
                "attempt_sha256": PARENT_ATTEMPT_SHA256,
                "selection_id": PARENT_SELECTION_ID,
                "selection_sha256": PARENT_SELECTION_SHA256,
                "selected_count": PARENT_SELECTED_COUNT,
                "completed": False,
            },
            "case_refs": case_refs,
            "source_root": str(source),
            "toolchain_root": str(toolchain),
            "harness_build": str(harness),
            "junit_path": str(junit),
            "command": command,
            "working_directory": str(source),
            "environment": environment,
            "forbidden_environment_keys": ["LEAN_CC", "PYTHONPATH", "TEST_BENCH"],
            "resource_envelope": resource_envelope(),
            "credit_class": "local-official-shard-outcomes-only",
            "record_sha256": "",
        },
        SPEC_SCHEMA,
    )


def validate_spec(spec: Any) -> list[str]:
    if not BASE.valid_seal(spec, SPEC_SCHEMA):
        return ["M2 spec identity drift"]
    if not isinstance(spec, dict):
        return ["M2 spec must be an object"]
    failures = []
    try:
        expected = build_spec(
            implementation_revision=spec["implementation_revision"],
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_build=Path(spec["harness_build"]),
            junit_path=Path(spec["junit_path"]),
        )
    except (KeyError, TypeError, M2ContractError) as error:
        return [f"M2 spec cannot be reconstructed: {error}"]
    if spec != expected:
        failures.append("M2 spec command, path, environment, shard, resource, or credit drift")
    environment = spec.get("environment", {})
    if any(key in environment for key in spec.get("forbidden_environment_keys", [])):
        failures.append("M2 spec contains a forbidden environment override")
    return failures


def render_environment_wrapper(source_root: Path, toolchain_root: Path) -> bytes:
    wrapper = R2.render_environment_wrapper(source_root, toolchain_root)
    forbidden = (b"LEAN_CC", b"TEST_BENCH", b"PYTHONPATH", b"-s524288")
    if any(item in wrapper for item in forbidden):
        raise M2ContractError("M2 wrapper contains a forbidden execution override")
    if wrapper.count(b"TEST_LEAN_ARGS=(-j1)") != 1 or wrapper.count(
        b"TEST_LEANI_ARGS=(-j1)"
    ) != 1:
        raise M2ContractError("M2 wrapper worker arrays drift")
    return wrapper


def _replace_token(value: str, roots: dict[str, Path]) -> str:
    for token, root in roots.items():
        if value == token:
            return str(root)
        prefix = token + "/"
        if value.startswith(prefix):
            return str(root / value[len(prefix) :])
    if "$" in value:
        raise M2ContractError(f"unresolved registration token: {value}")
    return value


def resolved_registration(
    case: dict[str, Any],
    *,
    source_root: Path,
    toolchain_root: Path,
    harness_root: Path,
) -> dict[str, Any]:
    roots = {
        "$BASH": Path("/usr/bin/bash"),
        "$LEAN_ROOT": source_root.resolve(),
        "$HARNESS_ROOT": harness_root.resolve(),
        "$BUILD_ROOT": toolchain_root.resolve(),
        "$PYTHON3": Path("/usr/bin/python3.14"),
    }
    registration = case["registration"]
    command = [_replace_token(item, roots) for item in registration["command"]]
    properties = [
        {"name": row["name"], "value": _replace_token(row["value"], roots)}
        for row in registration["properties"]
    ]
    if command[0] != "/usr/bin/bash":
        raise M2ContractError(f"{case['id']}: M2 supports only the frozen Bash registrations")
    return {"id": case["id"], "command": command, "properties": properties}


def _cmake_arg(value: str) -> str:
    if "]=]" in value or "\x00" in value or "\n" in value or "\r" in value:
        raise M2ContractError("registration value is not representable as a CMake bracket argument")
    return f"[=[{value}]=]"


def expected_registrations(
    *, source_root: Path, toolchain_root: Path, harness_root: Path
) -> list[dict[str, Any]]:
    return [
        resolved_registration(
            case,
            source_root=source_root,
            toolchain_root=toolchain_root,
            harness_root=harness_root,
        )
        for case in selected_contract()["cases"]
    ]


def render_ctest_file(
    *, source_root: Path, toolchain_root: Path, harness_root: Path
) -> bytes:
    lines = []
    for row in expected_registrations(
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    ):
        args = " ".join(_cmake_arg(item) for item in [row["id"], *row["command"]])
        lines.append(f"add_test({args})")
        properties = row["properties"]
        if properties:
            fields = []
            for item in properties:
                fields.extend((_cmake_arg(item["name"]), _cmake_arg(item["value"])))
            lines.append(
                f"set_tests_properties({_cmake_arg(row['id'])} PROPERTIES "
                + " ".join(fields)
                + ")"
            )
    return ("\n".join(lines) + "\n").encode("utf-8")


def normalize_discovery(
    payload: Any, *, source_root: Path, toolchain_root: Path, harness_root: Path
) -> list[dict[str, Any]]:
    if not isinstance(payload, dict) or not isinstance(payload.get("tests"), list):
        raise M2ContractError("malformed CTest discovery JSON")
    expected = expected_registrations(
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    )
    tests = payload["tests"]
    if len(tests) != SHARD_CASE_COUNT:
        raise M2ContractError("CTest discovery count drift")
    observed = []
    for index, (test, wanted) in enumerate(zip(tests, expected)):
        if not isinstance(test, dict):
            raise M2ContractError(f"CTest discovery row {index} is not an object")
        properties = test.get("properties", [])
        if not isinstance(properties, list):
            raise M2ContractError(f"CTest discovery row {index} properties are malformed")
        projected = []
        for item in properties:
            if not isinstance(item, dict) or set(item) != {"name", "value"}:
                raise M2ContractError(f"CTest discovery row {index} property is malformed")
            projected.append({"name": item["name"], "value": item["value"]})
        row = {
            "id": test.get("name"),
            "command": test.get("command"),
            "properties": projected,
        }
        if row != wanted:
            raise M2ContractError(f"CTest discovery row {index} identity or order drift")
        observed.append(row)
    return observed


def build_harness_record(
    *,
    source_root: Path,
    toolchain_root: Path,
    harness_root: Path,
    discovery_payload: dict[str, Any],
) -> dict[str, Any]:
    wrapper = render_environment_wrapper(source_root, toolchain_root)
    ctest = render_ctest_file(
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    )
    discovery = normalize_discovery(
        discovery_payload,
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    )
    return BASE.seal(
        {
            "schema": HARNESS_SCHEMA,
            "shard_id": SHARD_ID,
            "case_count": SHARD_CASE_COUNT,
            "case_ids_sha256": SHARD_CASE_IDS_SHA256,
            "wrapper": {
                "bytes": len(wrapper),
                "sha256": BASE.sha256_bytes(wrapper),
                "mode": 0o755,
            },
            "ctest_file": {
                "bytes": len(ctest),
                "sha256": BASE.sha256_bytes(ctest),
            },
            "discovery": discovery,
            "discovery_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-discovery-v1", discovery
            ),
            "record_sha256": "",
        },
        HARNESS_SCHEMA,
    )


def _xml_name(element: ET.Element) -> str:
    return element.tag.rsplit("}", 1)[-1]


def _count(value: str | None, label: str) -> int:
    if value is None or not value.isdigit():
        raise M2ContractError(f"JUnit {label} count is missing or invalid")
    return int(value)


def _duration(value: str | None) -> str | None:
    if value is None:
        return None
    try:
        parsed = float(value)
    except ValueError as error:
        raise M2ContractError("JUnit duration is invalid") from error
    if not (0.0 <= parsed < float("inf")):
        raise M2ContractError("JUnit duration is invalid")
    return value


def parse_junit(raw: bytes, terminal: dict[str, Any]) -> dict[str, Any]:
    try:
        root = ET.fromstring(raw)
    except ET.ParseError as error:
        raise M2ContractError("malformed JUnit XML") from error
    if _xml_name(root) == "testsuite":
        suites = [root]
    elif _xml_name(root) == "testsuites":
        suites = [item for item in root if _xml_name(item) == "testsuite"]
        if len(suites) != len(list(root)):
            raise M2ContractError("JUnit root has non-suite children")
    else:
        raise M2ContractError("JUnit root is not testsuite/testsuites")
    if len(suites) != 1:
        raise M2ContractError("JUnit must contain exactly one suite")
    suite = suites[0]
    tests = _count(suite.get("tests"), "tests")
    failures = _count(suite.get("failures"), "failures")
    errors = _count(suite.get("errors", "0"), "errors")
    skipped = _count(suite.get("skipped", "0"), "skipped")
    disabled = _count(suite.get("disabled", "0"), "disabled")
    testcases = [item for item in suite if _xml_name(item) == "testcase"]
    expected_ids = selected_contract()["shard"]["case_ids"]
    if tests != SHARD_CASE_COUNT or len(testcases) != SHARD_CASE_COUNT:
        raise M2ContractError("JUnit does not contain exactly 64 cases")
    if skipped != 0 or disabled != 0 or failures + errors > SHARD_CASE_COUNT:
        raise M2ContractError("JUnit contains skipped/not-run or impossible outcomes")
    rows = []
    observed_failures = 0
    for index, (testcase, case_id) in enumerate(zip(testcases, expected_ids)):
        if testcase.get("name") != case_id:
            raise M2ContractError(f"JUnit case {index} identity or order drift")
        failure_nodes = [
            item for item in testcase if _xml_name(item) in {"failure", "error"}
        ]
        skipped_nodes = [item for item in testcase if _xml_name(item) == "skipped"]
        if skipped_nodes or len(failure_nodes) > 1:
            raise M2ContractError(f"JUnit case {case_id} is skipped or multiply failed")
        outcome = "failed" if failure_nodes else "passed"
        observed_failures += int(outcome == "failed")
        rows.append(
            {
                "id": case_id,
                "classname": testcase.get("classname"),
                "duration_seconds_text": _duration(
                    testcase.get("time", suite.get("time"))
                ),
                "outcome": outcome,
            }
        )
    if observed_failures != failures + errors:
        raise M2ContractError("JUnit child and aggregate outcomes disagree")
    process = terminal.get("process", {}) if isinstance(terminal, dict) else {}
    clean_group = (
        terminal.get("class") == "exited"
        and terminal.get("signal") is None
        and process.get("watchdog_fired") is False
        and process.get("direct_child_reaped") is True
        and process.get("live_non_zombie_pids_after_cleanup") == []
    )
    expected_exit = 0 if observed_failures == 0 else 8
    if not clean_group or terminal.get("exit_code") != expected_exit:
        raise M2ContractError("JUnit aggregate disagrees with the CTest terminal")
    summary = {
        "official_cases": SHARD_CASE_COUNT,
        "official_outcomes": SHARD_CASE_COUNT,
        "official_passes": SHARD_CASE_COUNT - observed_failures,
        "official_failures": observed_failures,
    }
    return BASE.seal(
        {
            "schema": JUNIT_SCHEMA,
            "raw": {
                "path": "raw/junit.xml",
                "bytes": len(raw),
                "sha256": BASE.sha256_bytes(raw),
            },
            "suite_name": suite.get("name"),
            "cases": rows,
            "cases_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-junit-cases-v1", rows
            ),
            "summary": summary,
            "terminal_sha256": terminal["record_sha256"],
            "record_sha256": "",
        },
        JUNIT_SCHEMA,
    )


def case_generated_paths(case: dict[str, Any]) -> list[str]:
    source = case["source_path"]
    sidecars = set(case["sidecars"])
    no_compile = any(
        source + suffix in sidecars
        for suffix in (".no_compile_test", ".no_compile")
    )
    paths = [source + ".out.produced"]
    if not no_compile:
        paths.extend((source + ".c", source + ".out"))
    return sorted(paths)


def declared_generated_paths() -> list[str]:
    paths = {"tests/with_stage1_test_env.sh", *BASE.CTEST_SOURCE_PATHS}
    for case in selected_contract()["cases"]:
        paths.update(case_generated_paths(case))
    return sorted(paths)


def validate_junit_projection(junit: Any) -> list[str]:
    if not BASE.valid_seal(junit, JUNIT_SCHEMA):
        return ["M2 JUnit projection identity drift"]
    failures = []
    cases = junit.get("cases", [])
    expected_ids = selected_contract()["shard"]["case_ids"]
    if (
        not isinstance(cases, list)
        or [row.get("id") for row in cases if isinstance(row, dict)] != expected_ids
        or any(
            not isinstance(row, dict)
            or set(row) != {"id", "classname", "duration_seconds_text", "outcome"}
            or row.get("outcome") not in {"passed", "failed"}
            for row in cases
        )
    ):
        failures.append("M2 JUnit case identity, order, fields, or outcome drift")
    else:
        failed = sum(row["outcome"] == "failed" for row in cases)
        expected_summary = {
            "official_cases": SHARD_CASE_COUNT,
            "official_outcomes": SHARD_CASE_COUNT,
            "official_passes": SHARD_CASE_COUNT - failed,
            "official_failures": failed,
        }
        if junit.get("summary") != expected_summary:
            failures.append("M2 JUnit summary drift")
    if junit.get("cases_sha256") != BASE.domain_digest(
        "axeyum-lean-u2-official-execution-m2-junit-cases-v1", cases
    ):
        failures.append("M2 JUnit case digest drift")
    raw = junit.get("raw", {})
    if (
        not isinstance(raw, dict)
        or set(raw) != {"path", "bytes", "sha256"}
        or raw.get("path") != "raw/junit.xml"
        or not isinstance(raw.get("bytes"), int)
        or raw["bytes"] < 0
        or not BASE.HEX64.fullmatch(str(raw.get("sha256", "")))
        or not BASE.HEX64.fullmatch(str(junit.get("terminal_sha256", "")))
    ):
        failures.append("M2 JUnit raw or terminal identity drift")
    return failures


def build_post_record(
    *,
    original_files: list[dict[str, Any]],
    generated_files: list[dict[str, Any]],
    junit: dict[str, Any],
) -> dict[str, Any]:
    manifest_failures = [
        *BASE._validate_manifest_rows(original_files, "M2 original source"),
        *BASE._validate_manifest_rows(generated_files, "M2 generated artifact"),
    ]
    if manifest_failures:
        raise M2ContractError("; ".join(manifest_failures))
    junit_failures = validate_junit_projection(junit)
    if junit_failures:
        raise M2ContractError("; ".join(junit_failures))
    original_paths = [row["path"] for row in original_files]
    paths = [row["path"] for row in generated_files]
    allowed = set(declared_generated_paths())
    if any(path not in allowed for path in paths):
        raise M2ContractError("undeclared generated artifact")
    if any(
        row["kind"] != "file" or row["target"] is not None
        for row in generated_files
    ):
        raise M2ContractError("generated artifact identity is malformed")
    present = set(paths)
    required_global = {
        "tests/with_stage1_test_env.sh",
        *BASE.CTEST_REQUIRED_SOURCE_PATHS,
    }
    if not required_global.issubset(present):
        raise M2ContractError("required wrapper or CTest artifacts are missing")
    outcomes = {row["id"]: row["outcome"] for row in junit["cases"]}
    for case in selected_contract()["cases"]:
        if outcomes.get(case["id"]) == "passed" and not set(
            case_generated_paths(case)
        ).issubset(present):
            raise M2ContractError(f"passed case lacks declared artifacts: {case['id']}")
    if junit["summary"]["official_failures"] == 0:
        if present != allowed - {BASE.CTEST_SOURCE_PATHS[2]}:
            raise M2ContractError("all-pass shard generated artifact closure drift")
    elif BASE.CTEST_SOURCE_PATHS[2] not in present:
        raise M2ContractError("failed shard lacks LastTestsFailed.log")
    return BASE.seal(
        {
            "schema": POST_SCHEMA,
            "original_files_sha256": BASE.domain_digest(
                "axeyum-lean-u2-source-files-v1", original_files
            ),
            "original_file_count": len(original_files),
            "original_files_unchanged": True,
            "generated_files": generated_files,
            "generated_files_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-generated-files-v1",
                generated_files,
            ),
            "allowed_paths_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-allowed-paths-v1",
                sorted(allowed),
            ),
            "undeclared_paths": [],
            "junit_sha256": junit["record_sha256"],
            "record_sha256": "",
        },
        POST_SCHEMA,
    )


def result_projection(junit: dict[str, Any], post: dict[str, Any]) -> dict[str, Any]:
    junit_failures = validate_junit_projection(junit)
    if junit_failures:
        raise M2ContractError("; ".join(junit_failures))
    if (
        not BASE.valid_seal(post, POST_SCHEMA)
        or post.get("junit_sha256") != junit["record_sha256"]
        or post.get("original_files_unchanged") is not True
        or post.get("undeclared_paths") != []
    ):
        raise M2ContractError("M2 post-run projection identity or linkage drift")
    summary = junit["summary"]
    credits = {
        "official_cases": SHARD_CASE_COUNT,
        "official_outcomes": SHARD_CASE_COUNT,
        "official_passes": summary["official_passes"],
        "official_failures": summary["official_failures"],
        "unique_new_official_cases": SHARD_CASE_COUNT,
        "local_physical_shards_completed": 1,
        **ZERO_TERMINAL_CREDITS,
    }
    return BASE.seal(
        {
            "schema": PROJECTION_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "shard_id": SHARD_ID,
            "shard_complete": True,
            "parent_selection_id": PARENT_SELECTION_ID,
            "parent_selected_count": PARENT_SELECTED_COUNT,
            "parent_completed": False,
            "official_provider_reproduced": False,
            "junit_sha256": junit["record_sha256"],
            "post_sha256": post["record_sha256"],
            "credits": credits,
            "claims": {
                "local_official_shard_observed": True,
                "parent_profile_complete": False,
                "official_provider_reproduced": False,
                "axeyum_observed": False,
                "matched_pair_formed": False,
                "performance_measured": False,
                "lean_parity_established": False,
            },
            "record_sha256": "",
        },
        PROJECTION_SCHEMA,
    )


def synthetic_discovery(
    *, source_root: Path, toolchain_root: Path, harness_root: Path
) -> dict[str, Any]:
    """Build a non-executed CTest JSON shape for offline contract tests."""

    return {
        "tests": [
            {
                "name": row["id"],
                "command": row["command"],
                "properties": row["properties"],
            }
            for row in expected_registrations(
                source_root=source_root,
                toolchain_root=toolchain_root,
                harness_root=harness_root,
            )
        ]
    }


def validate_offline_contract() -> dict[str, Any]:
    contract = selected_contract()
    source = Path("/m2/source")
    toolchain = Path("/m2/toolchain")
    harness = Path("/m2/harness")
    spec = build_spec(
        implementation_revision="0" * 40,
        source_root=source,
        toolchain_root=toolchain,
        harness_build=harness,
        junit_path=Path("/m2/attempt/test-results.xml"),
    )
    failures = validate_spec(spec)
    if failures:
        raise M2ContractError("; ".join(failures))
    discovery = synthetic_discovery(
        source_root=source, toolchain_root=toolchain, harness_root=harness
    )
    harness_record = build_harness_record(
        source_root=source,
        toolchain_root=toolchain,
        harness_root=harness,
        discovery_payload=discovery,
    )
    return {
        "case_count": len(contract["cases"]),
        "first_case_id": contract["cases"][0]["id"],
        "last_case_id": contract["cases"][-1]["id"],
        "spec_sha256": spec["record_sha256"],
        "harness_sha256": harness_record["record_sha256"],
        "ctest_bytes": len(
            render_ctest_file(
                source_root=source, toolchain_root=toolchain, harness_root=harness
            )
        ),
        "live_execution_surface": False,
        "official_outcomes": 0,
        "parity_credit": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate frozen inputs")
    args = parser.parse_args()
    if not args.check:
        parser.error("only the offline --check operation is implemented")
    try:
        summary = validate_offline_contract()
    except (M2ContractError, BASE.U2ExecutionError) as error:
        print(f"LEAN_U2_M2_CONTRACT_ERROR|{error}", file=sys.stderr)
        return 1
    print(
        "LEAN_U2_M2_CONTRACT|"
        f"cases={summary['case_count']}|"
        f"first={summary['first_case_id']}|last={summary['last_case_id']}|"
        "live_execution=false|outcomes=0|pairs=0|parity=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
