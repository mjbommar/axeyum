#!/usr/bin/env python3
"""TL0.7.4 no-credit acceptance controls for pinned Lean and lean4export.

This module deliberately owns a schema separate from TL0.7.2 and TL0.7.3.
It imports their accepted process and storage mechanisms without changing
their fixture-specific authorities.  The two controls have empty U2
selections and can never create Lean-parity credit.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SMTCOMP = ROOT / "scripts/smtcomp_repro"
if str(SMTCOMP) not in sys.path:
    sys.path.insert(0, str(SMTCOMP))

from scripts import lean_execution_process as PROCESS  # noqa: E402
from scripts import lean_execution_store as STORE  # noqa: E402
from resume_fs import (  # noqa: E402
    CheckpointConflict,
    atomic_install_bytes,
    atomic_install_json,
)


PREREGISTRATION_PLAN = (
    ROOT / "docs/plan/lean-execution-acceptance-tl0.7.4-plan-2026-07-22.md"
)
PREREGISTRATION_COMMIT = "48a365954ad3dfc23985ef3504d8a9392d05f6c8"
R1_PREREGISTRATION_PLAN = (
    ROOT / "docs/plan/lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md"
)
R1_PREREGISTRATION_COMMIT = "fde64fb39ded789f3a392a818d86d2dc7d299406"
FAILED_ATTEMPT_RESULT = (
    ROOT / "docs/plan/lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md"
)
FAILED_EVIDENCE_ROOT = (
    ROOT / "docs/plan/evidence/lean-execution-acceptance-tl0.7.4-attempt-001-failed"
)
FAILED_IMPLEMENTATION_REVISION = "4ba69b7076996057390e54daf8624e1b1cec9fb7"
FAILED_EVIDENCE_FILES = 41
FAILED_EVIDENCE_BYTES = 89_974
FAILED_EVIDENCE_MANIFEST_SHA256 = "c4f9fa088cd0f2fdb8a1cbebc111053252326ce5ea106f3e5ffa6b22ba292ae7"
RESULT_AUTHORITY = ROOT / "docs/plan/lean-execution-acceptance-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-execution-acceptance.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-execution-acceptance.md"
DEFAULT_EVIDENCE_ROOT = (
    ROOT / "docs/plan/evidence/lean-execution-acceptance-tl0.7.4"
)
FLAT_SOURCE = ROOT / "docs/plan/fixtures/lean4export-v4.30-axeyum-probe.lean"
REFERENCE_STREAM = (
    ROOT / "docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson"
)

BUILD_SCHEMA = "axeyum-lean-execution-acceptance-build-v1"
MANIFEST_SCHEMA = "axeyum-lean-execution-acceptance-manifest-v1"
SPEC_SCHEMA = "axeyum-lean-execution-acceptance-spec-v1"
RUN_SCHEMA = "axeyum-lean-execution-acceptance-run-v1"
PRELAUNCH_SCHEMA = "axeyum-lean-execution-acceptance-prelaunch-v1"
TERMINAL_SCHEMA = "axeyum-lean-execution-acceptance-terminal-v1"
ARTIFACT_SCHEMA = "axeyum-lean-execution-acceptance-artifacts-v1"
COMPLETION_SCHEMA = "axeyum-lean-execution-acceptance-completion-v1"
RESULT_SCHEMA = "axeyum-lean-execution-acceptance-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-execution-acceptance-summary-v1"

CONTROL_IDS = (
    "pinned-lean-compile-preflight-4g-tstack512m",
    "official-lean4export-flat-export-8g",
)
COMPILE_CONTROL = CONTROL_IDS[0]
EXPORT_CONTROL = CONTROL_IDS[1]
FAILED_COMPILE_CONTROL = "pinned-lean-compile-preflight-4g"
EMPTY_SELECTION_ID = "tl0.7.4-empty-selection-v1"
CREDIT_CLASS = "real-external-control-no-credit"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
SAFE_ID = re.compile(r"[a-z0-9][a-z0-9.-]{0,127}\Z")

LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
LEAN_VERSION_LINE = (
    "Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit "
    f"{LEAN_COMMIT}, Release)"
)
LAKE_VERSION_LINE = "Lake version 5.0.0-src+d024af0 (Lean version 4.30.0)"
PINNED_LEAN_SHA256 = "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
PINNED_LAKE_SHA256 = "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b"
FLAT_SOURCE_SHA256 = "342337c885dd88d3ddc7c7b49aec52b57867206ebc3ae50f81f55e85e236dfb5"
REFERENCE_SHA256 = "c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280"
REFERENCE_BYTES = 3_849
REFERENCE_LINES = 65
TASK_STACK_KIB = 524_288
TASK_STACK_BYTES = 536_870_912

EXPORTER_REPOSITORY = "https://github.com/leanprover/lean4export"
EXPORTER_TAG = "v4.30.0"
EXPORTER_COMMIT = "a3e35a584f59b390667db7269cd37fca8575e4bf"
EXPORTER_TREE = "e8b4adcea8445abbe0ae656eb6067d079e3efca8"
EXPORTER_ARCHIVE_SHA256 = "a66fd0b6f04701565221cb82c9702ab4036ab624471f91af27cf306ee4e35098"
EXPORTER_SOURCE_HASHES = {
    "README.md": "98833b66efc1289df582d85faa79b253c83bcca27c9fdb073ba42bdf0ffe77c9",
    "format_ndjson.md": "f82a21e17e4258a1043895d0653ea4333bef8cb07aad2e3d6c1fc4be52b138e3",
    "lakefile.toml": "54dde3aba280f32035c882dcd2f2039e738e20ed45ca538337b65cc69c02f7df",
    "lean-toolchain": "54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325",
}
EXPORTER_TREE_ROWS = (
    ("100644", "blob", "6edae1f5abe49c9aac3aa203065c5b43383448d1", ".github/workflows/ci.yml"),
    ("100644", "blob", "01f8cdb637da2370fa79960e25efa59dd8cffd6d", ".gitignore"),
    ("100644", "blob", "2054d4735272bb4d8d80e100048e86dcd0388201", "Export.lean"),
    ("100644", "blob", "1eedbabc47e0db3df6405063913380ed0fed46ac", "Export/Parse.lean"),
    ("100644", "blob", "261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64", "LICENSE"),
    ("100644", "blob", "806fcf7b107c111d454db9ac29c09e73bf2e25aa", "Main.lean"),
    ("100644", "blob", "e69210983a283e83bca65132a5af17d9fce81bfa", "README.md"),
    ("100644", "blob", "5fe32cf052b2ee24db80327f20e355cf299c95f9", "Test.lean"),
    ("100644", "blob", "d3cd35f1313b4e78b5fded9886e450112aa75def", "examples/Nat.add_succ.ndjson"),
    ("100644", "blob", "6eee6b0f1dcaa4570590dcf878a1fb3ba381f07c", "format_ndjson.md"),
    ("100644", "blob", "5b9d18c8640739bb8f3a08599d6215f15069f04e", "lake-manifest.json"),
    ("100644", "blob", "2ec701102b5963981003d4b89948de18b713e69b", "lakefile.toml"),
    ("100644", "blob", "af9e5d339aeb37e4e6ba2603fb873e637678e304", "lean-toolchain"),
)

FROZEN_REPOSITORY_INPUTS = {
    "docs/plan/lean-execution-evidence-v1.json": "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a",
    "docs/plan/lean-execution-process-v1.json": "0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf",
    "scripts/lean_execution_process.py": "96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007",
    "docs/plan/lean-execution-store-v1.json": "e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647",
    "scripts/lean_execution_store.py": "06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679",
    "scripts/smtcomp_repro/resume_fs.py": "1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec",
    "lean-toolchain": "54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325",
    "scripts/install-pinned-lean.sh": "75acb49a48e18b43523257ac22bc82889d614a6678c1cc3a457b3a150e1c7f71",
    "docs/plan/fixtures/lean4export-v4.30-axeyum-probe.lean": FLAT_SOURCE_SHA256,
    "docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson": REFERENCE_SHA256,
    "docs/plan/lean-u2-official-ci-profiles-v1.json": "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548",
    "docs/plan/lean-execution-acceptance-tl0.7.4-r1-plan-2026-07-22.md": "241b9f4c2d68804f7fcfb91ef26c409cea377e75ed8cc58b526ecd031658bcda",
    "docs/plan/lean-execution-acceptance-tl0.7.4-attempt-001-2026-07-22.md": "27b948b21bc9b2b14e185d2534e2bb96c13648750871c7f4e682b2eece479ec1",
}

LANES = {
    COMPILE_CONTROL: {
        "lane_id": "standard-local-4g",
        "memory_limit_bytes": 4_294_967_296,
        "wall_timeout_ms": 60_000,
    },
    EXPORT_CONTROL: {
        "lane_id": "official-export-8g",
        "memory_limit_bytes": 8_589_934_592,
        "wall_timeout_ms": 120_000,
    },
}

ZERO_CREDITS = {
    "credited_runs": 0,
    "official_u2_cases": 0,
    "official_outcomes": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}

CONTROL_PATHS = {
    COMPILE_CONTROL: (
        "artifact.json",
        "artifacts/AxeyumProbe.lean",
        "artifacts/AxeyumProbe.olean",
        "attempt-prelaunch.json",
        "attempt-terminal.json",
        "completion.json",
        "manifest.json",
        "raw/stderr.bin",
        "raw/stdout.bin",
        "run.json",
        "spec.json",
    ),
    EXPORT_CONTROL: (
        "artifact.json",
        "artifacts/export.ndjson",
        "attempt-prelaunch.json",
        "attempt-terminal.json",
        "completion.json",
        "manifest.json",
        "raw/stderr.bin",
        "raw/stdout.bin",
        "run.json",
        "spec.json",
    ),
}

MANIFEST_FIELDS = {
    "schema", "control_id", "credit_class", "spec_sha256", "storage_class",
    "expected_paths", "completion_installed_last", "selection_case_ids", "credits",
    "record_sha256",
}
RUN_FIELDS = {
    "schema", "control_id", "run_id", "spec_sha256", "command", "command_sha256",
    "working_directory", "environment", "environment_sha256", "resource_envelope",
    "resource_envelope_sha256", "inputs", "inputs_sha256", "selection_set_id",
    "selection_case_ids", "platform", "platform_sha256", "storage_class",
    "storage_class_sha256", "credit_class", "record_sha256",
}
PRELAUNCH_FIELDS = {
    "schema", "control_id", "run_id", "attempt_id", "sequence",
    "recorded_before_launch", "terminal", "selection_case_ids", "artifact_ids",
    "record_sha256",
}
TERMINAL_FIELDS = {
    "schema", "control_id", "run_id", "attempt_id", "sequence",
    "prelaunch_sha256", "class", "exit_code", "signal", "events", "wall_time",
    "cpu_time", "peak_rss", "process", "raw_outputs", "record_sha256",
}
ARTIFACT_FIELDS = {
    "schema", "control_id", "artifacts", "predicates", "record_sha256",
}
COMPLETION_FIELDS = {
    "schema", "control_id", "run_id", "attempt_id", "state",
    "completion_installed_last", "dependencies", "record_set_sha256", "projection",
    "projection_sha256", "selection_case_ids", "case_records", "credits",
    "record_sha256",
}
RESULT_FIELDS = {
    "schema", "status", "preregistration_commit", "implementation_revision",
    "r1_preregistration_commit", "source_inputs", "build", "failed_attempt",
    "controls", "summary", "evidence_files",
    "evidence_manifest_sha256", "claims", "credits", "record_sha256",
}


class AcceptanceEvidenceError(ValueError):
    """The TL0.7.4 source, process, store, or result contract failed closed."""


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def digest(value: Any) -> str:
    return sha256_bytes(canonical_bytes(value))


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def seal(value: dict[str, Any], schema: str, field: str = "record_sha256") -> dict[str, Any]:
    sealed = copy.deepcopy(value)
    sealed[field] = domain_digest(
        schema, {key: item for key, item in sealed.items() if key != field}
    )
    return sealed


def valid_seal(value: Any, schema: str, field: str = "record_sha256") -> bool:
    return (
        isinstance(value, dict)
        and value.get("schema") == schema
        and value.get(field)
        == domain_digest(schema, {key: item for key, item in value.items() if key != field})
    )


def metric(state: str, value: int | None, unit: str) -> dict[str, Any]:
    return {"state": state, "value": value, "unit": unit}


def load_canonical(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AcceptanceEvidenceError(f"malformed canonical JSON: {path}") from exc
    if raw != canonical_bytes(value):
        raise AcceptanceEvidenceError(f"noncanonical JSON: {path}")
    return value


def load_json_document(path: Path) -> Any:
    """Load a human-readable generated JSON document.

    Immutable evidence records use ``load_canonical``. Result authorities are
    deliberately rendered with indentation and are checked against their exact
    regenerated text instead.
    """

    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AcceptanceEvidenceError(f"malformed generated JSON: {path}") from exc


def _install_json(root: Path, relative: str, value: Any) -> str:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or len(path.parts) > 2:
        raise AcceptanceEvidenceError(f"unsafe evidence path: {relative}")
    return atomic_install_json(
        root / path.parent,
        path.name,
        value,
        quarantine_root=root / "quarantine",
    )


def _install_bytes(root: Path, relative: str, value: bytes) -> str:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts or len(path.parts) > 2:
        raise AcceptanceEvidenceError(f"unsafe evidence path: {relative}")
    return atomic_install_bytes(
        root / path.parent,
        path.name,
        value,
        quarantine_root=root / "quarantine",
    )


def validate_repository_inputs() -> list[str]:
    failures = []
    for relative, expected in FROZEN_REPOSITORY_INPUTS.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            failures.append(f"frozen repository input drift: {relative}")
    if sha256_file(PREREGISTRATION_PLAN) == "":  # pragma: no cover - documents intent.
        failures.append("preregistration plan is empty")
    return failures


def _run_text(command: list[str], *, cwd: Path) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env={"LANG": "C.UTF-8", "PATH": "/usr/bin:/bin"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    if completed.returncode != 0:
        raise AcceptanceEvidenceError(
            f"identity command failed: {command[0]}: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    return completed.stdout.decode("utf-8", errors="strict").strip()


def _git(source_root: Path, *args: str) -> str:
    return _run_text(["/usr/bin/git", "-C", str(source_root), *args], cwd=ROOT)


def _file_record(relative: str, path: Path) -> dict[str, Any]:
    return {
        "path": relative,
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
    }


def _accepted_readonly_mode(path: Path) -> bool:
    """Accept live 0444 or Git-checkout 0644 for already tracked evidence.

    Git stores only the executable bit, so a committed 0444 checkpoint is
    materialized as 0644 in a fresh checkout. Untracked/live evidence must
    still be 0444; this exception cannot make a temporary mutation fixture
    pass.
    """

    mode = stat.S_IMODE(path.stat().st_mode)
    if mode == 0o444:
        return True
    if mode != 0o644:
        return False
    try:
        relative = path.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return False
    completed = subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), "ls-files", "--error-unmatch", "--", relative],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
        timeout=5,
    )
    return completed.returncode == 0


def capture_build_record(
    *,
    source_root: Path,
    lean: Path,
    lake: Path,
    exporter: Path,
    failed_stdout: Path,
    failed_stderr: Path,
    success_stdout: Path,
    success_stderr: Path,
    evidence_root: Path,
) -> dict[str, Any]:
    """Validate a previously executed source build and retain its exact record."""

    source_root = source_root.resolve()
    lean = lean.resolve()
    lake = lake.resolve()
    exporter = exporter.resolve()
    if evidence_root.exists():
        raise AcceptanceEvidenceError(f"evidence root must be new: {evidence_root}")
    for path in (lean, lake, exporter, failed_stdout, failed_stderr, success_stdout, success_stderr):
        if not path.is_file():
            raise AcceptanceEvidenceError(f"missing build input: {path}")
    if sha256_file(lean) != PINNED_LEAN_SHA256 or sha256_file(lake) != PINNED_LAKE_SHA256:
        raise AcceptanceEvidenceError("pinned Lean/Lake executable identity drift")
    lean_version = _run_text([str(lean), "--version"], cwd=ROOT)
    lake_version = _run_text([str(lake), "--version"], cwd=ROOT)
    if lean_version != LEAN_VERSION_LINE or lake_version != LAKE_VERSION_LINE:
        raise AcceptanceEvidenceError("pinned Lean/Lake version identity drift")
    if _git(source_root, "rev-parse", "HEAD") != EXPORTER_COMMIT:
        raise AcceptanceEvidenceError("exporter source commit drift")
    if _git(source_root, "rev-parse", "HEAD^{tree}") != EXPORTER_TREE:
        raise AcceptanceEvidenceError("exporter source tree drift")
    if _git(source_root, "status", "--porcelain=v1", "--untracked-files=all"):
        raise AcceptanceEvidenceError("exporter source is dirty")
    archive = subprocess.run(
        ["/usr/bin/git", "-C", str(source_root), "archive", "--format=tar", "HEAD"],
        cwd=ROOT,
        env={"LANG": "C.UTF-8", "PATH": "/usr/bin:/bin"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=30,
    )
    if archive.returncode != 0 or sha256_bytes(archive.stdout) != EXPORTER_ARCHIVE_SHA256:
        raise AcceptanceEvidenceError("exporter source archive identity drift")
    tree_rows = []
    for line in _git(source_root, "ls-tree", "-r", "--full-tree", "HEAD").splitlines():
        match = re.fullmatch(r"(\d{6}) (\S+) ([0-9a-f]{40})\t(.+)", line)
        if match is None:
            raise AcceptanceEvidenceError("malformed exporter tree row")
        tree_rows.append(
            {"mode": match[1], "type": match[2], "object": match[3], "path": match[4]}
        )
    expected_rows = [
        {"mode": mode, "type": kind, "object": obj, "path": path}
        for mode, kind, obj, path in EXPORTER_TREE_ROWS
    ]
    if tree_rows != expected_rows:
        raise AcceptanceEvidenceError("exporter recursive tree population drift")
    named_hashes = {name: sha256_file(source_root / name) for name in EXPORTER_SOURCE_HASHES}
    if named_hashes != EXPORTER_SOURCE_HASHES:
        raise AcceptanceEvidenceError("exporter named source identity drift")
    if sha256_file(failed_stdout) != sha256_bytes(b""):
        raise AcceptanceEvidenceError("failed preparation stdout drift")
    failed_message = b"error: unknown short option '-j'\n"
    if failed_stderr.read_bytes() != failed_message:
        raise AcceptanceEvidenceError("failed preparation stderr drift")
    if success_stderr.stat().st_size != 0:
        raise AcceptanceEvidenceError("successful build stderr must be empty")
    if exporter.stat().st_size <= 0 or not os.access(exporter, os.X_OK):
        raise AcceptanceEvidenceError("built exporter is absent, empty, or non-executable")

    evidence_root.mkdir(parents=True, mode=0o755)
    retained = {
        "failed_stdout": "preparation/attempt-001.stdout.bin",
        "failed_stderr": "preparation/attempt-001.stderr.bin",
        "success_stdout": "preparation/attempt-002.stdout.bin",
        "success_stderr": "preparation/attempt-002.stderr.bin",
    }
    for key, source in (
        ("failed_stdout", failed_stdout),
        ("failed_stderr", failed_stderr),
        ("success_stdout", success_stdout),
        ("success_stderr", success_stderr),
    ):
        _install_bytes(evidence_root, retained[key], source.read_bytes())
    environment = {
        "LANG": "C.UTF-8",
        "LAKE_NO_CACHE": "1",
        "LEAN_NUM_THREADS": "1",
        "PATH": f"{lake.parent}:/usr/bin:/bin",
    }
    common = {
        "working_directory": str(source_root),
        "environment": environment,
    }
    record = seal(
        {
            "schema": BUILD_SCHEMA,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "repository": EXPORTER_REPOSITORY,
            "tag": EXPORTER_TAG,
            "source_commit": EXPORTER_COMMIT,
            "source_tree": EXPORTER_TREE,
            "source_archive_sha256": EXPORTER_ARCHIVE_SHA256,
            "source_files": tree_rows,
            "source_file_count": len(tree_rows),
            "named_source_sha256": named_hashes,
            "clean_before_build": True,
            "clean_after_build": True,
            "attempts": [
                {
                    "sequence": 1,
                    "command": [str(lake), "-j1", "build", "lean4export"],
                    **common,
                    "exit_code": 1,
                    "stdout": _file_record(retained["failed_stdout"], evidence_root / retained["failed_stdout"]),
                    "stderr": _file_record(retained["failed_stderr"], evidence_root / retained["failed_stderr"]),
                    "compiled_sources": False,
                    "classification": "cli-option-rejected-before-build",
                },
                {
                    "sequence": 2,
                    "command": [str(lake), "build", "lean4export"],
                    **common,
                    "exit_code": 0,
                    "stdout": _file_record(retained["success_stdout"], evidence_root / retained["success_stdout"]),
                    "stderr": _file_record(retained["success_stderr"], evidence_root / retained["success_stderr"]),
                    "compiled_sources": True,
                    "classification": "completed",
                },
            ],
            "toolchain": {
                "lean_path": str(lean),
                "lean_sha256": sha256_file(lean),
                "lean_version": lean_version,
                "lake_path": str(lake),
                "lake_sha256": sha256_file(lake),
                "lake_version": lake_version,
            },
            "executable": {
                "path": str(exporter),
                "bytes": exporter.stat().st_size,
                "mode": stat.S_IMODE(exporter.stat().st_mode),
                "sha256": sha256_file(exporter),
            },
            "record_sha256": "",
        },
        BUILD_SCHEMA,
    )
    failures = validate_build_record(record, evidence_root=evidence_root)
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    _install_json(evidence_root, "preparation/build.json", record)
    return record


def validate_build_record(record: Any, *, evidence_root: Path | None = None) -> list[str]:
    failures: list[str] = []
    fields = {
        "schema", "preregistration_commit", "repository", "tag", "source_commit",
        "source_tree", "source_archive_sha256", "source_files", "source_file_count",
        "named_source_sha256", "clean_before_build", "clean_after_build", "attempts",
        "toolchain", "executable", "record_sha256",
    }
    if not isinstance(record, dict) or set(record) != fields:
        return ["build record fields must be exact"]
    if not valid_seal(record, BUILD_SCHEMA):
        failures.append("build record identity drift")
    if (
        record.get("preregistration_commit") != PREREGISTRATION_COMMIT
        or record.get("repository") != EXPORTER_REPOSITORY
        or record.get("tag") != EXPORTER_TAG
        or record.get("source_commit") != EXPORTER_COMMIT
        or record.get("source_tree") != EXPORTER_TREE
        or record.get("source_archive_sha256") != EXPORTER_ARCHIVE_SHA256
    ):
        failures.append("build source pin drift")
    expected_rows = [
        {"mode": mode, "type": kind, "object": obj, "path": path}
        for mode, kind, obj, path in EXPORTER_TREE_ROWS
    ]
    if record.get("source_files") != expected_rows or record.get("source_file_count") != 13:
        failures.append("build recursive source population drift")
    if record.get("named_source_sha256") != EXPORTER_SOURCE_HASHES:
        failures.append("build named source identity drift")
    if record.get("clean_before_build") is not True or record.get("clean_after_build") is not True:
        failures.append("build source cleanliness was not observed")
    toolchain = record.get("toolchain")
    if not isinstance(toolchain, dict) or set(toolchain) != {
        "lean_path", "lean_sha256", "lean_version", "lake_path", "lake_sha256", "lake_version"
    }:
        failures.append("build toolchain fields must be exact")
        toolchain = {}
    if (
        toolchain.get("lean_sha256") != PINNED_LEAN_SHA256
        or toolchain.get("lean_version") != LEAN_VERSION_LINE
        or toolchain.get("lake_sha256") != PINNED_LAKE_SHA256
        or toolchain.get("lake_version") != LAKE_VERSION_LINE
        or not Path(str(toolchain.get("lean_path", ""))).is_absolute()
        or not Path(str(toolchain.get("lake_path", ""))).is_absolute()
    ):
        failures.append("build pinned toolchain drift")
    attempts = record.get("attempts")
    if not isinstance(attempts, list) or len(attempts) != 2:
        failures.append("build must retain exactly two preparation attempts")
        attempts = []
    else:
        lake_path = toolchain.get("lake_path")
        expected_commands = (
            [lake_path, "-j1", "build", "lean4export"],
            [lake_path, "build", "lean4export"],
        )
        for index, attempt in enumerate(attempts):
            if not isinstance(attempt, dict) or set(attempt) != {
                "sequence", "command", "working_directory", "environment", "exit_code",
                "stdout", "stderr", "compiled_sources", "classification",
            }:
                failures.append("build attempt fields must be exact")
                continue
            if attempt.get("sequence") != index + 1 or attempt.get("command") != expected_commands[index]:
                failures.append("build attempt order or command drift")
            environment = attempt.get("environment")
            if environment != {
                "LANG": "C.UTF-8", "LAKE_NO_CACHE": "1", "LEAN_NUM_THREADS": "1",
                "PATH": f"{Path(str(lake_path)).parent}:/usr/bin:/bin",
            }:
                failures.append("build attempt environment drift")
            expected_status = (1, 0)[index]
            expected_compiled = (False, True)[index]
            expected_class = ("cli-option-rejected-before-build", "completed")[index]
            if (
                attempt.get("exit_code") != expected_status
                or attempt.get("compiled_sources") is not expected_compiled
                or attempt.get("classification") != expected_class
            ):
                failures.append("build attempt terminal attribution drift")
            for stream in ("stdout", "stderr"):
                sidecar = attempt.get(stream)
                if not isinstance(sidecar, dict) or set(sidecar) != {"path", "bytes", "sha256"}:
                    failures.append("build log fields must be exact")
                    continue
                if evidence_root is not None:
                    path = evidence_root / str(sidecar.get("path"))
                    if (
                        not path.is_file() or path.is_symlink()
                        or not _accepted_readonly_mode(path)
                        or path.stat().st_size != sidecar.get("bytes")
                        or sha256_file(path) != sidecar.get("sha256")
                    ):
                        failures.append("build retained log identity drift")
    executable = record.get("executable")
    if not isinstance(executable, dict) or set(executable) != {"path", "bytes", "mode", "sha256"}:
        failures.append("built executable fields must be exact")
    elif (
        not Path(str(executable.get("path"))).is_absolute()
        or not isinstance(executable.get("bytes"), int)
        or executable["bytes"] <= 0
        or not isinstance(executable.get("mode"), int)
        or executable["mode"] & 0o111 == 0
        or not isinstance(executable.get("sha256"), str)
        or not HEX64.fullmatch(executable["sha256"])
    ):
        failures.append("built executable identity is invalid")
    return failures


def resource_envelope(control_id: str) -> dict[str, Any]:
    lane = LANES[control_id]
    return {
        "lane_id": lane["lane_id"],
        "memory_limit": metric("observed", lane["memory_limit_bytes"], "bytes"),
        "memory_scope": "per-process-address-space",
        "memory_enforcement": "explicit-rlimit-as",
        "wall_timeout": metric("observed", lane["wall_timeout_ms"], "milliseconds"),
        "worker_limit": metric("observed", 1, "workers"),
        "thread_limit": metric("not-enforced", None, "threads"),
        "task_stack_limit": (
            metric("observed", TASK_STACK_BYTES, "bytes")
            if control_id == COMPILE_CONTROL
            else metric("not-observed", None, "bytes")
        ),
        "requested_parallelism": 1,
        "effective_parallelism": 1,
    }


def build_control_spec(
    control_id: str,
    *,
    implementation_revision: str,
    lean: Path,
    lake: Path,
    exporter: Path,
    exporter_source_root: Path,
    private_root: Path,
    compile_artifact_directory: Path | None,
    build_record: dict[str, Any],
    compile_completion: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if control_id not in CONTROL_IDS or not HEX40.fullmatch(implementation_revision):
        raise AcceptanceEvidenceError("invalid control or implementation revision")
    failures = validate_build_record(build_record)
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    lean = lean.resolve()
    lake = lake.resolve()
    exporter = exporter.resolve()
    exporter_source_root = exporter_source_root.resolve()
    private_root = private_root.resolve()
    if control_id == COMPILE_CONTROL:
        source = private_root / "AxeyumProbe.lean"
        output = private_root / "AxeyumProbe.olean"
        command = [
            str(lean), "-j1", f"-s{TASK_STACK_KIB}", "-o", str(output), str(source)
        ]
        working_directory = str(private_root)
        environment = {
            "LANG": "C.UTF-8",
            "LEAN_NUM_THREADS": "1",
            "PATH": f"{lean.parent}:/usr/bin:/bin",
        }
        inputs = {
            "lean_sha256": PINNED_LEAN_SHA256,
            "lean_version": LEAN_VERSION_LINE,
            "source_sha256": FLAT_SOURCE_SHA256,
            "build_record_sha256": build_record["record_sha256"],
            "lake_sha256": None,
            "exporter_sha256": None,
            "compile_completion_sha256": None,
            "compile_artifact_sha256": None,
            "reference_sha256": None,
        }
        expected = {
            "exit_code": 0,
            "stderr_bytes": None,
            "stdout_sha256": None,
            "artifact_kind": "lean-olean",
            "artifact_nonempty": True,
            "reference_bytes_equal": None,
        }
    else:
        if compile_artifact_directory is None or compile_completion is None:
            raise AcceptanceEvidenceError("export control requires completed compile evidence")
        artifact = compile_artifact_directory / "AxeyumProbe.olean"
        if not artifact.is_file() or artifact.is_symlink() or artifact.stat().st_size <= 0:
            raise AcceptanceEvidenceError("export control compile artifact is invalid")
        command = [str(lake), "env", str(exporter), "AxeyumProbe"]
        working_directory = str(exporter_source_root)
        environment = {
            "LANG": "C.UTF-8",
            "LAKE_NO_CACHE": "1",
            "LEAN_NUM_THREADS": "1",
            "LEAN_PATH": str(compile_artifact_directory.resolve()),
            "PATH": f"{lake.parent}:/usr/bin:/bin",
        }
        inputs = {
            "lean_sha256": PINNED_LEAN_SHA256,
            "lean_version": LEAN_VERSION_LINE,
            "source_sha256": None,
            "build_record_sha256": build_record["record_sha256"],
            "lake_sha256": PINNED_LAKE_SHA256,
            "exporter_sha256": build_record["executable"]["sha256"],
            "compile_completion_sha256": compile_completion["record_sha256"],
            "compile_artifact_sha256": sha256_file(artifact),
            "reference_sha256": REFERENCE_SHA256,
        }
        expected = {
            "exit_code": 0,
            "stderr_bytes": 0,
            "stdout_sha256": REFERENCE_SHA256,
            "artifact_kind": "lean4export-ndjson",
            "artifact_nonempty": True,
            "reference_bytes_equal": True,
        }
    spec = seal(
        {
            "schema": SPEC_SCHEMA,
            "control_id": control_id,
            "run_id": f"tl0.7.4-{control_id}",
            "attempt_id": f"attempt-{control_id}",
            "sequence": 1,
            "implementation_revision": implementation_revision,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "r1_preregistration_commit": R1_PREREGISTRATION_COMMIT,
            "lane_id": LANES[control_id]["lane_id"],
            "credit_class": CREDIT_CLASS,
            "command": command,
            "working_directory": working_directory,
            "environment": environment,
            "selection_set_id": EMPTY_SELECTION_ID,
            "selection_case_ids": [],
            "case_records": [],
            "resource_envelope": resource_envelope(control_id),
            "terminate_grace_ms": 1_000,
            "inputs": inputs,
            "expected": expected,
            "record_sha256": "",
        },
        SPEC_SCHEMA,
    )
    failures = validate_control_spec(spec)
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    return spec


def validate_control_spec(spec: Any) -> list[str]:
    failures: list[str] = []
    fields = {
        "schema", "control_id", "run_id", "attempt_id", "sequence",
        "implementation_revision", "preregistration_commit", "r1_preregistration_commit",
        "lane_id", "credit_class",
        "command", "working_directory", "environment", "selection_set_id",
        "selection_case_ids", "case_records", "resource_envelope", "terminate_grace_ms",
        "inputs", "expected", "record_sha256",
    }
    if not isinstance(spec, dict) or set(spec) != fields:
        return ["control spec fields must be exact"]
    if not valid_seal(spec, SPEC_SCHEMA):
        failures.append("control spec identity drift")
    control_id = spec.get("control_id")
    if control_id not in CONTROL_IDS:
        failures.append("unknown acceptance control")
        return failures
    if (
        spec.get("preregistration_commit") != PREREGISTRATION_COMMIT
        or spec.get("r1_preregistration_commit") != R1_PREREGISTRATION_COMMIT
        or not isinstance(spec.get("implementation_revision"), str)
        or not HEX40.fullmatch(spec["implementation_revision"])
        or spec.get("lane_id") != LANES[control_id]["lane_id"]
        or spec.get("credit_class") != CREDIT_CLASS
        or spec.get("sequence") != 1
    ):
        failures.append("control registration or lane drift")
    for field in ("run_id", "attempt_id"):
        if not isinstance(spec.get(field), str) or not SAFE_ID.fullmatch(spec[field]):
            failures.append(f"unsafe {field}")
    if (
        spec.get("selection_set_id") != EMPTY_SELECTION_ID
        or spec.get("selection_case_ids") != []
        or spec.get("case_records") != []
    ):
        failures.append("acceptance controls cannot select or record U2 cases")
    command = spec.get("command")
    if (
        not isinstance(command, list) or not command
        or not all(isinstance(item, str) and item for item in command)
        or not Path(command[0]).is_absolute()
    ):
        failures.append("control command must be an absolute argument array")
        command = []
    if spec.get("resource_envelope") != resource_envelope(control_id):
        failures.append("control resource envelope drift")
    if spec.get("terminate_grace_ms") != 1_000:
        failures.append("control termination grace drift")
    inputs = spec.get("inputs")
    expected = spec.get("expected")
    input_fields = {
        "lean_sha256", "lean_version", "source_sha256", "build_record_sha256",
        "lake_sha256", "exporter_sha256", "compile_completion_sha256",
        "compile_artifact_sha256", "reference_sha256",
    }
    expected_fields = {
        "exit_code", "stderr_bytes", "stdout_sha256", "artifact_kind",
        "artifact_nonempty", "reference_bytes_equal",
    }
    if not isinstance(inputs, dict) or set(inputs) != input_fields:
        failures.append("control input fields must be exact")
        inputs = {}
    if not isinstance(expected, dict) or set(expected) != expected_fields:
        failures.append("control expectation fields must be exact")
        expected = {}
    if inputs.get("lean_sha256") != PINNED_LEAN_SHA256 or inputs.get("lean_version") != LEAN_VERSION_LINE:
        failures.append("control Lean input drift")
    if not isinstance(inputs.get("build_record_sha256"), str) or not HEX64.fullmatch(inputs["build_record_sha256"]):
        failures.append("control build-record identity is invalid")
    environment = spec.get("environment")
    if control_id == COMPILE_CONTROL:
        if (
            len(command) != 6
            or command[1:4] != ["-j1", f"-s{TASK_STACK_KIB}", "-o"]
        ):
            failures.append("compile command shape drift")
        elif not all(Path(item).is_absolute() for item in (command[0], command[4], command[5])):
            failures.append("compile command uses implicit paths")
        expected_environment = {
            "LANG": "C.UTF-8", "LEAN_NUM_THREADS": "1",
            "PATH": f"{Path(command[0]).parent}:/usr/bin:/bin" if command else "",
        }
        if environment != expected_environment:
            failures.append("compile environment drift")
        if (
            inputs.get("source_sha256") != FLAT_SOURCE_SHA256
            or any(inputs.get(field) is not None for field in (
                "lake_sha256", "exporter_sha256", "compile_completion_sha256",
                "compile_artifact_sha256", "reference_sha256"
            ))
            or expected != {
                "exit_code": 0, "stderr_bytes": None, "stdout_sha256": None,
                "artifact_kind": "lean-olean", "artifact_nonempty": True,
                "reference_bytes_equal": None,
            }
        ):
            failures.append("compile input or acceptance predicate drift")
    else:
        if len(command) != 4 or command[1] != "env" or command[3] != "AxeyumProbe":
            failures.append("export command shape drift")
        elif not Path(command[0]).is_absolute() or not Path(command[2]).is_absolute():
            failures.append("export command uses implicit paths")
        expected_environment = {
            "LANG": "C.UTF-8", "LAKE_NO_CACHE": "1", "LEAN_NUM_THREADS": "1",
            "LEAN_PATH": str(environment.get("LEAN_PATH", "")) if isinstance(environment, dict) else "",
            "PATH": f"{Path(command[0]).parent}:/usr/bin:/bin" if command else "",
        }
        if (
            environment != expected_environment
            or not Path(expected_environment["LEAN_PATH"]).is_absolute()
        ):
            failures.append("export environment drift")
        for field in ("build_record_sha256", "exporter_sha256", "compile_completion_sha256", "compile_artifact_sha256"):
            if not isinstance(inputs.get(field), str) or not HEX64.fullmatch(inputs[field]):
                failures.append(f"export {field} identity is invalid")
        if (
            inputs.get("source_sha256") is not None
            or inputs.get("lake_sha256") != PINNED_LAKE_SHA256
            or inputs.get("reference_sha256") != REFERENCE_SHA256
            or expected != {
                "exit_code": 0, "stderr_bytes": 0, "stdout_sha256": REFERENCE_SHA256,
                "artifact_kind": "lean4export-ndjson", "artifact_nonempty": True,
                "reference_bytes_equal": True,
            }
        ):
            failures.append("export input or acceptance predicate drift")
        forbidden = {"--export-unsafe", "--export-mdata", "--"}
        if forbidden.intersection(command):
            failures.append("export command enables forbidden options or filtering")
    return failures


def _manifest(control_id: str, spec: dict[str, Any], storage: dict[str, Any]) -> dict[str, Any]:
    return seal(
        {
            "schema": MANIFEST_SCHEMA,
            "control_id": control_id,
            "credit_class": CREDIT_CLASS,
            "spec_sha256": spec["record_sha256"],
            "storage_class": storage,
            "expected_paths": list(CONTROL_PATHS[control_id]),
            "completion_installed_last": True,
            "selection_case_ids": [],
            "credits": ZERO_CREDITS,
            "record_sha256": "",
        },
        MANIFEST_SCHEMA,
    )


def _run_record(spec: dict[str, Any], storage: dict[str, Any]) -> dict[str, Any]:
    platform = PROCESS.capture_platform(Path(spec["working_directory"]))
    return seal(
        {
            "schema": RUN_SCHEMA,
            "control_id": spec["control_id"],
            "run_id": spec["run_id"],
            "spec_sha256": spec["record_sha256"],
            "command": spec["command"],
            "command_sha256": digest(spec["command"]),
            "working_directory": spec["working_directory"],
            "environment": spec["environment"],
            "environment_sha256": digest(spec["environment"]),
            "resource_envelope": spec["resource_envelope"],
            "resource_envelope_sha256": digest(spec["resource_envelope"]),
            "inputs": spec["inputs"],
            "inputs_sha256": digest(spec["inputs"]),
            "selection_set_id": EMPTY_SELECTION_ID,
            "selection_case_ids": [],
            "platform": platform,
            "platform_sha256": digest(platform),
            "storage_class": storage,
            "storage_class_sha256": storage["identity_sha256"],
            "credit_class": CREDIT_CLASS,
            "record_sha256": "",
        },
        RUN_SCHEMA,
    )


def _prelaunch_record(spec: dict[str, Any]) -> dict[str, Any]:
    return seal(
        {
            "schema": PRELAUNCH_SCHEMA,
            "control_id": spec["control_id"],
            "run_id": spec["run_id"],
            "attempt_id": spec["attempt_id"],
            "sequence": 1,
            "recorded_before_launch": True,
            "terminal": None,
            "selection_case_ids": [],
            "artifact_ids": [],
            "record_sha256": "",
        },
        PRELAUNCH_SCHEMA,
    )


def _raw_descriptor(path: str, value: bytes) -> dict[str, Any]:
    return {"path": path, "bytes": len(value), "sha256": sha256_bytes(value)}


def _execute_external(spec: dict[str, Any], private_root: Path) -> tuple[dict[str, Any], bytes, bytes]:
    failures = validate_control_spec(spec)
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    stdout_path = private_root / "stdout.bin"
    stderr_path = private_root / "stderr.bin"
    memory_limit = LANES[spec["control_id"]]["memory_limit_bytes"]
    timeout_ms = LANES[spec["control_id"]]["wall_timeout_ms"]
    process: subprocess.Popen[bytes] | None = None
    peak_rss: int | None = None
    events = ["prelaunch-record-installed"]
    start_ns = time.monotonic_ns()
    with stdout_path.open("xb", buffering=0) as stdout_handle, stderr_path.open("xb", buffering=0) as stderr_handle:
        try:
            process = subprocess.Popen(
                spec["command"],
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                cwd=spec["working_directory"],
                env=spec["environment"],
                shell=False,
                close_fds=True,
                start_new_session=True,
                preexec_fn=PROCESS._limit_hook(memory_limit),
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise AcceptanceEvidenceError(f"external control launch failed: {exc}") from exc
        pid = process.pid
        pgid = process.pid
        events.append("rlimit-as-installed")
        deadline_ns = start_ns + timeout_ms * 1_000_000
        watchdog_fired = False
        sigterm_sent = False
        sigkill_sent = False
        while process.poll() is None and time.monotonic_ns() < deadline_ns:
            sample = PROCESS._sample_peak_rss(pid)
            if sample is not None:
                peak_rss = max(peak_rss or 0, sample)
            time.sleep(0.01)
        if process.poll() is None:
            watchdog_fired = True
            events.append("wall-timeout-observed")
            try:
                os.killpg(pgid, signal.SIGTERM)
                sigterm_sent = True
                events.append("process-group-sigterm-sent")
            except ProcessLookupError:
                pass
            grace = time.monotonic_ns() + spec["terminate_grace_ms"] * 1_000_000
            while time.monotonic_ns() < grace and PROCESS._live_process_group_members(pgid):
                time.sleep(0.01)
            if PROCESS._live_process_group_members(pgid):
                try:
                    os.killpg(pgid, signal.SIGKILL)
                    sigkill_sent = True
                    events.append("process-group-sigkill-sent")
                except ProcessLookupError:
                    pass
        try:
            process.wait(timeout=3)
            direct_child_reaped = True
            events.append("direct-child-reaped")
        except subprocess.TimeoutExpired:
            try:
                os.killpg(pgid, signal.SIGKILL)
                sigkill_sent = True
            except ProcessLookupError:
                pass
            process.wait(timeout=3)
            direct_child_reaped = True
            events.append("direct-child-reaped")
        live = PROCESS._live_process_group_members(pgid)
        cleanup_deadline = time.monotonic_ns() + 1_000_000_000
        while live and time.monotonic_ns() < cleanup_deadline:
            time.sleep(0.01)
            live = PROCESS._live_process_group_members(pgid)
        if not live:
            events.append("process-group-no-live-members-observed")
        stdout_handle.flush()
        stderr_handle.flush()
        os.fsync(stdout_handle.fileno())
        os.fsync(stderr_handle.fileno())
    elapsed_ms = max(1, (time.monotonic_ns() - start_ns) // 1_000_000)
    stdout = stdout_path.read_bytes()
    stderr = stderr_path.read_bytes()
    return_code = process.returncode if process is not None else None
    terminal_class = "wall-timeout" if watchdog_fired else ("signaled" if return_code is not None and return_code < 0 else "exited")
    terminal = seal(
        {
            "schema": TERMINAL_SCHEMA,
            "control_id": spec["control_id"],
            "run_id": spec["run_id"],
            "attempt_id": spec["attempt_id"],
            "sequence": 1,
            "prelaunch_sha256": "",
            "class": terminal_class,
            "exit_code": return_code if return_code is not None and return_code >= 0 else None,
            "signal": -return_code if return_code is not None and return_code < 0 else None,
            "events": events,
            "wall_time": metric("observed", elapsed_ms, "milliseconds"),
            "cpu_time": metric("not-observed", None, "milliseconds"),
            "peak_rss": metric("observed", peak_rss, "bytes") if peak_rss else metric("not-observed", None, "bytes"),
            "process": {
                "pid": process.pid if process is not None else None,
                "process_group_id": process.pid if process is not None else None,
                "rlimit_as_bytes": memory_limit if process is not None else None,
                "watchdog_fired": watchdog_fired,
                "sigterm_sent": sigterm_sent,
                "sigkill_sent": sigkill_sent,
                "direct_child_reaped": direct_child_reaped,
                "live_non_zombie_pids_after_cleanup": live,
            },
            "raw_outputs": [
                _raw_descriptor("raw/stderr.bin", stderr),
                _raw_descriptor("raw/stdout.bin", stdout),
            ],
            "record_sha256": "",
        },
        TERMINAL_SCHEMA,
    )
    return terminal, stdout, stderr


def _artifact_record(control_id: str, artifacts: list[dict[str, Any]], predicates: dict[str, Any]) -> dict[str, Any]:
    return seal(
        {
            "schema": ARTIFACT_SCHEMA,
            "control_id": control_id,
            "artifacts": artifacts,
            "predicates": predicates,
            "record_sha256": "",
        },
        ARTIFACT_SCHEMA,
    )


def _projection(
    spec: dict[str, Any], terminal: dict[str, Any], artifact: dict[str, Any]
) -> dict[str, Any]:
    if spec["control_id"] == COMPILE_CONTROL:
        command_shape = [
            f"lean@{spec['inputs']['lean_sha256']}", "-j1",
            f"-s{TASK_STACK_KIB}", "-o",
            "private-output:AxeyumProbe.olean", "private-source:AxeyumProbe.lean",
        ]
        environment_shape = {
            "LANG": "C.UTF-8", "LEAN_NUM_THREADS": "1",
            "PATH": "pinned-lean-bin:/usr/bin:/bin",
        }
    else:
        command_shape = [
            f"lake@{spec['inputs']['lake_sha256']}", "env",
            f"lean4export@{spec['inputs']['exporter_sha256']}", "AxeyumProbe",
        ]
        environment_shape = {
            "LANG": "C.UTF-8", "LAKE_NO_CACHE": "1", "LEAN_NUM_THREADS": "1",
            "LEAN_PATH": f"compile-artifact@{spec['inputs']['compile_artifact_sha256']}",
            "PATH": "pinned-lean-bin:/usr/bin:/bin",
        }
    return {
        "schema": "axeyum-lean-execution-acceptance-projection-v1",
        "control_id": spec["control_id"],
        "implementation_revision": spec["implementation_revision"],
        "command_shape": command_shape,
        "environment_shape": environment_shape,
        "resource_envelope": spec["resource_envelope"],
        "inputs": spec["inputs"],
        "terminal": {
            "class": terminal["class"],
            "exit_code": terminal["exit_code"],
            "signal": terminal["signal"],
            "watchdog_fired": terminal["process"]["watchdog_fired"],
            "direct_child_reaped": terminal["process"]["direct_child_reaped"],
            "live_non_zombie_pids_after_cleanup": terminal["process"]["live_non_zombie_pids_after_cleanup"],
        },
        "raw_outputs": terminal["raw_outputs"],
        "artifacts": artifact["artifacts"],
        "predicates": artifact["predicates"],
        "selection_case_ids": [],
        "credits": ZERO_CREDITS,
    }


def _dependency_inventory(root: Path) -> list[dict[str, Any]]:
    rows = []
    for relative in CONTROL_PATHS[load_canonical(root / "spec.json")["control_id"]]:
        if relative == "completion.json":
            continue
        path = root / relative
        rows.append(_file_record(relative, path))
    return rows


def _completion_record(
    root: Path, spec: dict[str, Any], terminal: dict[str, Any], artifact: dict[str, Any]
) -> dict[str, Any]:
    dependencies = _dependency_inventory(root)
    projection = _projection(spec, terminal, artifact)
    return seal(
        {
            "schema": COMPLETION_SCHEMA,
            "control_id": spec["control_id"],
            "run_id": spec["run_id"],
            "attempt_id": spec["attempt_id"],
            "state": "complete",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": domain_digest(
                "axeyum-lean-execution-acceptance-record-set-v1", dependencies
            ),
            "projection": projection,
            "projection_sha256": digest(projection),
            "selection_case_ids": [],
            "case_records": [],
            "credits": ZERO_CREDITS,
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def _prepare_control_root(root: Path, spec: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if root.exists() or root.is_symlink():
        raise AcceptanceEvidenceError(f"control store must be new: {root}")
    root.mkdir(parents=True, mode=0o755)
    storage = STORE.capture_storage_class(STORE.STORAGE_CLASS_IDS[0], ROOT)
    STORE.preflight_storage_class(storage)
    manifest = _manifest(spec["control_id"], spec, storage)
    run = _run_record(spec, storage)
    prelaunch = _prelaunch_record(spec)
    _install_json(root, "manifest.json", manifest)
    _install_json(root, "spec.json", spec)
    _install_json(root, "run.json", run)
    _install_json(root, "attempt-prelaunch.json", prelaunch)
    return manifest, run, prelaunch


def execute_control(spec: dict[str, Any], *, control_root: Path, private_root: Path) -> dict[str, Any]:
    """Run one external control and install completion only after validation."""

    failures = validate_control_spec(spec)
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    private_root = private_root.resolve()
    if private_root.exists():
        raise AcceptanceEvidenceError(f"private control directory must be new: {private_root}")
    private_root.mkdir(parents=True, mode=0o700)
    _, _, prelaunch = _prepare_control_root(control_root, spec)
    if spec["control_id"] == COMPILE_CONTROL:
        source = private_root / "AxeyumProbe.lean"
        shutil.copyfile(FLAT_SOURCE, source)
        if source.read_bytes() != FLAT_SOURCE.read_bytes():
            raise AcceptanceEvidenceError("private Lean source copy drift")
        _install_bytes(control_root, "artifacts/AxeyumProbe.lean", source.read_bytes())
    terminal, stdout, stderr = _execute_external(spec, private_root)
    terminal["prelaunch_sha256"] = prelaunch["record_sha256"]
    terminal = seal(terminal, TERMINAL_SCHEMA)
    _install_bytes(control_root, "raw/stdout.bin", stdout)
    _install_bytes(control_root, "raw/stderr.bin", stderr)
    # Failure evidence must close before any success-artifact predicate can
    # raise. Attempt 001 exposed the inverse ordering as a retention defect.
    _install_json(control_root, "attempt-terminal.json", terminal)
    if spec["control_id"] == COMPILE_CONTROL:
        output = private_root / "AxeyumProbe.olean"
        if not output.is_file() or output.is_symlink() or output.stat().st_size <= 0:
            raise AcceptanceEvidenceError("compile control produced no regular nonempty .olean")
        output_bytes = output.read_bytes()
        _install_bytes(control_root, "artifacts/AxeyumProbe.olean", output_bytes)
        artifacts = [
            _raw_descriptor("artifacts/AxeyumProbe.lean", FLAT_SOURCE.read_bytes()),
            _raw_descriptor("artifacts/AxeyumProbe.olean", output_bytes),
        ]
        predicates = {
            "source_copy_equal": True,
            "artifact_nonempty": True,
            "stderr_empty": len(stderr) == 0,
            "stdout_empty": len(stdout) == 0,
            "reference_bytes_equal": None,
            "metadata_equal": None,
        }
    else:
        _install_bytes(control_root, "artifacts/export.ndjson", stdout)
        artifacts = [_raw_descriptor("artifacts/export.ndjson", stdout)]
        metadata_equal = False
        try:
            first = json.loads(stdout.splitlines()[0])
            metadata_equal = first == {
                "meta": {
                    "exporter": {"name": "lean4export", "version": "3.1.0"},
                    "format": {"version": "3.1.0"},
                    "lean": {"githash": LEAN_COMMIT, "version": "4.30.0"},
                }
            }
        except (IndexError, UnicodeDecodeError, json.JSONDecodeError):
            pass
        predicates = {
            "source_copy_equal": None,
            "artifact_nonempty": len(stdout) > 0,
            "stderr_empty": len(stderr) == 0,
            "stdout_empty": False,
            "reference_bytes_equal": stdout == REFERENCE_STREAM.read_bytes(),
            "metadata_equal": metadata_equal,
        }
    artifact = _artifact_record(spec["control_id"], artifacts, predicates)
    _install_json(control_root, "artifact.json", artifact)
    if (
        terminal["class"] != "exited" or terminal["exit_code"] != 0
        or terminal["process"]["watchdog_fired"]
        or not terminal["process"]["direct_child_reaped"]
        or terminal["process"]["live_non_zombie_pids_after_cleanup"] != []
    ):
        raise AcceptanceEvidenceError("external control did not exit cleanly and reap its group")
    if spec["control_id"] == EXPORT_CONTROL and not all(
        predicates[field] is True
        for field in ("artifact_nonempty", "stderr_empty", "reference_bytes_equal", "metadata_equal")
    ):
        raise AcceptanceEvidenceError("exporter output acceptance predicate failed")
    completion = _completion_record(control_root, spec, terminal, artifact)
    _install_json(control_root, "completion.json", completion)
    failures = validate_control_store(control_root, expected_control=spec["control_id"])
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    return completion


def _validate_metric(value: Any, label: str, failures: list[str]) -> None:
    if not isinstance(value, dict) or set(value) != {"state", "value", "unit"}:
        failures.append(f"{label} metric fields must be exact")
    elif value.get("state") == "observed" and (
        not isinstance(value.get("value"), int) or isinstance(value.get("value"), bool)
        or value["value"] < 0
    ):
        failures.append(f"{label} observed value is invalid")
    elif value.get("state") == "not-observed" and value.get("value") is not None:
        failures.append(f"{label} unobserved value must be null")


def validate_control_store(root: Path, *, expected_control: str) -> list[str]:
    failures: list[str] = []
    if expected_control not in CONTROL_IDS:
        return ["unknown expected control"]
    if not root.is_dir() or root.is_symlink():
        return ["control store must be a real directory"]
    allowed = set(CONTROL_PATHS[expected_control])
    actual = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        if relative == "quarantine" or relative.startswith("quarantine/"):
            continue
        if path.is_symlink():
            failures.append(f"symlinked evidence path: {relative}")
        if path.is_file():
            actual.add(relative)
            if not _accepted_readonly_mode(path):
                failures.append(f"accepted evidence is not read-only: {relative}")
    if actual != allowed:
        failures.append("control store file set must be exact")
        return failures
    try:
        manifest = load_canonical(root / "manifest.json")
        spec = load_canonical(root / "spec.json")
        run = load_canonical(root / "run.json")
        prelaunch = load_canonical(root / "attempt-prelaunch.json")
        terminal = load_canonical(root / "attempt-terminal.json")
        artifact = load_canonical(root / "artifact.json")
        completion = load_canonical(root / "completion.json")
    except AcceptanceEvidenceError as exc:
        return failures + [str(exc)]
    failures.extend(validate_control_spec(spec))
    if spec.get("control_id") != expected_control:
        failures.append("control store/spec attribution drift")
    if (
        not isinstance(manifest, dict) or set(manifest) != MANIFEST_FIELDS
        or not valid_seal(manifest, MANIFEST_SCHEMA)
        or manifest.get("control_id") != expected_control
    ):
        failures.append("manifest identity or attribution drift")
    elif (
        manifest.get("expected_paths") != list(CONTROL_PATHS[expected_control])
        or manifest.get("spec_sha256") != spec.get("record_sha256")
        or manifest.get("completion_installed_last") is not True
        or manifest.get("selection_case_ids") != []
        or manifest.get("credits") != ZERO_CREDITS
    ):
        failures.append("manifest closure or credit drift")
    storage = manifest.get("storage_class") if isinstance(manifest, dict) else None
    if STORE.validate_storage_descriptor(storage):
        failures.append("manifest storage descriptor drift")
    if (
        not isinstance(run, dict) or set(run) != RUN_FIELDS
        or not valid_seal(run, RUN_SCHEMA)
        or run.get("spec_sha256") != spec.get("record_sha256")
    ):
        failures.append("run identity or spec attribution drift")
    elif (
        run.get("control_id") != expected_control
        or run.get("run_id") != spec.get("run_id")
        or run.get("command") != spec.get("command")
        or run.get("command_sha256") != digest(spec.get("command"))
        or run.get("environment") != spec.get("environment")
        or run.get("environment_sha256") != digest(spec.get("environment"))
        or run.get("resource_envelope") != spec.get("resource_envelope")
        or run.get("resource_envelope_sha256") != digest(spec.get("resource_envelope"))
        or run.get("inputs") != spec.get("inputs")
        or run.get("inputs_sha256") != digest(spec.get("inputs"))
        or run.get("selection_case_ids") != []
        or run.get("credit_class") != CREDIT_CLASS
    ):
        failures.append("run exact identity drift")
    if (
        not isinstance(prelaunch, dict) or set(prelaunch) != PRELAUNCH_FIELDS
        or not valid_seal(prelaunch, PRELAUNCH_SCHEMA)
    ):
        failures.append("prelaunch identity drift")
    elif (
        prelaunch.get("control_id") != expected_control
        or prelaunch.get("run_id") != spec.get("run_id")
        or prelaunch.get("attempt_id") != spec.get("attempt_id")
        or prelaunch.get("sequence") != 1
        or prelaunch.get("recorded_before_launch") is not True
        or prelaunch.get("terminal") is not None
        or prelaunch.get("selection_case_ids") != []
    ):
        failures.append("prelaunch ordering or attribution drift")
    if (
        not isinstance(terminal, dict) or set(terminal) != TERMINAL_FIELDS
        or not valid_seal(terminal, TERMINAL_SCHEMA)
    ):
        failures.append("terminal identity drift")
    elif (
        terminal.get("control_id") != expected_control
        or terminal.get("run_id") != spec.get("run_id")
        or terminal.get("attempt_id") != spec.get("attempt_id")
        or terminal.get("prelaunch_sha256") != prelaunch.get("record_sha256")
        or terminal.get("class") != "exited"
        or terminal.get("exit_code") != 0
        or terminal.get("signal") is not None
    ):
        failures.append("terminal outcome or attribution drift")
    else:
        _validate_metric(terminal.get("wall_time"), "wall time", failures)
        _validate_metric(terminal.get("cpu_time"), "CPU time", failures)
        _validate_metric(terminal.get("peak_rss"), "peak RSS", failures)
        process = terminal.get("process")
        if not isinstance(process, dict) or set(process) != {
            "pid", "process_group_id", "rlimit_as_bytes", "watchdog_fired",
            "sigterm_sent", "sigkill_sent", "direct_child_reaped",
            "live_non_zombie_pids_after_cleanup",
        }:
            failures.append("terminal process fields must be exact")
        elif (
            process.get("rlimit_as_bytes") != LANES[expected_control]["memory_limit_bytes"]
            or process.get("watchdog_fired") is not False
            or process.get("sigterm_sent") is not False
            or process.get("sigkill_sent") is not False
            or process.get("direct_child_reaped") is not True
            or process.get("live_non_zombie_pids_after_cleanup") != []
        ):
            failures.append("terminal resource or process-group evidence drift")
        raw = terminal.get("raw_outputs")
        expected_raw = [
            _file_record("raw/stderr.bin", root / "raw/stderr.bin"),
            _file_record("raw/stdout.bin", root / "raw/stdout.bin"),
        ]
        if raw != expected_raw:
            failures.append("terminal raw output identity drift")
    if (
        not isinstance(artifact, dict) or set(artifact) != ARTIFACT_FIELDS
        or not valid_seal(artifact, ARTIFACT_SCHEMA)
        or artifact.get("control_id") != expected_control
    ):
        failures.append("artifact record identity drift")
    else:
        expected_artifacts = []
        artifact_paths = (
            ("artifacts/AxeyumProbe.lean", "artifacts/AxeyumProbe.olean")
            if expected_control == COMPILE_CONTROL else ("artifacts/export.ndjson",)
        )
        for relative in artifact_paths:
            expected_artifacts.append(_file_record(relative, root / relative))
        if artifact.get("artifacts") != expected_artifacts:
            failures.append("artifact payload identity drift")
        predicates = artifact.get("predicates")
        if expected_control == COMPILE_CONTROL:
            if (
                (root / "artifacts/AxeyumProbe.lean").read_bytes() != FLAT_SOURCE.read_bytes()
                or (root / "artifacts/AxeyumProbe.olean").stat().st_size <= 0
                or not isinstance(predicates, dict)
                or predicates.get("source_copy_equal") is not True
                or predicates.get("artifact_nonempty") is not True
            ):
                failures.append("compile artifact acceptance drift")
        else:
            stdout = (root / "raw/stdout.bin").read_bytes()
            reference = REFERENCE_STREAM.read_bytes()
            if (
                stdout != reference
                or (root / "raw/stderr.bin").stat().st_size != 0
                or (root / "artifacts/export.ndjson").read_bytes() != reference
                or reference.count(b"\n") != REFERENCE_LINES
                or len(reference) != REFERENCE_BYTES
                or not isinstance(predicates, dict)
                or any(predicates.get(field) is not True for field in (
                    "artifact_nonempty", "stderr_empty", "reference_bytes_equal", "metadata_equal"
                ))
            ):
                failures.append("export byte or metadata acceptance drift")
            else:
                try:
                    metadata = json.loads(reference.splitlines()[0])
                except (IndexError, json.JSONDecodeError):  # pragma: no cover - frozen fixture.
                    metadata = None
                if metadata != {
                    "meta": {
                        "exporter": {"name": "lean4export", "version": "3.1.0"},
                        "format": {"version": "3.1.0"},
                        "lean": {"githash": LEAN_COMMIT, "version": "4.30.0"},
                    }
                }:
                    failures.append("exporter metadata identity drift")
    if (
        not isinstance(completion, dict) or set(completion) != COMPLETION_FIELDS
        or not valid_seal(completion, COMPLETION_SCHEMA)
    ):
        failures.append("completion identity drift")
    else:
        dependencies = _dependency_inventory(root)
        projection = _projection(spec, terminal, artifact)
        if (
            completion.get("control_id") != expected_control
            or completion.get("state") != "complete"
            or completion.get("completion_installed_last") is not True
            or completion.get("dependencies") != dependencies
            or completion.get("record_set_sha256")
            != domain_digest("axeyum-lean-execution-acceptance-record-set-v1", dependencies)
            or completion.get("projection") != projection
            or completion.get("projection_sha256") != digest(projection)
            or completion.get("selection_case_ids") != []
            or completion.get("case_records") != []
            or completion.get("credits") != ZERO_CREDITS
        ):
            failures.append("completion dependency, projection, or credit drift")
    return failures


def _evidence_manifest(evidence_root: Path) -> list[dict[str, Any]]:
    rows = []
    for path in sorted(item for item in evidence_root.rglob("*") if item.is_file()):
        if "quarantine" in path.relative_to(evidence_root).parts:
            continue
        rows.append(_file_record(path.relative_to(evidence_root).as_posix(), path))
    return rows


def validate_failed_attempt_evidence() -> tuple[list[str], list[dict[str, Any]]]:
    failures: list[str] = []
    if not FAILED_EVIDENCE_ROOT.is_dir() or FAILED_EVIDENCE_ROOT.is_symlink():
        return ["missing real failed-attempt evidence root"], []
    rows = _evidence_manifest(FAILED_EVIDENCE_ROOT)
    if (
        len(rows) != FAILED_EVIDENCE_FILES
        or sum(item["bytes"] for item in rows) != FAILED_EVIDENCE_BYTES
        or domain_digest(
            "axeyum-lean-execution-acceptance-failed-evidence-v1", rows
        )
        != FAILED_EVIDENCE_MANIFEST_SHA256
    ):
        failures.append("failed-attempt evidence manifest drift")
    for item in rows:
        path = FAILED_EVIDENCE_ROOT / item["path"]
        if path.is_symlink() or not _accepted_readonly_mode(path):
            failures.append(f"invalid failed-attempt evidence mode: {item['path']}")
    control = FAILED_EVIDENCE_ROOT / "controls" / FAILED_COMPILE_CONTROL
    expected_partial = {
        "artifacts/AxeyumProbe.lean",
        "attempt-prelaunch.json",
        "manifest.json",
        "raw/stderr.bin",
        "raw/stdout.bin",
        "run.json",
        "spec.json",
    }
    actual_partial = {
        path.relative_to(control).as_posix()
        for path in control.rglob("*")
        if path.is_file()
    } if control.is_dir() else set()
    if actual_partial != expected_partial:
        failures.append("failed-attempt partial control file set drift")
    try:
        spec = load_canonical(control / "spec.json")
        build = load_canonical(FAILED_EVIDENCE_ROOT / "preparation/build.json")
    except AcceptanceEvidenceError as exc:
        failures.append(str(exc))
        return failures, rows
    failures.extend(
        f"failed attempt build: {failure}"
        for failure in validate_build_record(build, evidence_root=FAILED_EVIDENCE_ROOT)
    )
    if (
        spec.get("control_id") != FAILED_COMPILE_CONTROL
        or spec.get("implementation_revision") != FAILED_IMPLEMENTATION_REVISION
        or spec.get("command", [None, None])[1] != "-j1"
        or any(str(item).startswith("-s") for item in spec.get("command", []))
        or spec.get("resource_envelope", {}).get("memory_limit", {}).get("value")
        != 4_294_967_296
    ):
        failures.append("failed-attempt exact control attribution drift")
    stderr = control / "raw/stderr.bin"
    stdout = control / "raw/stdout.bin"
    if (
        not stderr.is_file()
        or stderr.stat().st_size != 98
        or sha256_file(stderr)
        != "32a60967270365f092cad81a408cf0e68f13aceab4359f32700f140a54129b9b"
        or not stdout.is_file()
        or stdout.stat().st_size != 0
    ):
        failures.append("failed-attempt raw diagnostic drift")
    trace = FAILED_EVIDENCE_ROOT / "diagnostics/strace/4g-thread-mmap.log"
    try:
        trace_text = trace.read_text(encoding="utf-8")
    except OSError:
        trace_text = ""
    if (
        "mmap(NULL, 1073745920" not in trace_text
        or "= -1 ENOMEM (Cannot allocate memory)" not in trace_text
    ):
        failures.append("failed-attempt thread-stack trace drift")
    expected_olean_hash = "1ce19df3f054ea6521fec7b8d49680d85087990c94e15bac00e731923152ecda"
    passing = [
        "diagnostics/rlimit-as-matrix/5g.olean",
        "diagnostics/rlimit-as-matrix/6g.olean",
        "diagnostics/rlimit-as-matrix/8g.olean",
        "diagnostics/tstack-option-matrix/64m.olean",
        "diagnostics/tstack-option-matrix/256m.olean",
        "diagnostics/tstack-option-matrix/512m.olean",
        "diagnostics/tstack-option-matrix/768m.olean",
    ]
    if any(
        not (FAILED_EVIDENCE_ROOT / relative).is_file()
        or (FAILED_EVIDENCE_ROOT / relative).stat().st_size != 9_672
        or sha256_file(FAILED_EVIDENCE_ROOT / relative) != expected_olean_hash
        for relative in passing
    ):
        failures.append("failed-attempt passing diagnostic artifact drift")
    return failures, rows


def validate_evidence_namespace(evidence_root: Path) -> list[str]:
    failures: list[str] = []
    if not evidence_root.is_dir() or evidence_root.is_symlink():
        return ["acceptance evidence root must be a real directory"]
    expected_preparation = {
        "build.json",
        "attempt-001.stdout.bin",
        "attempt-001.stderr.bin",
        "attempt-002.stdout.bin",
        "attempt-002.stderr.bin",
    }
    top = {path.name for path in evidence_root.iterdir() if path.name != "quarantine"}
    if top != {"preparation", "controls"}:
        failures.append("acceptance evidence top-level namespace drift")
        return failures
    preparation = evidence_root / "preparation"
    controls = evidence_root / "controls"
    if (
        not preparation.is_dir() or preparation.is_symlink()
        or not controls.is_dir() or controls.is_symlink()
    ):
        failures.append("acceptance evidence namespaces must be real directories")
        return failures
    if {path.name for path in preparation.iterdir()} != expected_preparation:
        failures.append("preparation evidence file set must be exact")
    if {path.name for path in controls.iterdir()} != set(CONTROL_IDS):
        failures.append("control evidence directory set must be exact")
    for path in preparation.iterdir():
        if (
            path.is_symlink() or not path.is_file()
            or not _accepted_readonly_mode(path)
        ):
            failures.append(f"invalid retained preparation file: {path.name}")
    return failures


def build_result_authority(
    evidence_root: Path, *, implementation_revision: str
) -> dict[str, Any]:
    if not HEX40.fullmatch(implementation_revision):
        raise AcceptanceEvidenceError("implementation revision must be a full Git hash")
    input_failures = validate_repository_inputs()
    if input_failures:
        raise AcceptanceEvidenceError("; ".join(input_failures))
    failed_failures, failed_evidence = validate_failed_attempt_evidence()
    if failed_failures:
        raise AcceptanceEvidenceError("; ".join(failed_failures))
    namespace_failures = validate_evidence_namespace(evidence_root)
    if namespace_failures:
        raise AcceptanceEvidenceError("; ".join(namespace_failures))
    build_path = evidence_root / "preparation/build.json"
    if not build_path.is_file():
        raise AcceptanceEvidenceError("missing retained exporter build record")
    build = load_canonical(build_path)
    failures = validate_build_record(build, evidence_root=evidence_root)
    completions = []
    for control_id in CONTROL_IDS:
        root = evidence_root / "controls" / control_id
        control_failures = validate_control_store(root, expected_control=control_id)
        failures.extend(f"{control_id}: {failure}" for failure in control_failures)
        if not control_failures:
            completion = load_canonical(root / "completion.json")
            spec = load_canonical(root / "spec.json")
            if spec["implementation_revision"] != implementation_revision:
                failures.append(f"{control_id}: implementation revision drift")
            completions.append(
                {
                    "control_id": control_id,
                    "completion_sha256": completion["record_sha256"],
                    "projection_sha256": completion["projection_sha256"],
                }
            )
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    evidence = _evidence_manifest(evidence_root)
    authority = seal(
        {
            "schema": RESULT_SCHEMA,
            "status": "accepted-no-credit-real-controls",
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "r1_preregistration_commit": R1_PREREGISTRATION_COMMIT,
            "implementation_revision": implementation_revision,
            "source_inputs": [
                {"path": path, "sha256": sha256_file(ROOT / path)}
                for path in sorted(FROZEN_REPOSITORY_INPUTS)
            ] + [
                {"path": "scripts/lean_execution_acceptance.py", "sha256": sha256_file(Path(__file__).resolve())},
                {"path": "scripts/tests/test_lean_execution_acceptance.py", "sha256": sha256_file(ROOT / "scripts/tests/test_lean_execution_acceptance.py")},
                {"path": PREREGISTRATION_PLAN.relative_to(ROOT).as_posix(), "sha256": sha256_file(PREREGISTRATION_PLAN)},
            ],
            "build": {
                "record_sha256": build["record_sha256"],
                "exporter_sha256": build["executable"]["sha256"],
                "exporter_bytes": build["executable"]["bytes"],
                "source_commit": EXPORTER_COMMIT,
                "source_tree": EXPORTER_TREE,
            },
            "failed_attempt": {
                "control_id": FAILED_COMPILE_CONTROL,
                "implementation_revision": FAILED_IMPLEMENTATION_REVISION,
                "state": "failed-incomplete-no-completion",
                "raw_stderr_sha256": "32a60967270365f092cad81a408cf0e68f13aceab4359f32700f140a54129b9b",
                "evidence_files": failed_evidence,
                "evidence_manifest_sha256": FAILED_EVIDENCE_MANIFEST_SHA256,
                "credits": ZERO_CREDITS,
            },
            "controls": completions,
            "summary": {
                "observed_external_controls": 2,
                "observed_external_process_attempts": 3,
                "failed_external_process_attempts": 1,
                "completed_external_controls": 2,
                "retained_files": len(evidence) + len(failed_evidence),
                "retained_bytes": sum(item["bytes"] for item in evidence)
                + sum(item["bytes"] for item in failed_evidence),
                "u2_cases": 0,
                "case_records": 0,
                "official_outcomes": 0,
                "axeyum_outcomes": 0,
                "paired_cells": 0,
                "performance_rows": 0,
            },
            "evidence_files": evidence,
            "evidence_manifest_sha256": domain_digest(
                "axeyum-lean-execution-acceptance-evidence-files-v1", evidence
            ),
            "claims": {
                "real_process_controls": True,
                "failed_compile_attempt_retained": True,
                "pinned_lean_compile_observed": True,
                "official_export_observed": True,
                "reference_stream_byte_equal": True,
                "official_u2_execution": False,
                "axeyum_import_or_check": False,
                "paired_comparison": False,
                "performance_measurement": False,
                "power_or_host_loss_durability": False,
            },
            "credits": ZERO_CREDITS,
            "record_sha256": "",
        },
        RESULT_SCHEMA,
    )
    return authority


def validate_result_authority(authority: Any) -> list[str]:
    failures = []
    if (
        not isinstance(authority, dict) or set(authority) != RESULT_FIELDS
        or not valid_seal(authority, RESULT_SCHEMA)
    ):
        return ["result authority identity drift"]
    if (
        authority.get("status") != "accepted-no-credit-real-controls"
        or authority.get("preregistration_commit") != PREREGISTRATION_COMMIT
        or authority.get("r1_preregistration_commit") != R1_PREREGISTRATION_COMMIT
        or not isinstance(authority.get("implementation_revision"), str)
        or not HEX40.fullmatch(authority["implementation_revision"])
    ):
        failures.append("result preregistration identity drift")
    if authority.get("credits") != ZERO_CREDITS:
        failures.append("acceptance result cannot receive parity credit")
    summary = authority.get("summary", {})
    for field in (
        "u2_cases", "case_records", "official_outcomes", "axeyum_outcomes",
        "paired_cells", "performance_rows",
    ):
        if summary.get(field) != 0:
            failures.append(f"result {field} must remain zero")
    if len(authority.get("controls", [])) != 2:
        failures.append("result must close exactly two controls")
    if (
        summary.get("observed_external_controls") != 2
        or summary.get("observed_external_process_attempts") != 3
        or summary.get("failed_external_process_attempts") != 1
        or summary.get("completed_external_controls") != 2
    ):
        failures.append("result observed/completed process counts drift")
    failed_attempt = authority.get("failed_attempt")
    if (
        not isinstance(failed_attempt, dict)
        or failed_attempt.get("control_id") != FAILED_COMPILE_CONTROL
        or failed_attempt.get("implementation_revision") != FAILED_IMPLEMENTATION_REVISION
        or failed_attempt.get("state") != "failed-incomplete-no-completion"
        or failed_attempt.get("evidence_manifest_sha256")
        != FAILED_EVIDENCE_MANIFEST_SHA256
        or domain_digest(
            "axeyum-lean-execution-acceptance-failed-evidence-v1",
            failed_attempt.get("evidence_files"),
        )
        != FAILED_EVIDENCE_MANIFEST_SHA256
        or failed_attempt.get("credits") != ZERO_CREDITS
    ):
        failures.append("result failed-attempt closure drift")
    evidence = authority.get("evidence_files")
    if (
        not isinstance(evidence, list)
        or authority.get("evidence_manifest_sha256")
        != domain_digest("axeyum-lean-execution-acceptance-evidence-files-v1", evidence)
    ):
        failures.append("result evidence manifest identity drift")
    return failures


def result_summary(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": SUMMARY_SCHEMA,
        "status": authority["status"],
        "implementation_revision": authority["implementation_revision"],
        "summary": authority["summary"],
        "claims": authority["claims"],
        "credits": authority["credits"],
        "authority_sha256": authority["record_sha256"],
    }


def render_markdown(authority: dict[str, Any]) -> str:
    summary = authority["summary"]
    build = authority["build"]
    controls = "\n".join(
        f"| `{item['control_id']}` | `{item['completion_sha256']}` | `{item['projection_sha256']}` |"
        for item in authority["controls"]
    )
    return f"""# TL0.7.4 Lean execution acceptance summary

Generated from [`lean-execution-acceptance-v1.json`](../lean-execution-acceptance-v1.json).

- Status: **accepted no-credit real controls**
- Implementation revision: `{authority['implementation_revision']}`
- Official exporter source: `{build['source_commit']}` / tree `{build['source_tree']}`
- Built exporter SHA-256: `{build['exporter_sha256']}` ({build['exporter_bytes']:,} bytes)
- Observed process attempts / completed controls: **3 / 2**
- Retained failed compile attempts: **1**
- Retained evidence: **{summary['retained_files']} files / {summary['retained_bytes']:,} bytes**
- U2 cases, official outcomes, Axeyum outcomes, paired cells, and performance rows: **0**
- Terminal Lean parity credit: **0**

| Control | Completion SHA-256 | Stable projection SHA-256 |
|---|---|---|
{controls}

The compile and export processes are real, but both selections are empty. The
export stream is byte-equal to the preregistered 65-line reference. This result
does not run U2, import or check with Axeyum, form a pair, measure performance,
or qualify power/host/network/object durability.
"""


def generate_result(
    *, evidence_root: Path, implementation_revision: str | None, check: bool
) -> None:
    if check:
        if not RESULT_AUTHORITY.is_file():
            raise AcceptanceEvidenceError("missing committed result authority")
        authority = load_json_document(RESULT_AUTHORITY)
        failures = validate_result_authority(authority)
        if failures:
            raise AcceptanceEvidenceError("; ".join(failures))
        rebuilt = build_result_authority(
            evidence_root, implementation_revision=authority["implementation_revision"]
        )
        if rebuilt != authority:
            raise AcceptanceEvidenceError("committed result authority is stale")
    else:
        if implementation_revision is None:
            raise AcceptanceEvidenceError("generation requires --implementation-revision")
        authority = build_result_authority(
            evidence_root, implementation_revision=implementation_revision
        )
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(result_summary(authority), indent=2) + "\n",
        RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [path for path, content in outputs.items() if not path.is_file() or path.read_text() != content]
        if stale:
            raise AcceptanceEvidenceError(
                "stale generated result: "
                + ", ".join(path.relative_to(ROOT).as_posix() for path in stale)
            )
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(
        "LEAN_EXECUTION_ACCEPTANCE|controls=2|u2_cases=0|official_outcomes=0|"
        "axeyum_outcomes=0|paired_cells=0|performance_rows=0|parity_credit=0"
    )


def run_pair(args: argparse.Namespace) -> None:
    failures = validate_repository_inputs()
    if failures:
        raise AcceptanceEvidenceError("; ".join(failures))
    current = _git(ROOT, "rev-parse", "HEAD")
    if current != args.implementation_revision:
        raise AcceptanceEvidenceError("working revision differs from implementation revision")
    status = _git(ROOT, "status", "--porcelain=v1", "--untracked-files=all")
    if status:
        raise AcceptanceEvidenceError("working tree must be clean before authoritative controls")
    if args.work_root.exists():
        raise AcceptanceEvidenceError("private work root must be new")
    args.work_root.mkdir(parents=True, mode=0o700)
    build = capture_build_record(
        source_root=args.exporter_source_root,
        lean=args.lean,
        lake=args.lake,
        exporter=args.exporter,
        failed_stdout=args.failed_stdout,
        failed_stderr=args.failed_stderr,
        success_stdout=args.success_stdout,
        success_stderr=args.success_stderr,
        evidence_root=args.evidence_root,
    )
    compile_private = args.work_root / "compile"
    compile_spec = build_control_spec(
        COMPILE_CONTROL,
        implementation_revision=args.implementation_revision,
        lean=args.lean,
        lake=args.lake,
        exporter=args.exporter,
        exporter_source_root=args.exporter_source_root,
        private_root=compile_private,
        compile_artifact_directory=None,
        build_record=build,
    )
    compile_root = args.evidence_root / "controls" / COMPILE_CONTROL
    compile_completion = execute_control(
        compile_spec, control_root=compile_root, private_root=compile_private
    )
    export_private = args.work_root / "export"
    compile_artifacts = compile_root / "artifacts"
    export_spec = build_control_spec(
        EXPORT_CONTROL,
        implementation_revision=args.implementation_revision,
        lean=args.lean,
        lake=args.lake,
        exporter=args.exporter,
        exporter_source_root=args.exporter_source_root,
        private_root=export_private,
        compile_artifact_directory=compile_artifacts,
        build_record=build,
        compile_completion=compile_completion,
    )
    export_root = args.evidence_root / "controls" / EXPORT_CONTROL
    execute_control(export_spec, control_root=export_root, private_root=export_private)
    print(
        "LEAN_EXECUTION_ACCEPTANCE_LIVE|controls=2|completed=2|selection=empty|credit=zero"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command_name", required=True)
    run = subparsers.add_parser("run-pair")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--lean", type=Path, required=True)
    run.add_argument("--lake", type=Path, required=True)
    run.add_argument("--exporter", type=Path, required=True)
    run.add_argument("--exporter-source-root", type=Path, required=True)
    run.add_argument("--failed-stdout", type=Path, required=True)
    run.add_argument("--failed-stderr", type=Path, required=True)
    run.add_argument("--success-stdout", type=Path, required=True)
    run.add_argument("--success-stderr", type=Path, required=True)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = subparsers.add_parser("validate-control")
    validate.add_argument("--control", choices=CONTROL_IDS, required=True)
    validate.add_argument("--root", type=Path, required=True)
    result = subparsers.add_parser("result")
    result.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result.add_argument("--implementation-revision")
    result.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.command_name == "run-pair":
            run_pair(args)
        elif args.command_name == "validate-control":
            failures = validate_control_store(args.root, expected_control=args.control)
            if failures:
                raise AcceptanceEvidenceError("; ".join(failures))
            print(f"LEAN_EXECUTION_ACCEPTANCE_CONTROL_VALID|control={args.control}|credit=zero")
        elif args.command_name == "result":
            generate_result(
                evidence_root=args.evidence_root,
                implementation_revision=args.implementation_revision,
                check=args.check,
            )
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except (AcceptanceEvidenceError, CheckpointConflict) as exc:
        print(f"LEAN_EXECUTION_ACCEPTANCE_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
