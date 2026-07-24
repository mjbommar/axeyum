#!/usr/bin/env python3
"""Run and validate the preregistered TL0.6.3 M0 official Lean case shard."""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_execution_process as PROCESS  # noqa: E402
from scripts import lean_execution_store as STORE  # noqa: E402
from scripts.lean_vendored_resume_fs import (  # noqa: E402
    atomic_install_bytes,
    atomic_install_json,
    canonical_bytes,
)


PLAN = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-plan-2026-07-22.md"
PREREGISTRATION_COMMIT = "cdc6b94f2ebe68cc4b2ac254ca79a99e8f6f6e00"
PLAN_SHA256 = "6c8aeeadca17ac79b9b949f504b1a4b8a9bc1c52c8343e4f2eebcbd045158e90"
R1_PLAN = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r1-plan-2026-07-22.md"
R1_PREREGISTRATION_COMMIT = "01d357d07b9fa699e42569ce27b085880f2c2a31"
R1_PLAN_SHA256 = "bdf5348916db12668b0bed53ac67f1b5408f58a2efaecce7c54d95cb52045ec4"
R1_AMENDMENT = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r1-"
    "git-mode-amendment-2026-07-22.md"
)
R1_AMENDMENT_COMMIT = "77623b4067093b518ad36b39bc848ae1847c59bb"
R1_AMENDMENT_SHA256 = "13b3152b1f7e78cef2991b20d4403dc1f0c1d4940e2453436689ebca7b99ab28"
RESULT_AUTHORITY = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0.md"
DEFAULT_EVIDENCE_ROOT = ROOT / "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0"

LEAN_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
LEAN_TREE = "0271450d1b109f9a0e5fadea2b6044160e9af7dd"
PARENT_CONTEXT_ID = "release-tag-l3"
PARENT_CONTEXT_SHA256 = "a2757855ea11633699e982418e53ae86f7b8e6807764202bcc06a7eeb83463c2"
PARENT_CELL_ID = "release-tag-l3--linux-release"
PARENT_CELL_SHA256 = "4da2ce61fca4141c2b963bc3dc94610ceebd9fee9059d45607cd8a23a621519b"
PARENT_ATTEMPT_ID = "release-tag-l3--linux-release--primary"
PARENT_ATTEMPT_SHA256 = "21e8b9540f42f4ea86c0eb52985b28b09cdd2c4ebb31cd34d723eaac028a48a3"
PARENT_SELECTION_ID = "default-filtered-aec7358564e4"
PARENT_SELECTION_SHA256 = "02132086eb928c862eb19e3523b376342b869d5a159b67f2afecdf3b80db46c2"
PARENT_SELECTED_IDS_SHA256 = "6f5d4dadd9bc51b42521fd6bb07e6fd270f4b638a08156c28cfa6cf7a998a488"
PARENT_SELECTED_COUNT = 3_678
CASE_ID = "compile/534.lean"
CASE_SHA256 = "ea289dd25543d2e90f2da84b79b60598a3848b600262969a8babe228133c0d4f"
CASE_SOURCE = "tests/compile/534.lean"
CASE_SOURCE_SHA256 = "720a6465ce5267560d754b2ebcfbbc237eb06c1a1aaf7d2e0dbd28522dad300e"
CASE_EXPECTED = "tests/compile/534.lean.out.expected"
CASE_EXPECTED_SHA256 = "98ea6e4f216f2fb4b69fff9b3a44842c38686ca685f3f55dc48c5d3fb1107be4"
CASE_RUNNER = "tests/compile/run_test.sh"
CASE_RUNNER_SHA256 = "557fe4726ec23d812a0649c56def2c22daa89faeddc58b7e49b118f3ab123396"
UTIL_SOURCE = "tests/util.sh"
UTIL_SHA256 = "55dbc20818948622b3a16072bed49d9ff5be31df4c766fdb8fa4cfb44c11c092"
WITH_ENV_SOURCE = "tests/with_env.sh.in"
WITH_ENV_SHA256 = "57efe3131b6663ffa8ac3ed01eb18174c5ee4bd61a9331bda69b9dc8627aef97"

PINNED_LEAN_SHA256 = "3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf"
PINNED_LEANC_SHA256 = "519d91f0c9e94c453d420de1ba9d3221c801e3332d4cfc399fc90931c41c23b2"
PINNED_LAKE_SHA256 = "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b"
LEAN_VERSION_LINE = (
    "Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit "
    f"{LEAN_COMMIT}, Release)"
)
LEANC_VERSION_PREFIX = "clang version 19.1.2"
LAKE_VERSION_LINE = "Lake version 5.0.0-src+d024af0 (Lean version 4.30.0)"

BASH_SHA256 = "3efccc187bafa75ff1e37d246270ab3e7aa559f242c7a52bf3ec2a1b5450bdbd"
CTEST_SHA256 = "2cf8308ae2235efcae86a2eba443444f33ab611193a84092de33ec16836f5f17"
CMAKE_SHA256 = "6e1dccda39845415d68eabb934c598998949c99ec4668625d571aee1827b05c7"
PYTHON_SHA256 = "b8d8288faefdd300201f43fcf00f6f539a27218eeed3a3dff5ab10b9c4c99700"
CXX_SHA256 = "e6718f7e0c7d057c3ff77b550c603da9bc4030e3ede3c053705acce1293dbe4d"
CC_SHA256 = "b5f1b773a7c733738352000c92a077dc5852a1a2fc6d836b1e411be1e9ec5f88"
DIFF_SHA256 = "0abb2ec6b0a64efc7fa84747a8534f1d10a2d823599de932a8df4cabf31ca98e"
PERL_SHA256 = "50036d900bc669506ea0899f0ad5c117806d6815c606cba442f955cd1b2ee1cf"

LANE_ID = "official-ctest-local-8g-lean-j1-v2"
MEMORY_LIMIT_BYTES = 8_589_934_592
WALL_TIMEOUT_MS = 120_000
TERMINATE_GRACE_MS = 1_000
RUN_ID = "tl0.6.3-m0-release-tag-linux-release-compile-534"
ATTEMPT_ID = "attempt-002"
SEQUENCE = 2
SHARD_ID = "release-tag-l3-linux-release-compile-534-singleton-v1"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")

HISTORICAL_RESULT_IMPLEMENTATION_REVISION = "1a2e7d3aa59710ba4c5dce7fe7f90f86db4841e4"
HISTORICAL_RESULT_REPOSITORY_INPUTS = {
    "docs/plan/lean-u2-test-authority-v1.json": "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e",
    "docs/plan/lean-u2-official-ci-profiles-v1.json": "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548",
    "docs/plan/lean-execution-evidence-v1.json": "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a",
    "docs/plan/lean-execution-process-v1.json": "0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf",
    "docs/plan/lean-execution-store-v1.json": "e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647",
    "docs/plan/lean-execution-acceptance-v1.json": "bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f",
    "scripts/lean_execution_process.py": "96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007",
    "scripts/lean_execution_store.py": "06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679",
    "scripts/smtcomp_repro/resume_contract.py": "4713707b26d81e0e5444acc7c653b461fa79c2a94c392873c8565b443ba33930",
    "scripts/smtcomp_repro/resume_fs.py": "1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec",
}

REPOSITORY_INPUTS = {
    "docs/plan/lean-u2-test-authority-v1.json": "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e",
    "docs/plan/lean-u2-official-ci-profiles-v1.json": "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548",
    "docs/plan/lean-execution-evidence-v1.json": "83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a",
    "docs/plan/lean-execution-process-v1.json": "0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf",
    "docs/plan/lean-execution-store-v1.json": "e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647",
    "docs/plan/lean-execution-acceptance-v1.json": "bd3f01fc5ac61bbcfdf23a82055fd58d47cf8167240727ec35e51ceb2a4be05f",
    "scripts/lean_execution_process.py": "96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007",
    "scripts/lean_execution_store.py": "06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679",
    "scripts/lean_vendored_resume_fs.py": "a60e6d300f193c5f7ee8444573e84a35d145f65a79c444000a0f6e5bf1416a5e",
    "scripts/lean_resume_fs_fixture_worker.py": "858fd5fcc45022e5e704f9becda885d190f5384c7f851dd8f23a3409e295f54b",
}

CURRENT_REPOSITORY_INPUT_OVERRIDES = {
    "scripts/lean_execution_process.py": "b2f90c46928afad352fbf95390c5e54858ce792b5d20677f1ba25978375f7948",
    "scripts/lean_execution_store.py": "acf0fa7f30f8509b298968daa8a505f7cb0010274ce8a42b2fa070411105dc9a",
}

HISTORICAL_RESULT_GENERATOR_INPUTS = (
    {
        "path": "scripts/lean_u2_official_execution.py",
        "sha256": "47c779d5b465e32b1ffa8faf3598472ed2ac98bd058928494e65a68d4f205fc2",
    },
    {
        "path": "scripts/tests/test_lean_u2_official_execution.py",
        "sha256": "0b5346109aba8b5222056577ef72ce9d375ebb63bb2883a3e91e588bcb4b2119",
    },
)

ZERO_NON_OFFICIAL_CREDITS = {
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
    "parent_profile_completions": 0,
    "provider_completions": 0,
}

FAILED_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/"
    "lean-u2-official-execution-tl0.6.3-m0-attempt-001-failed"
)
FAILED_EVIDENCE_FILE_COUNT = 18
FAILED_EVIDENCE_BYTES = 4_757_134
FAILED_EVIDENCE_MANIFEST_DOMAIN = (
    "axeyum-lean-u2-official-execution-attempt-evidence-v1"
)
FAILED_EVIDENCE_MANIFEST_SHA256 = (
    "7b8452e0a003a11867d2fc2150c00af99a0a61f41b10238b88a3ed2bb3838065"
)
FAILED_EVIDENCE_JSON_PATHS = (
    "harness.json",
    "junit.json",
    "prelaunch.json",
    "run.json",
    "source.json",
    "spec.json",
    "terminal.json",
    "toolchain.json",
    "tools.json",
)
FAILED_TERMINAL_SHA256 = (
    "93d033a92b1ba13631cf754ec717cf6058afb5a76e4a617eab1891331d93a55e"
)
FAILED_JUNIT_SHA256 = (
    "03b4aec0d34fdbbadd9acae8327934d7d90da87593ae74ecd49cc01f0069f687"
)
UNICODE_SOURCE_PATHS = (
    "tests/compile/utf8Path.lean.英語",
    "tests/elab/utf8英語.lean",
)

SPEC_SCHEMA = "axeyum-lean-u2-official-execution-spec-v1"
SOURCE_SCHEMA = "axeyum-lean-u2-official-execution-source-v1"
TOOLCHAIN_SCHEMA = "axeyum-lean-u2-official-execution-toolchain-v1"
TOOLS_SCHEMA = "axeyum-lean-u2-official-execution-local-tools-v1"
HARNESS_SCHEMA = "axeyum-lean-u2-official-execution-harness-v1"
RUN_SCHEMA = "axeyum-lean-u2-official-execution-run-v1"
PRELAUNCH_SCHEMA = "axeyum-lean-u2-official-execution-prelaunch-v1"
TERMINAL_SCHEMA = "axeyum-lean-u2-official-execution-terminal-v1"
JUNIT_SCHEMA = "axeyum-lean-u2-official-execution-junit-v1"
CASE_SCHEMA = "axeyum-lean-u2-official-execution-case-v1"
POST_SCHEMA = "axeyum-lean-u2-official-execution-post-v1"
COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-completion-v1"
RESULT_SCHEMA = "axeyum-lean-u2-official-execution-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-u2-official-execution-summary-v1"

CASE_GENERATED_SOURCE_PATHS = (
    "tests/with_stage1_test_env.sh",
    "tests/compile/534.lean.c",
    "tests/compile/534.lean.out",
    "tests/compile/534.lean.out.produced",
)
CTEST_SOURCE_PATHS = (
    "build/release/Testing/Temporary/CTestCostData.txt",
    "build/release/Testing/Temporary/LastTest.log",
    "build/release/Testing/Temporary/LastTestsFailed.log",
)
CTEST_REQUIRED_SOURCE_PATHS = CTEST_SOURCE_PATHS[:2]
GENERATED_SOURCE_PATHS = (*CASE_GENERATED_SOURCE_PATHS, *CTEST_SOURCE_PATHS)
EVIDENCE_GENERATED_PATHS = {
    **{
        relative: f"artifacts/generated/{Path(relative).name}"
        for relative in CASE_GENERATED_SOURCE_PATHS
    },
    **{
        relative: f"artifacts/ctest/{Path(relative).name}"
        for relative in CTEST_SOURCE_PATHS
    },
}
BASE_EVIDENCE_PATHS = (
    "source.json",
    "toolchain.json",
    "tools.json",
    "harness.json",
    "artifacts/with_stage1_test_env.sh",
    "artifacts/CTestTestfile.cmake",
    "raw/discovery.json",
    "spec.json",
    "run.json",
    "prelaunch.json",
    "raw/stderr.bin",
    "raw/stdout.bin",
    "terminal.json",
    "raw/junit.xml",
    "junit.json",
    "post.json",
    *(
        EVIDENCE_GENERATED_PATHS[path]
        for path in (*CASE_GENERATED_SOURCE_PATHS, *CTEST_REQUIRED_SOURCE_PATHS)
    ),
    "case.json",
    "completion.json",
)


class U2ExecutionError(ValueError):
    """The source, selection, process, JUnit, store, or credit contract failed."""


def legacy_canonical_bytes(value: Any) -> bytes:
    """Attempt-001's frozen ASCII-escaping seal serializer."""

    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def digest(value: Any) -> str:
    return sha256_bytes(canonical_bytes(value))


def seal(value: dict[str, Any], schema: str) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result["record_sha256"] = domain_digest(
        schema, {key: item for key, item in result.items() if key != "record_sha256"}
    )
    return result


def valid_seal(value: Any, schema: str) -> bool:
    return (
        isinstance(value, dict)
        and value.get("schema") == schema
        and value.get("record_sha256")
        == domain_digest(
            schema, {key: item for key, item in value.items() if key != "record_sha256"}
        )
    )


def legacy_domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + legacy_canonical_bytes(value))


def valid_legacy_seal(value: Any, schema: str) -> bool:
    return (
        isinstance(value, dict)
        and value.get("schema") == schema
        and value.get("record_sha256")
        == legacy_domain_digest(
            schema, {key: item for key, item in value.items() if key != "record_sha256"}
        )
    )


def metric(state: str, value: int | None, unit: str) -> dict[str, Any]:
    return {"state": state, "value": value, "unit": unit}


def load_canonical(path: Path) -> Any:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise U2ExecutionError(f"malformed canonical JSON: {path}") from exc
    if raw != canonical_bytes(value):
        raise U2ExecutionError(f"noncanonical JSON: {path}")
    return value


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise U2ExecutionError(f"malformed JSON: {path}") from exc


def install_json(root: Path, relative: str, value: Any) -> None:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise U2ExecutionError(f"unsafe evidence path: {relative}")
    atomic_install_json(
        root / path.parent,
        path.name,
        value,
        quarantine_root=root / "quarantine",
    )


def install_bytes(root: Path, relative: str, value: bytes) -> None:
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise U2ExecutionError(f"unsafe evidence path: {relative}")
    atomic_install_bytes(
        root / path.parent,
        path.name,
        value,
        quarantine_root=root / "quarantine",
    )


def file_record(relative: str, path: Path) -> dict[str, Any]:
    return {"path": relative, "bytes": path.stat().st_size, "sha256": sha256_file(path)}


def validate_repository_inputs() -> list[str]:
    failures = []
    if not PLAN.is_file() or sha256_file(PLAN) != PLAN_SHA256:
        failures.append("preregistration plan drift")
    if not R1_PLAN.is_file() or sha256_file(R1_PLAN) != R1_PLAN_SHA256:
        failures.append("R1 preregistration plan drift")
    if not R1_AMENDMENT.is_file() or sha256_file(R1_AMENDMENT) != R1_AMENDMENT_SHA256:
        failures.append("R1 Git-mode amendment drift")
    for relative, historical_expected in REPOSITORY_INPUTS.items():
        expected = CURRENT_REPOSITORY_INPUT_OVERRIDES.get(
            relative, historical_expected
        )
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            failures.append(f"frozen repository input drift: {relative}")
    return failures


def _run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None, timeout: int = 60) -> subprocess.CompletedProcess[bytes]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=env or {"LANG": "C.UTF-8", "PATH": "/usr/bin:/bin"},
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        timeout=timeout,
    )
    return completed


def _git(repo: Path, *args: str) -> str:
    completed = _run(["/usr/bin/git", "-C", str(repo), *args], cwd=ROOT)
    if completed.returncode != 0:
        raise U2ExecutionError(
            "git identity command failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    return completed.stdout.decode("utf-8", errors="strict").strip()


def failed_attempt_dependency(
    *, live_readonly_validated: bool, git_index_validated: bool
) -> dict[str, Any]:
    return {
        "path": FAILED_EVIDENCE_ROOT.relative_to(ROOT).as_posix(),
        "implementation_revision": "bc59fda54a2b6d7aa253173e5203c0aa4c0461ca",
        "attempt_id": "attempt-001",
        "files": FAILED_EVIDENCE_FILE_COUNT,
        "bytes": FAILED_EVIDENCE_BYTES,
        "manifest_domain": FAILED_EVIDENCE_MANIFEST_DOMAIN,
        "manifest_sha256": FAILED_EVIDENCE_MANIFEST_SHA256,
        "terminal_sha256": FAILED_TERMINAL_SHA256,
        "junit_sha256": FAILED_JUNIT_SHA256,
        "physical_utf8_canonical_validated": True,
        "frozen_legacy_seals_validated": True,
        "no_case_post_or_completion": True,
        "official_outcomes": 0,
        "parity_credit": 0,
        "live_readonly_mode": {
            "validated": live_readonly_validated,
            "mode": "0444" if live_readonly_validated else None,
        },
        "git_index_mode": {
            "validated": git_index_validated,
            "mode": "100644" if git_index_validated else None,
        },
    }


def _validate_git_regular_modes(root: Path, relative_paths: list[str]) -> None:
    try:
        relative_root = root.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise U2ExecutionError("failed evidence is outside the repository") from exc
    staged = _git(ROOT, "ls-files", "--stage", "--", relative_root)
    rows: dict[str, str] = {}
    for line in staged.splitlines():
        metadata, separator, path = line.partition("\t")
        fields = metadata.split()
        if not separator or len(fields) != 3:
            raise U2ExecutionError("malformed Git index row for failed evidence")
        rows[path] = fields[0]
    expected = {f"{relative_root}/{relative}" for relative in relative_paths}
    if set(rows) != expected or any(rows[path] != "100644" for path in expected):
        raise U2ExecutionError("failed evidence Git path or regular-file mode drift")


def validate_failed_attempt(
    root: Path = FAILED_EVIDENCE_ROOT,
    *,
    require_live_readonly: bool,
    require_git_index: bool,
) -> dict[str, Any]:
    if not root.is_dir() or root.is_symlink():
        raise U2ExecutionError("failed-attempt evidence root must be a real directory")
    rows: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise U2ExecutionError(f"symlinked failed-attempt evidence: {relative}")
        if stat.S_ISREG(info.st_mode):
            if require_live_readonly and stat.S_IMODE(info.st_mode) != 0o444:
                raise U2ExecutionError(
                    f"live failed-attempt evidence is not mode 0444: {relative}"
                )
            rows.append(file_record(relative, path))
        elif not stat.S_ISDIR(info.st_mode):
            raise U2ExecutionError(f"non-regular failed-attempt evidence: {relative}")
    if (
        len(rows) != FAILED_EVIDENCE_FILE_COUNT
        or sum(row["bytes"] for row in rows) != FAILED_EVIDENCE_BYTES
        or domain_digest(FAILED_EVIDENCE_MANIFEST_DOMAIN, rows)
        != FAILED_EVIDENCE_MANIFEST_SHA256
    ):
        raise U2ExecutionError("failed-attempt path, byte, hash, or manifest drift")
    paths = [row["path"] for row in rows]
    if any(path in paths for path in ("post.json", "case.json", "completion.json")):
        raise U2ExecutionError("failed attempt gained a retrospective outcome")
    for relative in FAILED_EVIDENCE_JSON_PATHS:
        record = load_canonical(root / relative)
        schema = record.get("schema") if isinstance(record, dict) else None
        if not isinstance(schema, str) or not valid_legacy_seal(record, schema):
            raise U2ExecutionError(f"failed-attempt legacy seal drift: {relative}")
    source = load_canonical(root / "source.json")
    source_paths = {
        row.get("path") for row in source.get("files", []) if isinstance(row, dict)
    }
    if not set(UNICODE_SOURCE_PATHS).issubset(source_paths):
        raise U2ExecutionError("failed source manifest lost frozen Unicode paths")
    if load_canonical(root / "terminal.json").get("record_sha256") != FAILED_TERMINAL_SHA256:
        raise U2ExecutionError("failed terminal identity drift")
    if load_canonical(root / "junit.json").get("record_sha256") != FAILED_JUNIT_SHA256:
        raise U2ExecutionError("failed JUnit identity drift")
    if require_git_index:
        _validate_git_regular_modes(root, paths)
    return failed_attempt_dependency(
        live_readonly_validated=require_live_readonly,
        git_index_validated=require_git_index,
    )


def validate_live_readonly_tree(root: Path) -> None:
    if not root.is_dir() or root.is_symlink():
        raise U2ExecutionError("live evidence root must be a real directory")
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise U2ExecutionError(f"symlinked live evidence path: {relative}")
        if stat.S_ISREG(info.st_mode) and stat.S_IMODE(info.st_mode) != 0o444:
            raise U2ExecutionError(f"live evidence is not mode 0444: {relative}")


def manifest_tree(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        mode = stat.S_IMODE(info.st_mode)
        if path.is_symlink():
            target = os.readlink(path)
            rows.append(
                {
                    "path": relative,
                    "kind": "symlink",
                    "mode": mode,
                    "bytes": len(target.encode()),
                    "sha256": sha256_bytes(target.encode()),
                    "target": target,
                }
            )
        elif path.is_file():
            rows.append(
                {
                    "path": relative,
                    "kind": "file",
                    "mode": mode,
                    "bytes": info.st_size,
                    "sha256": sha256_file(path),
                    "target": None,
                }
            )
        elif not path.is_dir():
            raise U2ExecutionError(f"unsupported manifest entry: {path}")
    return rows


def validate_selection_authorities() -> list[str]:
    failures: list[str] = []
    tests = load_json(ROOT / "docs/plan/lean-u2-test-authority-v1.json")
    profiles = load_json(ROOT / "docs/plan/lean-u2-official-ci-profiles-v1.json")
    cases = [item for item in tests.get("cases", []) if item.get("id") == CASE_ID]
    selections = [
        item for item in profiles.get("selection_sets", []) if item.get("id") == PARENT_SELECTION_ID
    ]
    attempts = [
        item for item in profiles.get("attempts", []) if item.get("id") == PARENT_ATTEMPT_ID
    ]
    cells = [item for item in profiles.get("cells", []) if item.get("id") == PARENT_CELL_ID]
    contexts = [
        item for item in profiles.get("contexts", []) if item.get("id") == PARENT_CONTEXT_ID
    ]
    if len(cases) != 1 or cases[0].get("sha256") != CASE_SHA256:
        failures.append("official case identity drift")
    if len(selections) != 1:
        failures.append("parent selection missing or duplicated")
    else:
        selection = selections[0]
        if (
            selection.get("sha256") != PARENT_SELECTION_SHA256
            or selection.get("selected_count") != PARENT_SELECTED_COUNT
            or selection.get("selected_ids_sha256") != PARENT_SELECTED_IDS_SHA256
            or selection.get("exclude_regex") != "foreign"
            or selection.get("selected_case_ids", []).count(CASE_ID) != 1
        ):
            failures.append("parent selection identity or membership drift")
    for rows, expected, label in (
        (attempts, PARENT_ATTEMPT_SHA256, "parent attempt"),
        (cells, PARENT_CELL_SHA256, "parent cell"),
        (contexts, PARENT_CONTEXT_SHA256, "parent context"),
    ):
        if len(rows) != 1 or rows[0].get("sha256") != expected:
            failures.append(f"{label} identity drift")
    return failures


def resource_envelope() -> dict[str, Any]:
    return {
        "lane_id": LANE_ID,
        "memory_limit": metric("observed", MEMORY_LIMIT_BYTES, "bytes"),
        "memory_scope": "per-process-address-space",
        "memory_enforcement": "explicit-rlimit-as",
        "ctest_worker_limit": metric("observed", 1, "workers"),
        "ctest_worker_enforcement": "explicit-command-argument",
        "lean_shell_worker_limit": metric("observed", 1, "workers"),
        "lean_shell_worker_enforcement": "explicit-official-test-argument-array",
        "generated_runtime_worker_limit": metric("requested", 1, "workers"),
        "generated_runtime_worker_enforcement": "LEAN_NUM_THREADS",
        "os_thread_limit": metric("not-enforced", None, "threads"),
        "task_stack_limit": metric("not-observed", None, "bytes"),
        "task_stack_policy": "unmodified-Lean-default-no-s-option",
        "aggregate_memory_limit": metric("not-enforced", None, "bytes"),
        "swap_limit": metric("not-enforced", None, "bytes"),
        "wall_timeout": metric("observed", WALL_TIMEOUT_MS, "milliseconds"),
    }


def build_spec(*, implementation_revision: str, source_root: Path, toolchain_root: Path, harness_build: Path, junit_path: Path) -> dict[str, Any]:
    if not HEX40.fullmatch(implementation_revision):
        raise U2ExecutionError("implementation revision must be a full Git hash")
    command = [
        "/usr/bin/ctest",
        "--preset",
        "release",
        "--test-dir",
        str(harness_build.resolve()),
        "-j1",
        "--output-junit",
        str(junit_path.resolve()),
        "-E",
        "foreign",
        "-R",
        r"^compile/534[.]lean$",
    ]
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "LEAN_NUM_THREADS": "1",
        "PATH": f"{toolchain_root.resolve() / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    return seal(
        {
            "schema": SPEC_SCHEMA,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "r1_preregistration_commit": R1_PREREGISTRATION_COMMIT,
            "r1_plan_sha256": R1_PLAN_SHA256,
            "r1_amendment_commit": R1_AMENDMENT_COMMIT,
            "r1_amendment_sha256": R1_AMENDMENT_SHA256,
            "failed_attempt_manifest_sha256": FAILED_EVIDENCE_MANIFEST_SHA256,
            "implementation_revision": implementation_revision,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "shard_id": SHARD_ID,
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
                "selected_ids_sha256": PARENT_SELECTED_IDS_SHA256,
                "completed": False,
            },
            "selection_case_ids": [CASE_ID],
            "case_sha256": CASE_SHA256,
            "source_root": str(source_root.resolve()),
            "toolchain_root": str(toolchain_root.resolve()),
            "harness_build": str(harness_build.resolve()),
            "command": command,
            "working_directory": str(source_root.resolve()),
            "environment": environment,
            "resource_envelope": resource_envelope(),
            "terminate_grace_ms": TERMINATE_GRACE_MS,
            "credit_class": "local-official-case-outcome-only",
            "record_sha256": "",
        },
        SPEC_SCHEMA,
    )


def validate_spec(spec: Any) -> list[str]:
    failures = []
    if not valid_seal(spec, SPEC_SCHEMA):
        return ["spec identity drift"]
    if (
        spec.get("preregistration_commit") != PREREGISTRATION_COMMIT
        or spec.get("r1_preregistration_commit") != R1_PREREGISTRATION_COMMIT
        or spec.get("r1_plan_sha256") != R1_PLAN_SHA256
        or spec.get("r1_amendment_commit") != R1_AMENDMENT_COMMIT
        or spec.get("r1_amendment_sha256") != R1_AMENDMENT_SHA256
        or spec.get("failed_attempt_manifest_sha256")
        != FAILED_EVIDENCE_MANIFEST_SHA256
        or not HEX40.fullmatch(spec.get("implementation_revision", ""))
        or spec.get("run_id") != RUN_ID
        or spec.get("attempt_id") != ATTEMPT_ID
        or spec.get("sequence") != SEQUENCE
        or spec.get("shard_id") != SHARD_ID
    ):
        failures.append("spec run/preregistration identity drift")
    if spec.get("selection_case_ids") != [CASE_ID] or spec.get("case_sha256") != CASE_SHA256:
        failures.append("spec shard identity drift")
    parent = spec.get("parent", {})
    expected_parent = {
        "context_id": PARENT_CONTEXT_ID,
        "context_sha256": PARENT_CONTEXT_SHA256,
        "cell_id": PARENT_CELL_ID,
        "cell_sha256": PARENT_CELL_SHA256,
        "attempt_id": PARENT_ATTEMPT_ID,
        "attempt_sha256": PARENT_ATTEMPT_SHA256,
        "selection_id": PARENT_SELECTION_ID,
        "selection_sha256": PARENT_SELECTION_SHA256,
        "selected_count": PARENT_SELECTED_COUNT,
        "selected_ids_sha256": PARENT_SELECTED_IDS_SHA256,
        "completed": False,
    }
    if parent != expected_parent:
        failures.append("spec parent profile identity or completion drift")
    if spec.get("resource_envelope") != resource_envelope():
        failures.append("spec resource lane drift")
    command = spec.get("command", [])
    if (
        not isinstance(command, list)
        or len(command) != 12
        or command[:4] != ["/usr/bin/ctest", "--preset", "release", "--test-dir"]
        or command[4] != spec.get("harness_build")
        or command[5:7] != ["-j1", "--output-junit"]
        or not isinstance(command[7], str)
        or not Path(command[7]).is_absolute()
        or command[8:] != ["-E", "foreign", "-R", r"^compile/534[.]lean$"]
    ):
        failures.append("spec derived CTest command drift")
    environment = spec.get("environment", {})
    if (
        not isinstance(environment, dict)
        or environment.get("LANG") != "C.UTF-8"
        or environment.get("LC_ALL") != "C.UTF-8"
        or environment.get("LEAN_NUM_THREADS") != "1"
        or environment.get("TZ") != "UTC"
        or not environment.get("PATH", "").endswith(":/usr/bin:/bin")
    ):
        failures.append("spec environment drift")
    if (
        not isinstance(spec.get("source_root"), str)
        or not Path(spec["source_root"]).is_absolute()
        or spec.get("working_directory") != spec.get("source_root")
        or not isinstance(spec.get("toolchain_root"), str)
        or not Path(spec["toolchain_root"]).is_absolute()
        or environment.get("PATH")
        != f"{Path(str(spec.get('toolchain_root'))).resolve() / 'bin'}:/usr/bin:/bin"
        or not isinstance(spec.get("harness_build"), str)
        or not Path(spec["harness_build"]).is_absolute()
        or spec.get("terminate_grace_ms") != TERMINATE_GRACE_MS
    ):
        failures.append("spec path, working-directory, or grace drift")
    if spec.get("credit_class") != "local-official-case-outcome-only":
        failures.append("spec credit class drift")
    return failures


def capture_source(source_repo: Path, source_root: Path) -> dict[str, Any]:
    source_repo = source_repo.resolve()
    source_root = source_root.resolve()
    if source_root.exists() or source_root.is_symlink():
        raise U2ExecutionError(f"source destination must be new: {source_root}")
    if _git(source_repo, "rev-parse", f"{LEAN_COMMIT}^{{tree}}") != LEAN_TREE:
        raise U2ExecutionError("pinned Lean tree drift")
    source_root.parent.mkdir(parents=True, exist_ok=True)
    archive = source_root.parent / "lean-v4.30.0.tar"
    with archive.open("xb") as handle:
        completed = subprocess.run(
            ["/usr/bin/git", "-C", str(source_repo), "archive", "--format=tar", LEAN_COMMIT],
            stdin=subprocess.DEVNULL,
            stdout=handle,
            stderr=subprocess.PIPE,
            check=False,
            timeout=120,
        )
    if completed.returncode != 0:
        raise U2ExecutionError(
            "pinned Lean archive failed: "
            + completed.stderr.decode("utf-8", errors="replace").strip()
        )
    source_root.mkdir(mode=0o755)
    with tarfile.open(archive) as bundle:
        for member in bundle.getmembers():
            path = Path(member.name)
            if path.is_absolute() or ".." in path.parts:
                raise U2ExecutionError(f"unsafe Lean archive member: {member.name}")
        bundle.extractall(source_root, filter="data")
    archive_sha256 = sha256_file(archive)
    archive_bytes = archive.stat().st_size
    archive.unlink()
    files = manifest_tree(source_root)
    for relative, expected in (
        (CASE_SOURCE, CASE_SOURCE_SHA256),
        (CASE_EXPECTED, CASE_EXPECTED_SHA256),
        (CASE_RUNNER, CASE_RUNNER_SHA256),
        (UTIL_SOURCE, UTIL_SHA256),
        (WITH_ENV_SOURCE, WITH_ENV_SHA256),
    ):
        path = source_root / relative
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise U2ExecutionError(f"pinned official source drift: {relative}")
    return seal(
        {
            "schema": SOURCE_SCHEMA,
            "repository": "https://github.com/leanprover/lean4",
            "commit": LEAN_COMMIT,
            "tree": LEAN_TREE,
            "archive_bytes": archive_bytes,
            "archive_sha256": archive_sha256,
            "file_count": len(files),
            "files_sha256": domain_digest("axeyum-lean-u2-source-files-v1", files),
            "files": files,
            "record_sha256": "",
        },
        SOURCE_SCHEMA,
    )


def _version(executable: Path, *args: str) -> str:
    completed = _run(
        [str(executable.resolve()), *args],
        cwd=ROOT,
        env={"LANG": "C.UTF-8", "PATH": f"{executable.resolve().parent}:/usr/bin:/bin"},
    )
    if completed.returncode != 0:
        raise U2ExecutionError(f"version command failed: {executable}")
    return completed.stdout.decode("utf-8", errors="strict").strip().splitlines()[0]


def executable_record(executable: Path, expected_sha256: str, version: str) -> dict[str, Any]:
    resolved = executable.resolve()
    if not resolved.is_file() or resolved.is_symlink() or sha256_file(resolved) != expected_sha256:
        raise U2ExecutionError(f"executable identity drift: {executable}")
    return {
        "path": str(executable),
        "resolved_path": str(resolved),
        "bytes": resolved.stat().st_size,
        "sha256": expected_sha256,
        "version": version,
    }


def capture_toolchain(toolchain_root: Path) -> dict[str, Any]:
    toolchain_root = toolchain_root.resolve()
    if not toolchain_root.is_dir() or toolchain_root.is_symlink():
        raise U2ExecutionError("toolchain root must be a regular directory")
    lean = toolchain_root / "bin/lean"
    leanc = toolchain_root / "bin/leanc"
    lake = toolchain_root / "bin/lake"
    lean_version = _version(lean, "--version")
    leanc_version = _version(leanc, "--version")
    lake_version = _version(lake, "--version")
    if lean_version != LEAN_VERSION_LINE:
        raise U2ExecutionError("pinned Lean version drift")
    if not leanc_version.startswith(LEANC_VERSION_PREFIX):
        raise U2ExecutionError("pinned leanc version drift")
    if lake_version != LAKE_VERSION_LINE:
        raise U2ExecutionError("pinned Lake version drift")
    files = manifest_tree(toolchain_root)
    return seal(
        {
            "schema": TOOLCHAIN_SCHEMA,
            "root": str(toolchain_root),
            "executables": {
                "lean": executable_record(lean, PINNED_LEAN_SHA256, lean_version),
                "leanc": executable_record(leanc, PINNED_LEANC_SHA256, leanc_version),
                "lake": executable_record(lake, PINNED_LAKE_SHA256, lake_version),
            },
            "file_count": len(files),
            "files_sha256": domain_digest("axeyum-lean-u2-toolchain-files-v1", files),
            "files": files,
            "record_sha256": "",
        },
        TOOLCHAIN_SCHEMA,
    )


def _shell_quote(value: str) -> str:
    return "'" + value.replace("'", "'\\''") + "'"


def render_environment_wrapper(source_root: Path, toolchain_root: Path) -> bytes:
    source = source_root.resolve()
    toolchain = toolchain_root.resolve()
    variables = " ".join(
        (
            "LEAN_CC=/usr/bin/cc",
            "STAGE=1",
            f"SRC_DIR={_shell_quote(str(source))}",
            f"TEST_DIR={_shell_quote(str(source / 'tests'))}",
            f"BUILD_DIR={_shell_quote(str(toolchain))}",
            f"SCRIPT_DIR={_shell_quote(str(source / 'script'))}",
            f"PATH={_shell_quote(str(toolchain / 'bin'))}:\"$PATH\"",
            f"LEANC_OPTS={_shell_quote('-I' + str(toolchain / 'include'))}",
            f"CXX={_shell_quote('/usr/bin/c++ -I' + str(toolchain / 'include'))}",
        )
    )
    return (
        "#!/usr/bin/env bash\n"
        f"export {variables}\n"
        "TEST_LEAN_ARGS=(-j1)\n"
        "TEST_LEANI_ARGS=(-j1)\n"
        'source "$TEST_DIR/util.sh"\n\n'
        'TEST_SCRIPT="$1"; shift\n'
        'cd "$(dirname "$TEST_SCRIPT")"\n'
        'source "$(basename "$TEST_SCRIPT")"\n'
    ).encode()


def render_ctest_file(source_root: Path) -> bytes:
    source = source_root.resolve()
    wrapper = source / "tests/with_stage1_test_env.sh"
    runner = source / CASE_RUNNER
    working = source / "tests/compile"
    return (
        f'add_test([=[{CASE_ID}]=] "/usr/bin/bash" "{wrapper}" "{runner}" "534.lean")\n'
        f'set_tests_properties([=[{CASE_ID}]=] PROPERTIES WORKING_DIRECTORY "{working}")\n'
    ).encode()


def normalize_discovery(payload: Any, *, source_root: Path) -> dict[str, Any]:
    if not isinstance(payload, dict) or not isinstance(payload.get("tests"), list):
        raise U2ExecutionError("malformed CTest discovery JSON")
    tests = payload["tests"]
    if len(tests) != 1 or tests[0].get("name") != CASE_ID:
        raise U2ExecutionError("CTest discovery is not the preregistered singleton")
    test = tests[0]
    command = test.get("command")
    expected_command = [
        "/usr/bin/bash",
        str(source_root.resolve() / "tests/with_stage1_test_env.sh"),
        str(source_root.resolve() / CASE_RUNNER),
        "534.lean",
    ]
    properties = {
        item.get("name"): item.get("value") for item in test.get("properties", [])
        if isinstance(item, dict)
    }
    if command != expected_command:
        raise U2ExecutionError("CTest discovered command drift")
    if properties.get("WORKING_DIRECTORY") != str(source_root.resolve() / "tests/compile"):
        raise U2ExecutionError("CTest discovered working directory drift")
    return {
        "case_id": CASE_ID,
        "command": command,
        "working_directory": properties["WORKING_DIRECTORY"],
    }


def prepare_harness(source_root: Path, toolchain_root: Path, harness_build: Path) -> tuple[dict[str, Any], bytes, bytes, bytes]:
    source_root = source_root.resolve()
    harness_build = harness_build.resolve()
    if harness_build.exists() or harness_build.is_symlink():
        raise U2ExecutionError(f"harness build must be new: {harness_build}")
    harness_build.mkdir(parents=True, mode=0o755)
    wrapper_bytes = render_environment_wrapper(source_root, toolchain_root)
    wrapper = source_root / "tests/with_stage1_test_env.sh"
    if wrapper.exists() or wrapper.is_symlink():
        raise U2ExecutionError("generated environment wrapper already exists")
    wrapper.write_bytes(wrapper_bytes)
    wrapper.chmod(0o755)
    ctest_bytes = render_ctest_file(source_root)
    (harness_build / "CTestTestfile.cmake").write_bytes(ctest_bytes)
    discovery = _run(
        ["/usr/bin/ctest", "--test-dir", str(harness_build), "--show-only=json-v1"],
        cwd=source_root,
        env={"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin", "TZ": "UTC"},
    )
    if discovery.returncode != 0:
        raise U2ExecutionError(
            "CTest discovery failed: "
            + discovery.stderr.decode("utf-8", errors="replace").strip()
        )
    try:
        payload = json.loads(discovery.stdout)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise U2ExecutionError("CTest discovery output is not JSON") from exc
    normalized = normalize_discovery(payload, source_root=source_root)
    record = seal(
        {
            "schema": HARNESS_SCHEMA,
            "case_id": CASE_ID,
            "wrapper": {
                "bytes": len(wrapper_bytes),
                "sha256": sha256_bytes(wrapper_bytes),
                "mode": 0o755,
            },
            "ctest_file": {
                "bytes": len(ctest_bytes),
                "sha256": sha256_bytes(ctest_bytes),
            },
            "discovery": normalized,
            "discovery_raw_bytes": len(discovery.stdout),
            "discovery_raw_sha256": sha256_bytes(discovery.stdout),
            "record_sha256": "",
        },
        HARNESS_SCHEMA,
    )
    return record, wrapper_bytes, ctest_bytes, discovery.stdout


def _raw_descriptor(path: str, value: bytes) -> dict[str, Any]:
    return {"path": path, "bytes": len(value), "sha256": sha256_bytes(value)}


def execute_process(spec: dict[str, Any], private_root: Path, prelaunch_sha256: str) -> tuple[dict[str, Any], bytes, bytes]:
    failures = validate_spec(spec)
    if failures:
        raise U2ExecutionError("; ".join(failures))
    private_root.mkdir(parents=True, mode=0o700)
    stdout_path = private_root / "stdout.bin"
    stderr_path = private_root / "stderr.bin"
    process: subprocess.Popen[bytes] | None = None
    peak_rss: int | None = None
    events = ["prelaunch-record-installed"]
    start_ns = time.monotonic_ns()
    with stdout_path.open("xb", buffering=0) as stdout_handle, stderr_path.open("xb", buffering=0) as stderr_handle:
        try:
            process = subprocess.Popen(
                spec["command"],
                cwd=spec["working_directory"],
                env=spec["environment"],
                stdin=subprocess.DEVNULL,
                stdout=stdout_handle,
                stderr=stderr_handle,
                shell=False,
                close_fds=True,
                start_new_session=True,
                preexec_fn=PROCESS._limit_hook(MEMORY_LIMIT_BYTES),
            )
        except (OSError, subprocess.SubprocessError) as exc:
            raise U2ExecutionError(f"CTest launch failed: {exc}") from exc
        pid = process.pid
        pgid = process.pid
        events.append("rlimit-as-installed")
        deadline_ns = start_ns + WALL_TIMEOUT_MS * 1_000_000
        watchdog = False
        sigterm_sent = False
        sigkill_sent = False
        while process.poll() is None and time.monotonic_ns() < deadline_ns:
            sample = PROCESS._sample_peak_rss(pid)
            if sample is not None:
                peak_rss = max(peak_rss or 0, sample)
            time.sleep(0.01)
        if process.poll() is None:
            watchdog = True
            events.append("wall-timeout-observed")
            try:
                os.killpg(pgid, signal.SIGTERM)
                sigterm_sent = True
                events.append("process-group-sigterm-sent")
            except ProcessLookupError:
                pass
            grace = time.monotonic_ns() + TERMINATE_GRACE_MS * 1_000_000
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
    stdout = stdout_path.read_bytes()
    stderr = stderr_path.read_bytes()
    elapsed_ms = max(1, (time.monotonic_ns() - start_ns) // 1_000_000)
    return_code = process.returncode if process is not None else None
    terminal_class = (
        "wall-timeout"
        if watchdog
        else "signaled"
        if return_code is not None and return_code < 0
        else "exited"
    )
    terminal = seal(
        {
            "schema": TERMINAL_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "prelaunch_sha256": prelaunch_sha256,
            "class": terminal_class,
            "exit_code": return_code if return_code is not None and return_code >= 0 else None,
            "signal": -return_code if return_code is not None and return_code < 0 else None,
            "events": events,
            "wall_time": metric("observed", elapsed_ms, "milliseconds"),
            "cpu_time": metric("not-observed", None, "milliseconds"),
            "peak_rss": (
                metric("observed", peak_rss, "bytes")
                if peak_rss is not None
                else metric("not-observed", None, "bytes")
            ),
            "process": {
                "pid": process.pid if process else None,
                "process_group_id": process.pid if process else None,
                "rlimit_as_bytes": MEMORY_LIMIT_BYTES,
                "watchdog_fired": watchdog,
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


def _tool_version(path: Path, args: list[str]) -> str:
    completed = _run(
        [str(path), *args],
        cwd=ROOT,
        env={"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"},
    )
    if completed.returncode != 0:
        raise U2ExecutionError(f"local tool version command failed: {path}")
    lines = [line for line in completed.stdout.decode("utf-8", errors="strict").splitlines() if line]
    if not lines:
        raise U2ExecutionError(f"local tool returned no version line: {path}")
    return lines[0]


def capture_local_tools() -> dict[str, Any]:
    definitions = {
        "bash": (Path("/usr/bin/bash"), BASH_SHA256, ["--version"]),
        "cmake": (Path("/usr/bin/cmake"), CMAKE_SHA256, ["--version"]),
        "ctest": (Path("/usr/bin/ctest"), CTEST_SHA256, ["--version"]),
        "python": (Path("/usr/bin/python3.14"), PYTHON_SHA256, ["--version"]),
        "cxx": (Path("/usr/bin/c++"), CXX_SHA256, ["--version"]),
        "cc": (Path("/usr/bin/cc"), CC_SHA256, ["--version"]),
        "diff": (Path("/usr/bin/diff"), DIFF_SHA256, ["--version"]),
        "perl": (Path("/usr/bin/perl"), PERL_SHA256, ["-v"]),
    }
    tools = {}
    for name, (path, expected_sha256, args) in definitions.items():
        version = _tool_version(path, args)
        tools[name] = executable_record(path, expected_sha256, version) | {
            "version_argv": [str(path), *args]
        }
    return seal(
        {
            "schema": TOOLS_SCHEMA,
            "tools": tools,
            "record_sha256": "",
        },
        TOOLS_SCHEMA,
    )


def _validate_manifest_rows(rows: Any, label: str) -> list[str]:
    failures: list[str] = []
    if not isinstance(rows, list):
        return [f"{label} manifest is not a list"]
    paths: list[str] = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {
            "path", "kind", "mode", "bytes", "sha256", "target"
        }:
            failures.append(f"{label} manifest row fields drift")
            continue
        path = row.get("path")
        if (
            not isinstance(path, str)
            or not path
            or Path(path).is_absolute()
            or ".." in Path(path).parts
        ):
            failures.append(f"{label} manifest path is unsafe")
        else:
            paths.append(path)
        if row.get("kind") not in {"file", "symlink"}:
            failures.append(f"{label} manifest kind is invalid")
        if not isinstance(row.get("mode"), int) or not 0 <= row["mode"] <= 0o7777:
            failures.append(f"{label} manifest mode is invalid")
        if not isinstance(row.get("bytes"), int) or row["bytes"] < 0:
            failures.append(f"{label} manifest byte count is invalid")
        if not isinstance(row.get("sha256"), str) or not HEX64.fullmatch(row["sha256"]):
            failures.append(f"{label} manifest digest is invalid")
        if row.get("kind") == "file" and row.get("target") is not None:
            failures.append(f"{label} regular file has a symlink target")
        if row.get("kind") == "symlink" and not isinstance(row.get("target"), str):
            failures.append(f"{label} symlink target is invalid")
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        failures.append(f"{label} manifest order or uniqueness drift")
    return failures


def validate_source_record(record: Any) -> list[str]:
    if not valid_seal(record, SOURCE_SCHEMA):
        return ["source record identity drift"]
    failures = _validate_manifest_rows(record.get("files"), "source")
    files = record.get("files", [])
    if (
        record.get("repository") != "https://github.com/leanprover/lean4"
        or record.get("commit") != LEAN_COMMIT
        or record.get("tree") != LEAN_TREE
        or record.get("file_count") != len(files)
        or record.get("files_sha256")
        != domain_digest("axeyum-lean-u2-source-files-v1", files)
        or not isinstance(record.get("archive_bytes"), int)
        or record.get("archive_bytes", 0) <= 0
        or not isinstance(record.get("archive_sha256"), str)
        or not HEX64.fullmatch(record.get("archive_sha256", ""))
    ):
        failures.append("source record content drift")
    by_path = {row.get("path"): row for row in files if isinstance(row, dict)}
    for relative, expected in (
        (CASE_SOURCE, CASE_SOURCE_SHA256),
        (CASE_EXPECTED, CASE_EXPECTED_SHA256),
        (CASE_RUNNER, CASE_RUNNER_SHA256),
        (UTIL_SOURCE, UTIL_SHA256),
        (WITH_ENV_SOURCE, WITH_ENV_SHA256),
    ):
        if by_path.get(relative, {}).get("sha256") != expected:
            failures.append(f"source identity drift: {relative}")
    for relative in UNICODE_SOURCE_PATHS:
        if by_path.get(relative, {}).get("kind") != "file":
            failures.append(f"source Unicode path missing: {relative}")
    return failures


def validate_toolchain_record(record: Any) -> list[str]:
    if not valid_seal(record, TOOLCHAIN_SCHEMA):
        return ["toolchain record identity drift"]
    failures = _validate_manifest_rows(record.get("files"), "toolchain")
    files = record.get("files", [])
    if (
        record.get("file_count") != len(files)
        or record.get("files_sha256")
        != domain_digest("axeyum-lean-u2-toolchain-files-v1", files)
    ):
        failures.append("toolchain manifest aggregate drift")
    executables = record.get("executables")
    expected = {
        "lean": (PINNED_LEAN_SHA256, LEAN_VERSION_LINE),
        "leanc": (PINNED_LEANC_SHA256, LEANC_VERSION_PREFIX),
        "lake": (PINNED_LAKE_SHA256, LAKE_VERSION_LINE),
    }
    if not isinstance(executables, dict) or set(executables) != set(expected):
        failures.append("toolchain executable set drift")
    else:
        for name, (expected_hash, expected_version) in expected.items():
            item = executables[name]
            version = item.get("version") if isinstance(item, dict) else None
            if (
                not isinstance(item, dict)
                or item.get("sha256") != expected_hash
                or not isinstance(item.get("bytes"), int)
                or item.get("bytes", 0) <= 0
                or (
                    version != expected_version
                    if name != "leanc"
                    else not isinstance(version, str) or not version.startswith(expected_version)
                )
            ):
                failures.append(f"toolchain executable drift: {name}")
    return failures


def validate_local_tools(record: Any) -> list[str]:
    if not valid_seal(record, TOOLS_SCHEMA):
        return ["local tools record identity drift"]
    tools = record.get("tools")
    expected = {
        "bash": BASH_SHA256,
        "cmake": CMAKE_SHA256,
        "ctest": CTEST_SHA256,
        "python": PYTHON_SHA256,
        "cxx": CXX_SHA256,
        "cc": CC_SHA256,
        "diff": DIFF_SHA256,
        "perl": PERL_SHA256,
    }
    if not isinstance(tools, dict) or set(tools) != set(expected):
        return ["local tool set drift"]
    failures = []
    for name, expected_sha256 in expected.items():
        item = tools[name]
        if (
            not isinstance(item, dict)
            or item.get("sha256") != expected_sha256
            or not isinstance(item.get("version"), str)
            or not item["version"]
            or not isinstance(item.get("version_argv"), list)
            or not item["version_argv"]
        ):
            failures.append(f"local tool identity drift: {name}")
    return failures


def build_run_record(
    spec: dict[str, Any],
    source: dict[str, Any],
    toolchain: dict[str, Any],
    tools: dict[str, Any],
    harness: dict[str, Any],
    storage: dict[str, Any],
) -> dict[str, Any]:
    platform = PROCESS.capture_platform(Path(spec["working_directory"]))
    libc = _run(["/usr/bin/getconf", "GNU_LIBC_VERSION"], cwd=ROOT)
    platform |= {
        "captured_utc": dt.datetime.now(dt.UTC).isoformat().replace("+00:00", "Z"),
        "uname": list(os.uname()),
        "glibc": (
            libc.stdout.decode("utf-8", errors="strict").strip()
            if libc.returncode == 0
            else "not-observed"
        ),
        "online_cpu_count": os.cpu_count(),
        "official_provider_claimed": False,
    }
    return seal(
        {
            "schema": RUN_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "spec_sha256": spec["record_sha256"],
            "implementation_revision": spec["implementation_revision"],
            "command": spec["command"],
            "command_sha256": digest(spec["command"]),
            "working_directory": spec["working_directory"],
            "environment": spec["environment"],
            "environment_sha256": digest(spec["environment"]),
            "resource_envelope": spec["resource_envelope"],
            "resource_envelope_sha256": digest(spec["resource_envelope"]),
            "source_sha256": source["record_sha256"],
            "toolchain_sha256": toolchain["record_sha256"],
            "tools_sha256": tools["record_sha256"],
            "harness_sha256": harness["record_sha256"],
            "platform": platform,
            "platform_sha256": digest(platform),
            "storage_class": storage,
            "storage_class_sha256": storage["identity_sha256"],
            "credit_class": "local-official-case-outcome-only",
            "record_sha256": "",
        },
        RUN_SCHEMA,
    )


def build_prelaunch(
    spec: dict[str, Any],
    run: dict[str, Any],
    failed_attempt: dict[str, Any],
) -> dict[str, Any]:
    expected_failed = failed_attempt_dependency(
        live_readonly_validated=True, git_index_validated=True
    )
    if failed_attempt != expected_failed:
        raise U2ExecutionError("prelaunch failed-attempt dependency is not fully validated")
    return seal(
        {
            "schema": PRELAUNCH_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "spec_sha256": spec["record_sha256"],
            "run_sha256": run["record_sha256"],
            "failed_attempt": failed_attempt,
            "recorded_before_launch": True,
            "terminal": None,
            "selection_case_ids": [CASE_ID],
            "case_records": [],
            "record_sha256": "",
        },
        PRELAUNCH_SCHEMA,
    )


def _xml_name(element: ET.Element) -> str:
    return element.tag.rsplit("}", 1)[-1]


def _xml_nonnegative_int(value: str | None, label: str) -> int:
    if value is None or not value.isdigit():
        raise U2ExecutionError(f"JUnit {label} count is missing or invalid")
    return int(value)


def parse_junit(raw: bytes, terminal: dict[str, Any]) -> dict[str, Any]:
    try:
        root = ET.fromstring(raw)
    except ET.ParseError as exc:
        raise U2ExecutionError("malformed JUnit XML") from exc
    if _xml_name(root) == "testsuite":
        suites = [root]
    elif _xml_name(root) == "testsuites":
        suites = [item for item in root if _xml_name(item) == "testsuite"]
        if len(suites) != len(list(root)):
            raise U2ExecutionError("JUnit root has non-suite children")
    else:
        raise U2ExecutionError("JUnit root is not testsuite/testsuites")
    if len(suites) != 1:
        raise U2ExecutionError("JUnit must contain exactly one test suite")
    suite = suites[0]
    testcases = [item for item in suite if _xml_name(item) == "testcase"]
    if len(testcases) != 1 or testcases[0].get("name") != CASE_ID:
        raise U2ExecutionError("JUnit test case count or name drift")
    tests = _xml_nonnegative_int(suite.get("tests"), "tests")
    failures = _xml_nonnegative_int(suite.get("failures"), "failures")
    errors = _xml_nonnegative_int(suite.get("errors", "0"), "errors")
    skipped = _xml_nonnegative_int(
        suite.get("skipped", suite.get("disabled", "0")), "skipped"
    )
    if tests != 1 or failures > 1 or errors > 1 or skipped != 0 or failures + errors > 1:
        raise U2ExecutionError("JUnit aggregate counts are not one decided case")
    testcase = testcases[0]
    failure_nodes = [
        item for item in testcase if _xml_name(item) in {"failure", "error"}
    ]
    skipped_nodes = [item for item in testcase if _xml_name(item) == "skipped"]
    if skipped_nodes or len(failure_nodes) != failures + errors:
        raise U2ExecutionError("JUnit child and aggregate outcomes disagree")
    clean_terminal = (
        terminal.get("class") == "exited"
        and terminal.get("exit_code") == 0
        and terminal.get("signal") is None
        and terminal.get("process", {}).get("watchdog_fired") is False
        and terminal.get("process", {}).get("direct_child_reaped") is True
        and terminal.get("process", {}).get("live_non_zombie_pids_after_cleanup") == []
    )
    if failures + errors == 0:
        if not clean_terminal:
            raise U2ExecutionError("passing JUnit disagrees with process terminal")
        outcome = "passed"
    else:
        if terminal.get("class") != "exited" or terminal.get("exit_code") in {None, 0}:
            raise U2ExecutionError("failed JUnit disagrees with process terminal")
        outcome = "failed"
    duration = testcase.get("time", suite.get("time"))
    if duration is not None:
        try:
            if not (float(duration) >= 0.0 and float(duration) < float("inf")):
                raise ValueError
        except ValueError as exc:
            raise U2ExecutionError("JUnit duration is invalid") from exc
    return seal(
        {
            "schema": JUNIT_SCHEMA,
            "raw": _raw_descriptor("raw/junit.xml", raw),
            "suite": {
                "name": suite.get("name"),
                "tests": tests,
                "failures": failures,
                "errors": errors,
                "skipped": skipped,
            },
            "testcase": {
                "name": CASE_ID,
                "classname": testcase.get("classname"),
                "duration_seconds_text": duration,
                "outcome": outcome,
            },
            "terminal_sha256": terminal["record_sha256"],
            "record_sha256": "",
        },
        JUNIT_SCHEMA,
    )


def build_post_record(
    source_root: Path,
    source: dict[str, Any],
    wrapper_bytes: bytes,
    outcome: str,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    if outcome not in {"passed", "failed"}:
        raise U2ExecutionError("post-run outcome is not decided")
    before = {row["path"]: row for row in source["files"]}
    after_rows = manifest_tree(source_root)
    after = {row["path"]: row for row in after_rows}
    changed = [path for path, row in before.items() if after.get(path) != row]
    if changed:
        raise U2ExecutionError("official source or sidecar mutated: " + ", ".join(changed[:5]))
    new_paths = sorted(set(after) - set(before))
    undeclared = sorted(set(new_paths) - set(GENERATED_SOURCE_PATHS))
    if undeclared:
        raise U2ExecutionError("undeclared generated source artifacts: " + ", ".join(undeclared))
    present = set(new_paths)
    required = {
        "tests/with_stage1_test_env.sh",
        *CTEST_REQUIRED_SOURCE_PATHS,
    }
    if outcome == "passed":
        if CTEST_SOURCE_PATHS[2] in present:
            raise U2ExecutionError("passing case retained LastTestsFailed.log")
        expected = {*CASE_GENERATED_SOURCE_PATHS, *CTEST_REQUIRED_SOURCE_PATHS}
        if present != expected:
            raise U2ExecutionError("passing case did not create the exact declared artifact set")
    else:
        required.add(CTEST_SOURCE_PATHS[2])
        if not required.issubset(present):
            raise U2ExecutionError("failed case did not create the required CTest artifact set")
    if any(after[path].get("kind") != "file" for path in new_paths):
        raise U2ExecutionError("generated artifact is not a regular file")
    payloads = {path: (source_root / path).read_bytes() for path in new_paths}
    if payloads["tests/with_stage1_test_env.sh"] != wrapper_bytes:
        raise U2ExecutionError("generated environment wrapper mutated")
    generated = [after[path] for path in new_paths]
    return (
        seal(
            {
                "schema": POST_SCHEMA,
                "source_record_sha256": source["record_sha256"],
                "original_file_count": len(before),
                "original_files_unchanged": True,
                "generated_paths": new_paths,
                "case_generated_paths": [
                    path for path in new_paths if path in CASE_GENERATED_SOURCE_PATHS
                ],
                "ctest_generated_paths": [
                    path for path in new_paths if path in CTEST_SOURCE_PATHS
                ],
                "generated_files": generated,
                "generated_files_sha256": domain_digest(
                    "axeyum-lean-u2-generated-files-v1", generated
                ),
                "undeclared_paths": [],
                "record_sha256": "",
            },
            POST_SCHEMA,
        ),
        payloads,
    )


def case_credits(outcome: str) -> dict[str, int]:
    return {
        "official_cases": 1,
        "official_outcomes": 1,
        "official_passes": int(outcome == "passed"),
        "official_failures": int(outcome == "failed"),
        **ZERO_NON_OFFICIAL_CREDITS,
    }


def build_case_record(
    spec: dict[str, Any],
    terminal: dict[str, Any],
    junit: dict[str, Any],
    post: dict[str, Any],
) -> dict[str, Any]:
    outcome = junit["testcase"]["outcome"]
    return seal(
        {
            "schema": CASE_SCHEMA,
            "case_id": CASE_ID,
            "case_sha256": CASE_SHA256,
            "source_path": CASE_SOURCE,
            "source_sha256": CASE_SOURCE_SHA256,
            "expected_output_path": CASE_EXPECTED,
            "expected_output_sha256": CASE_EXPECTED_SHA256,
            "runner_path": CASE_RUNNER,
            "runner_sha256": CASE_RUNNER_SHA256,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "shard_id": SHARD_ID,
            "parent": spec["parent"],
            "terminal_sha256": terminal["record_sha256"],
            "junit_sha256": junit["record_sha256"],
            "post_sha256": post["record_sha256"],
            "output_policy": "process-exit-zero-and-exact-output-sidecar",
            "outcome": outcome,
            "local_shard_only": True,
            "official_provider_claimed": False,
            "credits": case_credits(outcome),
            "record_sha256": "",
        },
        CASE_SCHEMA,
    )


def _evidence_inventory(root: Path, *, include_completion: bool) -> list[dict[str, Any]]:
    rows = []
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root).as_posix()
        if "quarantine" in Path(relative).parts or (
            not include_completion and relative == "completion.json"
        ):
            continue
        rows.append(file_record(relative, path))
    return rows


def build_completion(root: Path, case: dict[str, Any]) -> dict[str, Any]:
    dependencies = _evidence_inventory(root, include_completion=False)
    projection = {
        "run_id": RUN_ID,
        "attempt_id": ATTEMPT_ID,
        "shard_id": SHARD_ID,
        "parent_selection_id": PARENT_SELECTION_ID,
        "parent_selected_count": PARENT_SELECTED_COUNT,
        "parent_completed": False,
        "provider_completed": False,
        "case_id": CASE_ID,
        "case_outcome": case["outcome"],
        "credits": case["credits"],
    }
    return seal(
        {
            "schema": COMPLETION_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "state": "complete-local-case-outcome",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": domain_digest(
                "axeyum-lean-u2-official-execution-record-set-v1", dependencies
            ),
            "case_records": [
                {"case_id": CASE_ID, "record_sha256": case["record_sha256"]}
            ],
            "projection": projection,
            "projection_sha256": digest(projection),
            "credits": case["credits"],
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def _accepted_readonly(path: Path) -> bool:
    return path.is_file() and not path.is_symlink() and stat.S_IMODE(path.stat().st_mode) == 0o444


def validate_evidence_root(
    root: Path, *, require_live_readonly: bool = False
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not root.is_dir() or root.is_symlink():
        raise U2ExecutionError("official execution evidence root must be a real directory")
    validate_failed_attempt(
        require_live_readonly=False,
        require_git_index=True,
    )
    required_records = (
        "source.json", "toolchain.json", "tools.json", "harness.json", "spec.json",
        "run.json", "prelaunch.json", "terminal.json", "junit.json", "post.json",
        "case.json", "completion.json",
    )
    try:
        records = {relative: load_canonical(root / relative) for relative in required_records}
    except U2ExecutionError:
        raise
    post = records["post.json"]
    generated_paths = post.get("generated_paths") if isinstance(post, dict) else None
    if not isinstance(generated_paths, list) or not all(
        isinstance(path, str) and path in GENERATED_SOURCE_PATHS for path in generated_paths
    ) or generated_paths != sorted(set(generated_paths)):
        raise U2ExecutionError("post-run generated path set is invalid")
    expected = set(BASE_EVIDENCE_PATHS) - set(EVIDENCE_GENERATED_PATHS.values())
    expected.update(EVIDENCE_GENERATED_PATHS[path] for path in generated_paths)
    actual = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        if "quarantine" in Path(relative).parts:
            continue
        if path.is_symlink():
            raise U2ExecutionError(f"symlinked evidence path: {relative}")
        if path.is_file():
            actual.add(relative)
            if require_live_readonly and not _accepted_readonly(path):
                raise U2ExecutionError(f"accepted evidence is not read-only: {relative}")
    if actual != expected:
        raise U2ExecutionError("official execution evidence file set drift")

    source = records["source.json"]
    toolchain = records["toolchain.json"]
    tools = records["tools.json"]
    harness = records["harness.json"]
    spec = records["spec.json"]
    run = records["run.json"]
    prelaunch = records["prelaunch.json"]
    terminal = records["terminal.json"]
    junit = records["junit.json"]
    case = records["case.json"]
    completion = records["completion.json"]
    if not all(
        isinstance(record, dict)
        for record in (
            source, toolchain, tools, harness, spec, run, prelaunch, terminal,
            junit, post, case, completion,
        )
    ):
        raise U2ExecutionError("official execution record must be a JSON object")
    failures = validate_source_record(source)
    failures.extend(validate_toolchain_record(toolchain))
    failures.extend(validate_local_tools(tools))
    failures.extend(validate_spec(spec))

    wrapper = (root / "artifacts/with_stage1_test_env.sh").read_bytes()
    ctest_file = (root / "artifacts/CTestTestfile.cmake").read_bytes()
    discovery_raw = (root / "raw/discovery.json").read_bytes()
    try:
        discovery = normalize_discovery(json.loads(discovery_raw), source_root=Path(spec["source_root"]))
    except (UnicodeDecodeError, json.JSONDecodeError, KeyError, U2ExecutionError) as exc:
        failures.append(f"retained CTest discovery drift: {exc}")
        discovery = None
    if (
        not valid_seal(harness, HARNESS_SCHEMA)
        or harness.get("case_id") != CASE_ID
        or harness.get("wrapper")
        != {"bytes": len(wrapper), "sha256": sha256_bytes(wrapper), "mode": 0o755}
        or harness.get("ctest_file")
        != {"bytes": len(ctest_file), "sha256": sha256_bytes(ctest_file)}
        or harness.get("discovery") != discovery
        or harness.get("discovery_raw_bytes") != len(discovery_raw)
        or harness.get("discovery_raw_sha256") != sha256_bytes(discovery_raw)
        or wrapper != render_environment_wrapper(Path(spec["source_root"]), Path(spec["toolchain_root"]))
        or ctest_file != render_ctest_file(Path(spec["source_root"]))
    ):
        failures.append("harness identity, discovery, or payload drift")

    storage = run.get("storage_class") if isinstance(run, dict) else None
    if (
        not valid_seal(run, RUN_SCHEMA)
        or run.get("run_id") != RUN_ID
        or run.get("attempt_id") != ATTEMPT_ID
        or run.get("spec_sha256") != spec.get("record_sha256")
        or run.get("implementation_revision") != spec.get("implementation_revision")
        or run.get("command") != spec.get("command")
        or run.get("command_sha256") != digest(spec.get("command"))
        or run.get("working_directory") != spec.get("working_directory")
        or run.get("environment") != spec.get("environment")
        or run.get("environment_sha256") != digest(spec.get("environment"))
        or run.get("resource_envelope") != spec.get("resource_envelope")
        or run.get("resource_envelope_sha256") != digest(spec.get("resource_envelope"))
        or run.get("source_sha256") != source.get("record_sha256")
        or run.get("toolchain_sha256") != toolchain.get("record_sha256")
        or run.get("tools_sha256") != tools.get("record_sha256")
        or run.get("harness_sha256") != harness.get("record_sha256")
        or run.get("platform_sha256") != digest(run.get("platform"))
        or run.get("storage_class_sha256")
        != (storage.get("identity_sha256") if isinstance(storage, dict) else None)
        or run.get("credit_class") != "local-official-case-outcome-only"
    ):
        failures.append("run record identity or dependency drift")
    if STORE.validate_storage_descriptor(storage):
        failures.append("run storage class drift")
    platform = run.get("platform", {}) if isinstance(run, dict) else {}
    if (
        not isinstance(platform, dict)
        or platform.get("provider") != "local-process"
        or platform.get("official_provider_claimed") is not False
        or not isinstance(platform.get("captured_utc"), str)
        or not platform.get("glibc")
        or not isinstance(platform.get("online_cpu_count"), int)
    ):
        failures.append("run platform record drift")

    if (
        not valid_seal(prelaunch, PRELAUNCH_SCHEMA)
        or prelaunch.get("run_id") != RUN_ID
        or prelaunch.get("attempt_id") != ATTEMPT_ID
        or prelaunch.get("sequence") != SEQUENCE
        or prelaunch.get("spec_sha256") != spec.get("record_sha256")
        or prelaunch.get("run_sha256") != run.get("record_sha256")
        or prelaunch.get("failed_attempt")
        != failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )
        or prelaunch.get("recorded_before_launch") is not True
        or prelaunch.get("terminal") is not None
        or prelaunch.get("selection_case_ids") != [CASE_ID]
        or prelaunch.get("case_records") != []
    ):
        failures.append("prelaunch identity or ordering drift")

    stderr = (root / "raw/stderr.bin").read_bytes()
    stdout = (root / "raw/stdout.bin").read_bytes()
    process = terminal.get("process", {}) if isinstance(terminal, dict) else {}
    expected_raw = [
        _raw_descriptor("raw/stderr.bin", stderr),
        _raw_descriptor("raw/stdout.bin", stdout),
    ]
    if (
        not valid_seal(terminal, TERMINAL_SCHEMA)
        or terminal.get("run_id") != RUN_ID
        or terminal.get("attempt_id") != ATTEMPT_ID
        or terminal.get("sequence") != SEQUENCE
        or terminal.get("prelaunch_sha256") != prelaunch.get("record_sha256")
        or terminal.get("class") != "exited"
        or terminal.get("signal") is not None
        or not isinstance(terminal.get("exit_code"), int)
        or terminal.get("raw_outputs") != expected_raw
        or not isinstance(process, dict)
        or process.get("rlimit_as_bytes") != MEMORY_LIMIT_BYTES
        or process.get("watchdog_fired") is not False
        or process.get("direct_child_reaped") is not True
        or process.get("live_non_zombie_pids_after_cleanup") != []
    ):
        failures.append("terminal process, attribution, or raw-output drift")

    raw_junit = (root / "raw/junit.xml").read_bytes()
    try:
        rebuilt_junit = parse_junit(raw_junit, terminal)
    except U2ExecutionError as exc:
        failures.append(str(exc))
        rebuilt_junit = None
    if junit != rebuilt_junit:
        failures.append("JUnit canonical projection drift")

    generated_rows = post.get("generated_files", []) if isinstance(post, dict) else []
    generated_by_path = {
        row.get("path"): row for row in generated_rows if isinstance(row, dict)
    }
    source_by_path = {
        row.get("path"): row for row in source.get("files", []) if isinstance(row, dict)
    }
    if (
        not valid_seal(post, POST_SCHEMA)
        or post.get("source_record_sha256") != source.get("record_sha256")
        or post.get("original_file_count") != len(source_by_path)
        or post.get("original_files_unchanged") is not True
        or post.get("undeclared_paths") != []
        or post.get("case_generated_paths")
        != [path for path in generated_paths if path in CASE_GENERATED_SOURCE_PATHS]
        or post.get("ctest_generated_paths")
        != [path for path in generated_paths if path in CTEST_SOURCE_PATHS]
        or post.get("generated_files_sha256")
        != domain_digest("axeyum-lean-u2-generated-files-v1", generated_rows)
        or [row.get("path") for row in generated_rows] != generated_paths
    ):
        failures.append("post-run source closure drift")
    for source_path in generated_paths:
        evidence_path = EVIDENCE_GENERATED_PATHS[source_path]
        payload = (root / evidence_path).read_bytes()
        row = generated_by_path.get(source_path, {})
        if (
            row.get("kind") != "file"
            or row.get("bytes") != len(payload)
            or row.get("sha256") != sha256_bytes(payload)
        ):
            failures.append(f"generated artifact payload drift: {source_path}")
    if "tests/with_stage1_test_env.sh" not in generated_paths:
        failures.append("post-run wrapper is missing")

    outcome = junit.get("testcase", {}).get("outcome") if isinstance(junit, dict) else None
    if outcome == "passed":
        expected_pass = {*CASE_GENERATED_SOURCE_PATHS, *CTEST_REQUIRED_SOURCE_PATHS}
        if set(generated_paths) != expected_pass:
            failures.append("passing case did not retain the exact generated artifact set")
    elif outcome == "failed":
        required_failure = {
            "tests/with_stage1_test_env.sh",
            *CTEST_REQUIRED_SOURCE_PATHS,
            CTEST_SOURCE_PATHS[2],
        }
        if not required_failure.issubset(generated_paths):
            failures.append("failed case did not retain the required CTest artifact set")
    expected_case = (
        build_case_record(spec, terminal, junit, post)
        if isinstance(junit, dict) and valid_seal(junit, JUNIT_SCHEMA)
        else None
    )
    if case != expected_case:
        failures.append("official case record drift")
    elif case.get("official_provider_claimed") is not False or case.get("credits") != case_credits(outcome):
        failures.append("official case credit drift")

    expected_completion = build_completion(root, case) if isinstance(case, dict) else None
    if completion != expected_completion:
        failures.append("completion dependency, projection, ordering, or credit drift")
    if failures:
        raise U2ExecutionError("; ".join(failures))
    return completion, _evidence_inventory(root, include_completion=True)


def run_m0(args: argparse.Namespace) -> None:
    failures = validate_repository_inputs() + validate_selection_authorities()
    if failures:
        raise U2ExecutionError("; ".join(failures))
    failed_attempt = validate_failed_attempt(
        require_live_readonly=True,
        require_git_index=True,
    )
    current = _git(ROOT, "rev-parse", "HEAD")
    if current != args.implementation_revision:
        raise U2ExecutionError("working revision differs from implementation revision")
    if _git(ROOT, "rev-parse", "@{upstream}") != current:
        raise U2ExecutionError("implementation revision is not at the tracking revision")
    if _git(ROOT, "status", "--porcelain=v1", "--untracked-files=all"):
        raise U2ExecutionError("working tree must be clean before official execution")
    if args.work_root.exists() or args.work_root.is_symlink():
        raise U2ExecutionError("private work root must be new")
    if args.evidence_root.exists() or args.evidence_root.is_symlink():
        raise U2ExecutionError("evidence root must be new")
    args.work_root.mkdir(parents=True, mode=0o700)
    source_root = args.work_root / "source"
    harness_build = args.work_root / "harness"
    private_root = args.work_root / "attempt"
    junit_path = private_root / "test-results.xml"

    source = capture_source(args.source_repo, source_root)
    toolchain = capture_toolchain(args.toolchain_root)
    tools = capture_local_tools()
    harness, wrapper_bytes, ctest_bytes, discovery_raw = prepare_harness(
        source_root, args.toolchain_root, harness_build
    )
    spec = build_spec(
        implementation_revision=args.implementation_revision,
        source_root=source_root,
        toolchain_root=args.toolchain_root,
        harness_build=harness_build,
        junit_path=junit_path,
    )
    spec_failures = validate_spec(spec)
    if spec_failures:
        raise U2ExecutionError("; ".join(spec_failures))
    storage = STORE.capture_storage_class(STORE.STORAGE_CLASS_IDS[0], ROOT)
    STORE.preflight_storage_class(storage)
    run = build_run_record(spec, source, toolchain, tools, harness, storage)
    prelaunch = build_prelaunch(spec, run, failed_attempt)

    args.evidence_root.mkdir(parents=True, mode=0o755)
    for relative, value in (
        ("source.json", source),
        ("toolchain.json", toolchain),
        ("tools.json", tools),
        ("harness.json", harness),
        ("spec.json", spec),
        ("run.json", run),
        ("prelaunch.json", prelaunch),
    ):
        install_json(args.evidence_root, relative, value)
    install_bytes(args.evidence_root, "artifacts/with_stage1_test_env.sh", wrapper_bytes)
    install_bytes(args.evidence_root, "artifacts/CTestTestfile.cmake", ctest_bytes)
    install_bytes(args.evidence_root, "raw/discovery.json", discovery_raw)
    validate_live_readonly_tree(args.evidence_root)

    terminal, stdout, stderr = execute_process(spec, private_root, prelaunch["record_sha256"])
    install_bytes(args.evidence_root, "raw/stdout.bin", stdout)
    install_bytes(args.evidence_root, "raw/stderr.bin", stderr)
    install_json(args.evidence_root, "terminal.json", terminal)
    validate_live_readonly_tree(args.evidence_root)
    process = terminal["process"]
    if (
        terminal["class"] != "exited"
        or terminal["signal"] is not None
        or process["watchdog_fired"]
        or not process["direct_child_reaped"]
        or process["live_non_zombie_pids_after_cleanup"] != []
    ):
        raise U2ExecutionError("official CTest process did not close as an exited, reaped group")
    if not junit_path.is_file() or junit_path.is_symlink():
        raise U2ExecutionError("official CTest process produced no regular JUnit file")
    raw_junit = junit_path.read_bytes()
    install_bytes(args.evidence_root, "raw/junit.xml", raw_junit)
    junit = parse_junit(raw_junit, terminal)
    install_json(args.evidence_root, "junit.json", junit)
    validate_live_readonly_tree(args.evidence_root)
    post, generated = build_post_record(
        source_root, source, wrapper_bytes, junit["testcase"]["outcome"]
    )
    for source_path, payload in generated.items():
        install_bytes(args.evidence_root, EVIDENCE_GENERATED_PATHS[source_path], payload)
    install_json(args.evidence_root, "post.json", post)
    validate_live_readonly_tree(args.evidence_root)
    case = build_case_record(spec, terminal, junit, post)
    install_json(args.evidence_root, "case.json", case)
    validate_live_readonly_tree(args.evidence_root)
    completion = build_completion(args.evidence_root, case)
    install_json(args.evidence_root, "completion.json", completion)
    validate_live_readonly_tree(args.evidence_root)
    validate_evidence_root(args.evidence_root, require_live_readonly=True)
    print(
        f"LEAN_U2_OFFICIAL_M0|case={CASE_ID}|outcome={case['outcome']}|"
        "official_outcomes=1|parent_complete=false|provider=false|parity_credit=0"
    )


def build_result_authority(root: Path, *, implementation_revision: str) -> dict[str, Any]:
    if not HEX40.fullmatch(implementation_revision):
        raise U2ExecutionError("implementation revision must be a full Git hash")
    failures = validate_repository_inputs() + validate_selection_authorities()
    if failures:
        raise U2ExecutionError("; ".join(failures))
    completion, evidence = validate_evidence_root(root)
    spec = load_canonical(root / "spec.json")
    prelaunch = load_canonical(root / "prelaunch.json")
    case = load_canonical(root / "case.json")
    terminal = load_canonical(root / "terminal.json")
    if spec["implementation_revision"] != implementation_revision:
        raise U2ExecutionError("result implementation revision differs from retained spec")
    test_path = ROOT / HISTORICAL_RESULT_GENERATOR_INPUTS[1]["path"]
    if not test_path.is_file():
        raise U2ExecutionError("missing official execution contract tests")
    result_repository_inputs = (
        HISTORICAL_RESULT_REPOSITORY_INPUTS
        if implementation_revision == HISTORICAL_RESULT_IMPLEMENTATION_REVISION
        else REPOSITORY_INPUTS
    )
    source_inputs = [
        {"path": path, "sha256": result_repository_inputs[path]}
        for path in sorted(result_repository_inputs)
    ] + [
        {"path": PLAN.relative_to(ROOT).as_posix(), "sha256": sha256_file(PLAN)},
        {"path": R1_PLAN.relative_to(ROOT).as_posix(), "sha256": sha256_file(R1_PLAN)},
        {
            "path": R1_AMENDMENT.relative_to(ROOT).as_posix(),
            "sha256": sha256_file(R1_AMENDMENT),
        },
    ] + list(HISTORICAL_RESULT_GENERATOR_INPUTS)
    credits = case["credits"]
    return seal(
        {
            "schema": RESULT_SCHEMA,
            "status": "complete-local-official-case-outcome",
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "r1_preregistration_commit": R1_PREREGISTRATION_COMMIT,
            "r1_amendment_commit": R1_AMENDMENT_COMMIT,
            "implementation_revision": implementation_revision,
            "source_inputs": source_inputs,
            "failed_attempt": prelaunch["failed_attempt"],
            "attempts": [
                {
                    "id": "attempt-001",
                    "sequence": 1,
                    "status": "incomplete-process-failure",
                    "terminal_sha256": FAILED_TERMINAL_SHA256,
                    "junit_sha256": FAILED_JUNIT_SHA256,
                    "evidence_manifest_sha256": FAILED_EVIDENCE_MANIFEST_SHA256,
                    "official_outcomes": 0,
                    "parity_credit": 0,
                },
                {
                    "id": ATTEMPT_ID,
                    "sequence": SEQUENCE,
                    "status": "complete-local-official-case-outcome",
                    "terminal_sha256": terminal["record_sha256"],
                    "junit_sha256": load_canonical(root / "junit.json")["record_sha256"],
                    "completion_sha256": completion["record_sha256"],
                    "official_outcomes": 1,
                    "parity_credit": 0,
                },
            ],
            "parent": spec["parent"],
            "shard": {
                "id": SHARD_ID,
                "selection_case_ids": [CASE_ID],
                "completed": True,
                "completion_sha256": completion["record_sha256"],
            },
            "case": {
                "id": CASE_ID,
                "outcome": case["outcome"],
                "record_sha256": case["record_sha256"],
            },
            "terminal": {
                "class": terminal["class"],
                "exit_code": terminal["exit_code"],
                "wall_time": terminal["wall_time"],
                "peak_rss": terminal["peak_rss"],
                "record_sha256": terminal["record_sha256"],
            },
            "summary": {
                "parent_selected_cases": PARENT_SELECTED_COUNT,
                "process_attempts": 2,
                "incomplete_process_attempts": 1,
                "completed_process_attempts": 1,
                "local_shard_selected_cases": 1,
                "local_shard_completed_cases": 1,
                "official_outcomes": 1,
                "official_passes": credits["official_passes"],
                "official_failures": credits["official_failures"],
                "parent_profiles_completed": 0,
                "providers_completed": 0,
                "axeyum_outcomes": 0,
                "paired_cells": 0,
                "performance_rows": 0,
                "complete_axes": 0,
                "satisfied_gates": 0,
            },
            "claims": {
                "official_lean_case_observed": True,
                "local_shard_complete": True,
                "parent_profile_complete": False,
                "official_provider_reproduced": False,
                "axeyum_observed": False,
                "matched_pair_formed": False,
                "performance_measured": False,
                "lean_parity_established": False,
            },
            "evidence_files": evidence,
            "evidence_manifest_sha256": domain_digest(
                "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
            ),
            "credits": credits,
            "record_sha256": "",
        },
        RESULT_SCHEMA,
    )


def validate_result_authority(authority: Any) -> list[str]:
    if not valid_seal(authority, RESULT_SCHEMA):
        return ["official execution result authority identity drift"]
    failures = []
    if (
        authority.get("status") != "complete-local-official-case-outcome"
        or authority.get("preregistration_commit") != PREREGISTRATION_COMMIT
        or authority.get("r1_preregistration_commit") != R1_PREREGISTRATION_COMMIT
        or authority.get("r1_amendment_commit") != R1_AMENDMENT_COMMIT
        or not HEX40.fullmatch(authority.get("implementation_revision", ""))
    ):
        failures.append("result preregistration or implementation identity drift")
    if authority.get("failed_attempt") != failed_attempt_dependency(
        live_readonly_validated=True, git_index_validated=True
    ):
        failures.append("result failed-attempt dependency drift")
    attempts = authority.get("attempts")
    if (
        not isinstance(attempts, list)
        or len(attempts) != 2
        or attempts[0]
        != {
            "id": "attempt-001",
            "sequence": 1,
            "status": "incomplete-process-failure",
            "terminal_sha256": FAILED_TERMINAL_SHA256,
            "junit_sha256": FAILED_JUNIT_SHA256,
            "evidence_manifest_sha256": FAILED_EVIDENCE_MANIFEST_SHA256,
            "official_outcomes": 0,
            "parity_credit": 0,
        }
        or not isinstance(attempts[1], dict)
        or attempts[1].get("id") != ATTEMPT_ID
        or attempts[1].get("sequence") != SEQUENCE
        or attempts[1].get("status") != "complete-local-official-case-outcome"
        or attempts[1].get("official_outcomes") != 1
        or attempts[1].get("parity_credit") != 0
        or not HEX64.fullmatch(attempts[1].get("terminal_sha256", ""))
        or not HEX64.fullmatch(attempts[1].get("junit_sha256", ""))
        or not HEX64.fullmatch(attempts[1].get("completion_sha256", ""))
    ):
        failures.append("result attempt history drift")
    parent = authority.get("parent", {})
    if parent.get("completed") is not False or parent.get("selected_count") != PARENT_SELECTED_COUNT:
        failures.append("result parent profile completion drift")
    shard = authority.get("shard", {})
    if (
        shard.get("id") != SHARD_ID
        or shard.get("selection_case_ids") != [CASE_ID]
        or shard.get("completed") is not True
        or not HEX64.fullmatch(shard.get("completion_sha256", ""))
    ):
        failures.append("result shard completion drift")
    case = authority.get("case", {})
    if case.get("id") != CASE_ID or case.get("outcome") not in {"passed", "failed"}:
        failures.append("result case outcome drift")
    expected_credits = case_credits(case.get("outcome")) if case.get("outcome") in {"passed", "failed"} else None
    if authority.get("credits") != expected_credits:
        failures.append("result credit boundary drift")
    summary = authority.get("summary", {})
    zero_fields = {
        "parent_profiles_completed", "providers_completed", "axeyum_outcomes",
        "paired_cells", "performance_rows", "complete_axes", "satisfied_gates",
    }
    if (
        summary.get("parent_selected_cases") != PARENT_SELECTED_COUNT
        or summary.get("process_attempts") != 2
        or summary.get("incomplete_process_attempts") != 1
        or summary.get("completed_process_attempts") != 1
        or summary.get("local_shard_selected_cases") != 1
        or summary.get("local_shard_completed_cases") != 1
        or summary.get("official_outcomes") != 1
        or any(summary.get(field) != 0 for field in zero_fields)
    ):
        failures.append("result count or non-official credit drift")
    claims = authority.get("claims", {})
    if claims != {
        "official_lean_case_observed": True,
        "local_shard_complete": True,
        "parent_profile_complete": False,
        "official_provider_reproduced": False,
        "axeyum_observed": False,
        "matched_pair_formed": False,
        "performance_measured": False,
        "lean_parity_established": False,
    }:
        failures.append("result claims drift")
    evidence = authority.get("evidence_files")
    if (
        not isinstance(evidence, list)
        or authority.get("evidence_manifest_sha256")
        != domain_digest("axeyum-lean-u2-official-execution-evidence-files-v1", evidence)
    ):
        failures.append("result evidence manifest drift")
    return failures


def result_summary(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": SUMMARY_SCHEMA,
        "status": authority["status"],
        "implementation_revision": authority["implementation_revision"],
        "attempts": authority["attempts"],
        "case": authority["case"],
        "summary": authority["summary"],
        "claims": authority["claims"],
        "credits": authority["credits"],
        "authority_sha256": authority["record_sha256"],
    }


def render_markdown(authority: dict[str, Any]) -> str:
    case = authority["case"]
    terminal = authority["terminal"]
    evidence_bytes = sum(row["bytes"] for row in authority["evidence_files"])
    return f"""# TL0.6.3 M0 official Lean execution summary

Generated from [`lean-u2-official-execution-tl0.6.3-m0-v1.json`](../lean-u2-official-execution-tl0.6.3-m0-v1.json).

- Status: **complete local official-case outcome**
- Implementation revision: `{authority['implementation_revision']}`
- Official case: `{case['id']}` — **{case['outcome']}**
- Process terminal: `{terminal['class']}` / exit `{terminal['exit_code']}`
- Process attempts: **2** (**1** incomplete / **1** completed local outcome)
- Parent selection coverage: **1 / {PARENT_SELECTED_COUNT:,}**
- Retained evidence: **{len(authority['evidence_files'])} files / {evidence_bytes:,} bytes**
- Parent-profile completions, provider completions, Axeyum outcomes, matched pairs, performance rows: **0**
- Complete parity axes / satisfied terminal gates / Lean parity credit: **0 / 0 / 0**

This authority retains attempt 001's process failure with zero outcomes and
attempt 002's one local outcome from an official Lean CTest registration. It
does not complete the parent release-tag Linux-release profile, reproduce an
official GitHub Actions provider, observe Axeyum, form a matched both-system
cell, measure performance, or establish complete Lean 4 parity.
"""


def generate_result(*, root: Path, implementation_revision: str | None, check: bool) -> None:
    if check:
        if not RESULT_AUTHORITY.is_file():
            raise U2ExecutionError("missing committed official execution result authority")
        authority = load_json(RESULT_AUTHORITY)
        failures = validate_result_authority(authority)
        if failures:
            raise U2ExecutionError("; ".join(failures))
        rebuilt = build_result_authority(
            root, implementation_revision=authority["implementation_revision"]
        )
        if rebuilt != authority:
            raise U2ExecutionError("committed official execution result authority is stale")
    else:
        if implementation_revision is None:
            raise U2ExecutionError("result generation requires --implementation-revision")
        authority = build_result_authority(root, implementation_revision=implementation_revision)
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(result_summary(authority), indent=2) + "\n",
        RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [
            path for path, content in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != content
        ]
        if stale:
            raise U2ExecutionError(
                "stale official execution result: "
                + ", ".join(path.relative_to(ROOT).as_posix() for path in stale)
            )
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    print(
        f"LEAN_U2_OFFICIAL_RESULT|case={CASE_ID}|outcome={authority['case']['outcome']}|"
        "parent_complete=false|provider=false|axeyum=0|pairs=0|parity_credit=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command_name", required=True)
    run = commands.add_parser("run-m0")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--source-repo", type=Path, required=True)
    run.add_argument("--toolchain-root", type=Path, required=True)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result = commands.add_parser("result")
    result.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    result.add_argument("--implementation-revision")
    result.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        if args.command_name == "run-m0":
            run_m0(args)
        elif args.command_name == "validate":
            completion, _ = validate_evidence_root(args.evidence_root)
            print(
                f"LEAN_U2_OFFICIAL_EVIDENCE_VALID|case={CASE_ID}|"
                f"outcome={completion['projection']['case_outcome']}|parity_credit=0"
            )
        elif args.command_name == "result":
            generate_result(
                root=args.evidence_root,
                implementation_revision=args.implementation_revision,
                check=args.check,
            )
        else:  # pragma: no cover
            raise AssertionError(args.command_name)
    except (U2ExecutionError, STORE.CheckpointConflict, STORE.StoreEvidenceError) as exc:
        print(f"LEAN_U2_OFFICIAL_ERROR|{exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
