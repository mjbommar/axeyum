#!/usr/bin/env python3
"""Run and validate TL0.6.3 M0 attempt-003 without mutating R1 replay semantics."""

from __future__ import annotations

import argparse
import base64
import copy
import json
import stat
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

from scripts import lean_u2_official_execution as BASE


ROOT = BASE.ROOT
R2_PLAN = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r2-plan-2026-07-22.md"
R2_PREREGISTRATION_COMMIT = "f1ad1043fd2c95e4295345046013ae895c415f05"
R2_PLAN_SHA256 = "1c926eb7f1a5e0e147c4cb54ea9a709c5fc6ed8a9c80108b1cfd526a530eb7b1"
R1_AUTHORITY = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-v1.json"
R1_AUTHORITY_BYTES_SHA256 = (
    "61c7bb015dee1cb767b6c460a08f2c4416a62f1c41e040c817fd5b0d6ea24f8d"
)
R1_AUTHORITY_RECORD_SHA256 = (
    "fe1a61fd0ec3e2fed918d46711cec66644b0980795dfaf80fe9ed401556dfa6e"
)
R1_EVIDENCE_ROOT = ROOT / "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0"
R1_EVIDENCE_FILE_COUNT = 23
R1_EVIDENCE_BYTES = 4_778_395
R1_EVIDENCE_MANIFEST_DOMAIN = "axeyum-lean-u2-official-execution-evidence-files-v1"
R1_EVIDENCE_MANIFEST_SHA256 = (
    "7b08bb0a450676db217ba138ccff34dccf9c682c587ea5f25fd6b8bcc0cfecef"
)
R1_TERMINAL_SHA256 = (
    "a0d2cef7134a9301458250cc1fa5de360aacbbdc342fbe81e13d962640a0dc20"
)
R1_JUNIT_SHA256 = "65deb3bef7c2c9910f5763731eda116c7453bc6f11069184a9801226d039852c"
R1_COMPLETION_SHA256 = (
    "85d4c1b4b478157d1f54b35c993e559f8ab5fd2f7489dce7b2b842d4d06c9e91"
)

LANE_ID = "official-ctest-local-8g-lean-j1-bundled-cc-v3"
ATTEMPT_ID = "attempt-003"
SEQUENCE = 3
DEFAULT_EVIDENCE_ROOT = (
    ROOT / "docs/plan/evidence/lean-u2-official-execution-tl0.6.3-m0-r2"
)
RESULT_AUTHORITY = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r2-v1.json"
RESULT_JSON = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0-r2.json"
RESULT_MARKDOWN = ROOT / "docs/plan/generated/lean-u2-official-execution-tl0.6.3-m0-r2.md"
RESULT_SCHEMA = "axeyum-lean-u2-official-execution-r2-result-v1"
SUMMARY_SCHEMA = "axeyum-lean-u2-official-execution-r2-summary-v1"

CLANG_SHA256 = "f6cf302db3066d715a9cf83891973bfe43384d118d29bff10fd25d9f89f306ce"
LLD_SHA256 = "aefdcb18b0de9bd30a5e12310679e95b4fabb243b0f0032b65a14d2a3fe8ed5c"
LIBCXX_SHA256 = "edb85368448ef81b2da7e61a28c78dbaa9530582c824956d691ee9aba10427c8"
LIBCXXABI_SHA256 = "3081ce2f7bbe374c5330330a0df6e1df39a20b0a0eeece88d7021cd014b9b802"
COMPILER_PROBE_SOURCE = b"int main(void) { return 0; }\n"
COMPILER_CONTRACT_DOMAIN = "axeyum-lean-u2-r2-bundled-compiler-v1"
PRIOR_ATTEMPTS_DOMAIN = "axeyum-lean-u2-r2-prior-attempts-v1"
COMPILER_IDENTITIES = {
    "bin/clang": {"bytes": 119_208, "sha256": CLANG_SHA256},
    "bin/ld.lld": {"bytes": 5_271_616, "sha256": LLD_SHA256},
    "lib/libc++.a": {"bytes": 2_351_478, "sha256": LIBCXX_SHA256},
    "lib/libc++abi.a": {"bytes": 696_718, "sha256": LIBCXXABI_SHA256},
}


ORIG_RENDER_WRAPPER = BASE.render_environment_wrapper
ORIG_BUILD_SPEC = BASE.build_spec
ORIG_VALIDATE_SPEC = BASE.validate_spec
ORIG_VALIDATE_REPOSITORY_INPUTS = BASE.validate_repository_inputs
ORIG_FAILED_DEPENDENCY = BASE.failed_attempt_dependency
ORIG_VALIDATE_FAILED_ATTEMPT = BASE.validate_failed_attempt
ORIG_CAPTURE_TOOLCHAIN = BASE.capture_toolchain
ORIG_VALIDATE_TOOLCHAIN = BASE.validate_toolchain_record
ORIG_RUN_M0 = BASE.run_m0
ORIG_BUILD_RESULT = BASE.build_result_authority

_CURRENT_WORK_ROOT: Path | None = None


def _file_identity(root: Path, relative: str, expected_sha256: str) -> dict[str, Any]:
    path = root / relative
    if not path.is_file() or path.is_symlink():
        raise BASE.U2ExecutionError(f"missing regular released-toolchain file: {relative}")
    actual = BASE.sha256_file(path)
    if actual != expected_sha256:
        raise BASE.U2ExecutionError(f"released-toolchain file drift: {relative}")
    return {
        "path": relative,
        "bytes": path.stat().st_size,
        "sha256": actual,
    }


def _expected_file_identity(relative: str) -> dict[str, Any]:
    return {"path": relative, **COMPILER_IDENTITIES[relative]}


def _stream_identity(value: bytes) -> dict[str, Any]:
    return {
        "bytes": len(value),
        "sha256": BASE.sha256_bytes(value),
        "utf8": value.decode("utf-8", errors="strict"),
    }


def capture_compiler_contract(toolchain_root: Path, work_root: Path) -> dict[str, Any]:
    toolchain = toolchain_root.resolve()
    probe = work_root.resolve() / "compiler-probe"
    probe.mkdir(parents=True, mode=0o700)
    source = probe / "probe.c"
    output = probe / "probe.out"
    source.write_bytes(COMPILER_PROBE_SOURCE)
    command = [str(toolchain / "bin/leanc"), "-v", "-o", str(output), str(source)]
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": f"{toolchain / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    if "LEAN_CC" in environment:
        raise BASE.U2ExecutionError("compiler probe environment contains LEAN_CC")
    completed = BASE._run(command, cwd=probe, env=environment, timeout=60)
    if completed.returncode != 0 or not output.is_file() or output.is_symlink():
        raise BASE.U2ExecutionError("released bundled-compiler probe failed")
    stderr_text = completed.stderr.decode("utf-8", errors="strict")
    clang = str(toolchain / "bin/clang")
    linker = str(toolchain / "bin/ld.lld")
    if (
        clang not in stderr_text
        or linker not in stderr_text
        or "/usr/bin/cc" in stderr_text
        or "ld.bfd" in stderr_text
        or f"--sysroot {toolchain}" not in stderr_text
    ):
        raise BASE.U2ExecutionError("verbose leanc probe did not select the bundled toolchain")
    output_bytes = output.read_bytes()
    payload = {
        "domain": COMPILER_CONTRACT_DOMAIN,
        "lean_cc": {"state": "absent", "value": None},
        "command": command,
        "environment": environment,
        "source": {
            "bytes": len(COMPILER_PROBE_SOURCE),
            "sha256": BASE.sha256_bytes(COMPILER_PROBE_SOURCE),
            "utf8": COMPILER_PROBE_SOURCE.decode("utf-8"),
        },
        "terminal": {"class": "exited", "exit_code": completed.returncode},
        "stdout": _stream_identity(completed.stdout),
        "stderr": _stream_identity(completed.stderr),
        "output": {
            "bytes": len(output_bytes),
            "sha256": BASE.sha256_bytes(output_bytes),
            "base64": base64.b64encode(output_bytes).decode("ascii"),
        },
        "selected_compiler": _file_identity(toolchain, "bin/clang", CLANG_SHA256),
        "selected_linker": _file_identity(toolchain, "bin/ld.lld", LLD_SHA256),
        "static_cxx": [
            _file_identity(toolchain, "lib/libc++.a", LIBCXX_SHA256),
            _file_identity(toolchain, "lib/libc++abi.a", LIBCXXABI_SHA256),
        ],
    }
    return payload | {
        "identity_sha256": BASE.domain_digest(COMPILER_CONTRACT_DOMAIN, payload)
    }


def validate_compiler_contract(contract: Any, toolchain_root: Path) -> list[str]:
    if not isinstance(contract, dict):
        return ["missing R2 bundled-compiler contract"]
    failures: list[str] = []
    payload = {key: value for key, value in contract.items() if key != "identity_sha256"}
    if (
        contract.get("identity_sha256")
        != BASE.domain_digest(COMPILER_CONTRACT_DOMAIN, payload)
        or contract.get("domain") != COMPILER_CONTRACT_DOMAIN
        or contract.get("lean_cc") != {"state": "absent", "value": None}
        or contract.get("terminal") != {"class": "exited", "exit_code": 0}
    ):
        failures.append("R2 compiler contract identity or terminal drift")
    root = toolchain_root.resolve()
    expected_environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "PATH": f"{root / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    environment = contract.get("environment", {})
    if environment != expected_environment or "LEAN_CC" in environment:
        failures.append("R2 compiler environment drift or LEAN_CC override")
    command = contract.get("command", [])
    command_paths_valid = False
    if isinstance(command, list) and len(command) == 5:
        output_path = Path(command[3]) if isinstance(command[3], str) else Path()
        source_path = Path(command[4]) if isinstance(command[4], str) else Path()
        command_paths_valid = (
            command[1:3] == ["-v", "-o"]
            and output_path.is_absolute()
            and source_path.is_absolute()
            and output_path.name == "probe.out"
            and source_path.name == "probe.c"
            and output_path.parent == source_path.parent
        )
    if (
        not isinstance(command, list)
        or len(command) != 5
        or command[0] != str(root / "bin/leanc")
        or not command_paths_valid
    ):
        failures.append("R2 verbose leanc probe command drift")
    source = contract.get("source")
    expected_source = {
        "bytes": len(COMPILER_PROBE_SOURCE),
        "sha256": BASE.sha256_bytes(COMPILER_PROBE_SOURCE),
        "utf8": COMPILER_PROBE_SOURCE.decode("utf-8"),
    }
    if source != expected_source:
        failures.append("R2 compiler probe source drift")
    for field in ("stdout", "stderr"):
        stream = contract.get(field, {})
        text = stream.get("utf8") if isinstance(stream, dict) else None
        if (
            not isinstance(text, str)
            or stream.get("bytes") != len(text.encode("utf-8"))
            or stream.get("sha256") != BASE.sha256_bytes(text.encode("utf-8"))
        ):
            failures.append(f"R2 compiler {field} evidence drift")
    stderr = contract.get("stderr", {}).get("utf8", "")
    if (
        str(root / "bin/clang") not in stderr
        or str(root / "bin/ld.lld") not in stderr
        or "/usr/bin/cc" in stderr
        or "ld.bfd" in stderr
        or f"--sysroot {root}" not in stderr
    ):
        failures.append("R2 compiler selection evidence drift")
    output = contract.get("output", {})
    try:
        output_bytes = base64.b64decode(output.get("base64", ""), validate=True)
    except (ValueError, TypeError):
        output_bytes = b""
        failures.append("R2 compiler output base64 is invalid")
    if (
        output.get("bytes") != len(output_bytes)
        or output.get("sha256") != BASE.sha256_bytes(output_bytes)
        or not output_bytes.startswith(b"\x7fELF")
    ):
        failures.append("R2 compiler output identity drift")
    expected_files = (
        ("selected_compiler", "bin/clang"),
        ("selected_linker", "bin/ld.lld"),
    )
    for field, relative in expected_files:
        if contract.get(field) != _expected_file_identity(relative):
            failures.append(f"R2 {field} identity drift")
    expected_cxx = [
        _expected_file_identity("lib/libc++.a"),
        _expected_file_identity("lib/libc++abi.a"),
    ]
    if contract.get("static_cxx") != expected_cxx:
        failures.append("R2 static C++ archive identity drift")
    return failures


def capture_toolchain(toolchain_root: Path) -> dict[str, Any]:
    if _CURRENT_WORK_ROOT is None:
        raise BASE.U2ExecutionError("R2 compiler probe work root is not configured")
    record = ORIG_CAPTURE_TOOLCHAIN(toolchain_root)
    record["bundled_compiler_contract"] = capture_compiler_contract(
        toolchain_root, _CURRENT_WORK_ROOT
    )
    return BASE.seal(record, BASE.TOOLCHAIN_SCHEMA)


def validate_toolchain_record(record: Any) -> list[str]:
    failures = ORIG_VALIDATE_TOOLCHAIN(record)
    if isinstance(record, dict) and isinstance(record.get("root"), str):
        failures.extend(
            validate_compiler_contract(
                record.get("bundled_compiler_contract"), Path(record["root"])
            )
        )
    else:
        failures.append("R2 toolchain root is missing")
    return failures


def render_environment_wrapper(source_root: Path, toolchain_root: Path) -> bytes:
    original = ORIG_RENDER_WRAPPER(source_root, toolchain_root)
    marker = b"export LEAN_CC=/usr/bin/cc "
    if original.count(marker) != 1:
        raise BASE.U2ExecutionError("R1 wrapper LEAN_CC marker drift")
    result = original.replace(marker, b"export ", 1)
    if b"LEAN_CC" in result:
        raise BASE.U2ExecutionError("R2 wrapper still contains LEAN_CC")
    return result


def r1_attempt_dependency(
    *, live_readonly_validated: bool, git_index_validated: bool
) -> dict[str, Any]:
    return {
        "path": R1_EVIDENCE_ROOT.relative_to(ROOT).as_posix(),
        "implementation_revision": "1a2e7d3aa59710ba4c5dce7fe7f90f86db4841e4",
        "attempt_id": "attempt-002",
        "files": R1_EVIDENCE_FILE_COUNT,
        "bytes": R1_EVIDENCE_BYTES,
        "manifest_domain": R1_EVIDENCE_MANIFEST_DOMAIN,
        "manifest_sha256": R1_EVIDENCE_MANIFEST_SHA256,
        "terminal_sha256": R1_TERMINAL_SHA256,
        "junit_sha256": R1_JUNIT_SHA256,
        "completion_sha256": R1_COMPLETION_SHA256,
        "outcome": "failed",
        "official_outcomes": 1,
        "official_passes": 0,
        "official_failures": 1,
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


def validate_r1_attempt(
    *, require_live_readonly: bool, require_git_index: bool
) -> dict[str, Any]:
    if not R1_EVIDENCE_ROOT.is_dir() or R1_EVIDENCE_ROOT.is_symlink():
        raise BASE.U2ExecutionError("R1 evidence root drift")
    inventory: list[dict[str, Any]] = []
    for path in sorted(R1_EVIDENCE_ROOT.rglob("*")):
        relative = path.relative_to(R1_EVIDENCE_ROOT).as_posix()
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise BASE.U2ExecutionError(f"symlinked R1 evidence: {relative}")
        if stat.S_ISREG(info.st_mode):
            if require_live_readonly and stat.S_IMODE(info.st_mode) != 0o444:
                raise BASE.U2ExecutionError(f"live R1 evidence is not mode 0444: {relative}")
            inventory.append(BASE.file_record(relative, path))
        elif not stat.S_ISDIR(info.st_mode):
            raise BASE.U2ExecutionError(f"non-regular R1 evidence: {relative}")
    if (
        len(inventory) != R1_EVIDENCE_FILE_COUNT
        or sum(row["bytes"] for row in inventory) != R1_EVIDENCE_BYTES
        or BASE.domain_digest(R1_EVIDENCE_MANIFEST_DOMAIN, inventory)
        != R1_EVIDENCE_MANIFEST_SHA256
    ):
        raise BASE.U2ExecutionError("R1 evidence manifest drift")
    for name, expected in (
        ("terminal.json", R1_TERMINAL_SHA256),
        ("junit.json", R1_JUNIT_SHA256),
        ("completion.json", R1_COMPLETION_SHA256),
    ):
        if BASE.load_canonical(R1_EVIDENCE_ROOT / name).get("record_sha256") != expected:
            raise BASE.U2ExecutionError(f"R1 {name} identity drift")
    if require_git_index:
        BASE._validate_git_regular_modes(
            R1_EVIDENCE_ROOT, [row["path"] for row in inventory]
        )
    if BASE.sha256_file(R1_AUTHORITY) != R1_AUTHORITY_BYTES_SHA256:
        raise BASE.U2ExecutionError("R1 authority physical bytes drift")
    authority = BASE.load_json(R1_AUTHORITY)
    if (
        not BASE.valid_seal(authority, BASE.RESULT_SCHEMA)
        or authority.get("record_sha256") != R1_AUTHORITY_RECORD_SHA256
        or authority.get("case", {}).get("outcome") != "failed"
        or authority.get("summary", {}).get("official_outcomes") != 1
        or authority.get("credits", {}).get("parity_credit") != 0
    ):
        raise BASE.U2ExecutionError("R1 authority claim or seal drift")
    return r1_attempt_dependency(
        live_readonly_validated=require_live_readonly,
        git_index_validated=require_git_index,
    )


def failed_attempt_dependency(
    *, live_readonly_validated: bool, git_index_validated: bool
) -> dict[str, Any]:
    attempts = [
        ORIG_FAILED_DEPENDENCY(
            live_readonly_validated=live_readonly_validated,
            git_index_validated=git_index_validated,
        ),
        r1_attempt_dependency(
            live_readonly_validated=live_readonly_validated,
            git_index_validated=git_index_validated,
        ),
    ]
    payload = {
        "attempts": attempts,
        "process_attempts": 2,
        "official_outcomes": 1,
        "official_passes": 0,
        "official_failures": 1,
        "parity_credit": 0,
    }
    return payload | {
        "identity_sha256": BASE.domain_digest(PRIOR_ATTEMPTS_DOMAIN, payload)
    }


def validate_failed_attempt(
    root: Path = BASE.FAILED_EVIDENCE_ROOT,
    *,
    require_live_readonly: bool,
    require_git_index: bool,
) -> dict[str, Any]:
    if root != BASE.FAILED_EVIDENCE_ROOT:
        raise BASE.U2ExecutionError("R2 prior-attempt root substitution")
    ORIG_VALIDATE_FAILED_ATTEMPT(
        root,
        require_live_readonly=require_live_readonly,
        require_git_index=require_git_index,
    )
    validate_r1_attempt(
        require_live_readonly=require_live_readonly,
        require_git_index=require_git_index,
    )
    return failed_attempt_dependency(
        live_readonly_validated=require_live_readonly,
        git_index_validated=require_git_index,
    )


def validate_repository_inputs() -> list[str]:
    failures = ORIG_VALIDATE_REPOSITORY_INPUTS()
    if not R2_PLAN.is_file() or BASE.sha256_file(R2_PLAN) != R2_PLAN_SHA256:
        failures.append("R2 preregistration plan drift")
    if not R1_AUTHORITY.is_file() or BASE.sha256_file(R1_AUTHORITY) != R1_AUTHORITY_BYTES_SHA256:
        failures.append("R1 result authority drift")
    return failures


def build_spec(**kwargs: Any) -> dict[str, Any]:
    spec = ORIG_BUILD_SPEC(**kwargs)
    spec |= {
        "r2_preregistration_commit": R2_PREREGISTRATION_COMMIT,
        "r2_plan_sha256": R2_PLAN_SHA256,
        "r1_authority_bytes_sha256": R1_AUTHORITY_BYTES_SHA256,
        "r1_authority_record_sha256": R1_AUTHORITY_RECORD_SHA256,
        "prior_attempts_sha256": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )["identity_sha256"],
    }
    return BASE.seal(spec, BASE.SPEC_SCHEMA)


def validate_spec(spec: Any) -> list[str]:
    if not BASE.valid_seal(spec, BASE.SPEC_SCHEMA):
        return ["R2 spec identity drift"]
    failures: list[str] = []
    expected = {
        "r2_preregistration_commit": R2_PREREGISTRATION_COMMIT,
        "r2_plan_sha256": R2_PLAN_SHA256,
        "r1_authority_bytes_sha256": R1_AUTHORITY_BYTES_SHA256,
        "r1_authority_record_sha256": R1_AUTHORITY_RECORD_SHA256,
        "prior_attempts_sha256": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        )["identity_sha256"],
    }
    if any(spec.get(key) != value for key, value in expected.items()):
        failures.append("R2 preregistration or prior-attempt identity drift")
    if "LEAN_CC" in spec.get("environment", {}):
        failures.append("R2 spec environment contains LEAN_CC")
    probe = copy.deepcopy(spec)
    for key in expected:
        probe.pop(key, None)
    probe = BASE.seal(probe, BASE.SPEC_SCHEMA)
    failures.extend(ORIG_VALIDATE_SPEC(probe))
    return failures


@contextmanager
def base_r2_configuration() -> Iterator[None]:
    replacements = {
        "LANE_ID": LANE_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "render_environment_wrapper": render_environment_wrapper,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "validate_repository_inputs": validate_repository_inputs,
        "failed_attempt_dependency": failed_attempt_dependency,
        "validate_failed_attempt": validate_failed_attempt,
        "capture_toolchain": capture_toolchain,
        "validate_toolchain_record": validate_toolchain_record,
    }
    original = {name: getattr(BASE, name) for name in replacements}
    for name, value in replacements.items():
        setattr(BASE, name, value)
    try:
        yield
    finally:
        for name, value in original.items():
            setattr(BASE, name, value)


def validate_evidence_root(
    root: Path, *, require_live_readonly: bool = False
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    with base_r2_configuration():
        return BASE.validate_evidence_root(
            root, require_live_readonly=require_live_readonly
        )


def aggregate_credits(outcome: str) -> dict[str, int]:
    credits = BASE.case_credits(outcome)
    credits["official_cases"] = 1
    credits["official_outcomes"] = 2
    credits["official_passes"] = int(outcome == "passed")
    credits["official_failures"] = 1 + int(outcome == "failed")
    return credits


def build_result_authority(root: Path, *, implementation_revision: str) -> dict[str, Any]:
    with base_r2_configuration():
        authority = ORIG_BUILD_RESULT(root, implementation_revision=implementation_revision)
    case = authority["case"]
    outcome = case["outcome"]
    current = authority["attempts"][1]
    r2_sources = [
        {"path": R2_PLAN.relative_to(ROOT).as_posix(), "sha256": BASE.sha256_file(R2_PLAN)},
        {"path": R1_AUTHORITY.relative_to(ROOT).as_posix(), "sha256": BASE.sha256_file(R1_AUTHORITY)},
        {
            "path": Path(__file__).resolve().relative_to(ROOT).as_posix(),
            "sha256": BASE.sha256_file(Path(__file__).resolve()),
        },
        {
            "path": "scripts/tests/test_lean_u2_official_execution_r2.py",
            "sha256": BASE.sha256_file(
                ROOT / "scripts/tests/test_lean_u2_official_execution_r2.py"
            ),
        },
    ]
    source_by_path = {row["path"]: row for row in authority["source_inputs"]}
    source_by_path.update({row["path"]: row for row in r2_sources})
    credits = aggregate_credits(outcome)
    authority |= {
        "schema": RESULT_SCHEMA,
        "status": "complete-local-official-case-history",
        "r2_preregistration_commit": R2_PREREGISTRATION_COMMIT,
        "r2_plan_sha256": R2_PLAN_SHA256,
        "r1_authority_bytes_sha256": R1_AUTHORITY_BYTES_SHA256,
        "r1_authority_record_sha256": R1_AUTHORITY_RECORD_SHA256,
        "source_inputs": [source_by_path[path] for path in sorted(source_by_path)],
        "failed_attempt": failed_attempt_dependency(
            live_readonly_validated=True, git_index_validated=True
        ),
        "attempts": [
            {
                "id": "attempt-001",
                "sequence": 1,
                "status": "incomplete-process-failure",
                "terminal_sha256": BASE.FAILED_TERMINAL_SHA256,
                "junit_sha256": BASE.FAILED_JUNIT_SHA256,
                "evidence_manifest_sha256": BASE.FAILED_EVIDENCE_MANIFEST_SHA256,
                "official_outcomes": 0,
                "parity_credit": 0,
            },
            {
                "id": "attempt-002",
                "sequence": 2,
                "status": "complete-local-official-case-outcome",
                "outcome": "failed",
                "terminal_sha256": R1_TERMINAL_SHA256,
                "junit_sha256": R1_JUNIT_SHA256,
                "completion_sha256": R1_COMPLETION_SHA256,
                "evidence_manifest_sha256": R1_EVIDENCE_MANIFEST_SHA256,
                "official_outcomes": 1,
                "parity_credit": 0,
            },
            current | {"outcome": outcome},
        ],
        "summary": authority["summary"]
        | {
            "process_attempts": 3,
            "incomplete_process_attempts": 1,
            "completed_process_attempts": 2,
            "official_outcomes": 2,
            "official_passes": credits["official_passes"],
            "official_failures": credits["official_failures"],
        },
        "credits": credits,
        "record_sha256": "",
    }
    return BASE.seal(authority, RESULT_SCHEMA)


def validate_result_authority(authority: Any) -> list[str]:
    if not BASE.valid_seal(authority, RESULT_SCHEMA):
        return ["R2 result authority identity drift"]
    failures: list[str] = []
    if (
        authority.get("status") != "complete-local-official-case-history"
        or authority.get("r2_preregistration_commit") != R2_PREREGISTRATION_COMMIT
        or authority.get("r2_plan_sha256") != R2_PLAN_SHA256
        or authority.get("r1_authority_bytes_sha256") != R1_AUTHORITY_BYTES_SHA256
        or authority.get("r1_authority_record_sha256") != R1_AUTHORITY_RECORD_SHA256
        or not BASE.HEX40.fullmatch(authority.get("implementation_revision", ""))
    ):
        failures.append("R2 result preregistration or implementation drift")
    attempts = authority.get("attempts", [])
    if (
        not isinstance(attempts, list)
        or len(attempts) != 3
        or [row.get("id") for row in attempts if isinstance(row, dict)]
        != ["attempt-001", "attempt-002", ATTEMPT_ID]
        or [row.get("sequence") for row in attempts if isinstance(row, dict)]
        != [1, 2, SEQUENCE]
        or attempts[0].get("official_outcomes") != 0
        or attempts[1].get("outcome") != "failed"
        or attempts[1].get("official_outcomes") != 1
        or attempts[2].get("outcome") not in {"passed", "failed"}
        or attempts[2].get("official_outcomes") != 1
    ):
        failures.append("R2 result attempt history drift")
    case = authority.get("case", {})
    outcome = case.get("outcome")
    if outcome not in {"passed", "failed"} or authority.get("credits") != aggregate_credits(outcome):
        failures.append("R2 result case or aggregate credit drift")
    summary = authority.get("summary", {})
    if (
        summary.get("process_attempts") != 3
        or summary.get("incomplete_process_attempts") != 1
        or summary.get("completed_process_attempts") != 2
        or summary.get("official_outcomes") != 2
        or summary.get("official_passes") != int(outcome == "passed")
        or summary.get("official_failures") != 1 + int(outcome == "failed")
        or summary.get("parent_profiles_completed") != 0
        or summary.get("axeyum_outcomes") != 0
        or summary.get("paired_cells") != 0
        or summary.get("performance_rows") != 0
    ):
        failures.append("R2 result summary drift")
    if authority.get("failed_attempt") != failed_attempt_dependency(
        live_readonly_validated=True, git_index_validated=True
    ):
        failures.append("R2 result prior-attempt dependency drift")
    evidence = authority.get("evidence_files")
    if (
        not isinstance(evidence, list)
        or authority.get("evidence_manifest_sha256")
        != BASE.domain_digest(
            "axeyum-lean-u2-official-execution-evidence-files-v1", evidence
        )
    ):
        failures.append("R2 result evidence manifest drift")
    claims = authority.get("claims", {})
    if (
        claims.get("parent_profile_complete") is not False
        or claims.get("official_provider_reproduced") is not False
        or claims.get("axeyum_observed") is not False
        or claims.get("matched_pair_formed") is not False
        or claims.get("performance_measured") is not False
        or claims.get("lean_parity_established") is not False
    ):
        failures.append("R2 result claim boundary drift")
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
    summary = authority["summary"]
    evidence_bytes = sum(row["bytes"] for row in authority["evidence_files"])
    return f"""# TL0.6.3 M0 R2 official Lean execution summary

Generated from [`lean-u2-official-execution-tl0.6.3-m0-r2-v1.json`](../lean-u2-official-execution-tl0.6.3-m0-r2-v1.json).

- Status: **complete local official-case history**
- Implementation revision: `{authority['implementation_revision']}`
- Attempt 002 retained outcome: **failed**
- Attempt 003 outcome: **{case['outcome']}**
- Process attempts / decided official outcomes: **3 / {summary['official_outcomes']}**
- Official passes / failures: **{summary['official_passes']} / {summary['official_failures']}**
- Parent selection coverage: **1 / {BASE.PARENT_SELECTED_COUNT:,}** unique cases
- Attempt-003 evidence: **{len(authority['evidence_files'])} files / {evidence_bytes:,} bytes**
- Parent/provider completions, Axeyum outcomes, pairs, performance rows: **0**
- Complete populations / axes / gates / Lean parity credit: **0 / 0 / 0 / 0**

The history preserves R1's failed local outcome and R2's result separately. It
does not complete the parent profile, reproduce an official provider, observe
Axeyum, form a matched semantic pair, measure performance, or establish Lean
4 parity.
"""


def generate_result(*, root: Path, implementation_revision: str | None, check: bool) -> None:
    if check:
        if not RESULT_AUTHORITY.is_file():
            raise BASE.U2ExecutionError("missing committed R2 result authority")
        authority = BASE.load_json(RESULT_AUTHORITY)
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
        rebuilt = build_result_authority(
            root, implementation_revision=authority["implementation_revision"]
        )
        if rebuilt != authority:
            raise BASE.U2ExecutionError("committed R2 result authority is stale")
    else:
        if implementation_revision is None:
            raise BASE.U2ExecutionError("R2 result generation requires implementation revision")
        authority = build_result_authority(root, implementation_revision=implementation_revision)
        failures = validate_result_authority(authority)
        if failures:
            raise BASE.U2ExecutionError("; ".join(failures))
    outputs = {
        RESULT_AUTHORITY: json.dumps(authority, indent=2) + "\n",
        RESULT_JSON: json.dumps(result_summary(authority), indent=2) + "\n",
        RESULT_MARKDOWN: render_markdown(authority),
    }
    if check:
        stale = [
            path
            for path, content in outputs.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != content
        ]
        if stale:
            raise BASE.U2ExecutionError("stale R2 generated result")
    else:
        for path, content in outputs.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    print(
        f"LEAN_U2_OFFICIAL_R2_RESULT|case={BASE.CASE_ID}|"
        f"outcome={authority['case']['outcome']}|official_outcomes=2|"
        "parent_complete=false|axeyum=0|pairs=0|parity_credit=0"
    )


def run_m0(args: argparse.Namespace) -> None:
    global _CURRENT_WORK_ROOT
    _CURRENT_WORK_ROOT = args.work_root
    try:
        with base_r2_configuration():
            ORIG_RUN_M0(args)
    finally:
        _CURRENT_WORK_ROOT = None


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
                f"LEAN_U2_OFFICIAL_R2_EVIDENCE_VALID|case={BASE.CASE_ID}|"
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
    except (BASE.U2ExecutionError, BASE.STORE.CheckpointConflict, BASE.STORE.StoreEvidenceError) as exc:
        print(f"LEAN_U2_OFFICIAL_R2_ERROR|{exc}", file=BASE.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
