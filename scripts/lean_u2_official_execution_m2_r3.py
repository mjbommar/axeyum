#!/usr/bin/env python3
"""Run and validate the source-first M2 R3 attempt-002 contract.

Offline validation and the direct-runtime stack probe do not construct the
selected CTest harness.  ``run-r3`` is the only selected-execution surface.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Callable, Iterator

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402
from scripts import lean_u2_official_execution_m2_r2 as R2_DIAGNOSTIC  # noqa: E402
from scripts import lean_u2_official_execution_m2_run as OLD_RUN  # noqa: E402
from scripts import lean_u2_official_execution_m2_store as OLD_STORE  # noqa: E402
from scripts import lean_u2_official_execution_r2 as TOOLCHAIN  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r3-"
    "attempt-002-plan-2026-07-23.md"
)
PREREGISTRATION_COMMIT = "ec64a52370a38c7b127ffe66160ab9cedd7d2b5f"
PLAN_SHA256 = "c2aea0d4ae6c6affeed5a7d865f6e466bbb795efaa17361d3e5349d3c04ce961"

R1_AUTHORITY_SHA256 = R2_DIAGNOSTIC.R1_AUTHORITY_SHA256
R1_AUTHORITY_RECORD = R2_DIAGNOSTIC.R1_AUTHORITY_RECORD
R2_POST_RECORD = "46494553ed39e06359b195be398205d330cb047623bf6f16fa028825ec69bd66"
R2_COMPLETION_RECORD = (
    "5ef1040a692a7a72650868909f7477beddf770093e86e2162bec5ff3745d459b"
)

RUN_ID = "tl0.6.3-m2-release-linux-shard-0001-v2"
ATTEMPT_ID = "attempt-002"
SEQUENCE = 2
LANE_ID = "official-ctest-local-8g-lean-j1-stack512m-shard64-v2"
STACK_SIZE_KB = 524_288
STACK_SIZE_BYTES = STACK_SIZE_KB * 1024
STACK_ENV = "LEAN_STACK_SIZE_KB"

DEFAULT_SOURCE_REPO = ROOT / "references/lean4"
DEFAULT_TOOLCHAIN_ROOT = Path(
    "/home/mjbommar/.cache/axeyum-lean-gate-v430-audit/elan-home/"
    "toolchains/leanprover--lean4---v4.30.0"
)
DEFAULT_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/"
    "lean-u2-official-execution-tl0.6.3-m2-shard-0001-r3-attempt-002"
)
WORK_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r3-"

COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-m2-r3-completion-v1"
RECORD_SET_DOMAIN = "axeyum-lean-u2-official-execution-m2-r3-record-set-v1"
FULL_DOMAIN = "axeyum-lean-u2-official-execution-m2-r3-generated-files-v1"
RETAINED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r3-retained-files-v1"
METADATA_DOMAIN = "axeyum-lean-u2-official-execution-m2-r3-metadata-files-v1"
ALLOWED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r3-allowed-paths-v1"
PROBE_SOURCE = b'''def main : IO Unit := do\n  let value <- IO.getEnv "LEAN_STACK_SIZE_KB"\n  IO.println (value.getD "missing")\n'''

ORIG_BUILD_SPEC = M2.build_spec
ORIG_VALIDATE_SPEC = M2.validate_spec
ORIG_RENDER_WRAPPER = M2.render_environment_wrapper
ORIG_BUILD_HARNESS = M2.build_harness_record
ORIG_RESOURCE_ENVELOPE = M2.resource_envelope
ORIG_CASE_PATHS = M2.case_generated_paths
ORIG_DECLARED_PATHS = M2.declared_generated_paths
ORIG_BUILD_POST = M2.build_post_record
ORIG_RESULT_PROJECTION = M2.result_projection


class R3Error(ValueError):
    """The R3 preregistration, execution, or evidence closure drifted."""


def validate_history() -> dict[str, Any]:
    if (
        not M2.HEX40.fullmatch(PREREGISTRATION_COMMIT)
        or not PLAN.is_file()
        or BASE.sha256_file(PLAN) != PLAN_SHA256
    ):
        raise R3Error("R3 preregistration identity drift")
    completion = R2_DIAGNOSTIC.validate_completed(R2_DIAGNOSTIC.EVIDENCE_ROOT)
    post = BASE.load_canonical(
        R2_DIAGNOSTIC.EVIDENCE_ROOT / "diagnostic/post.json"
    )
    if (
        post.get("r1_authority_sha256") != R1_AUTHORITY_SHA256
        or post.get("r1_authority_record_sha256") != R1_AUTHORITY_RECORD
        or post.get("record_sha256") != R2_POST_RECORD
        or completion.get("record_sha256") != R2_COMPLETION_RECORD
        or post.get("process_attempts_added") != 0
        or completion.get("official_outcomes") != 0
    ):
        raise R3Error("R1/R2 immutable history drift")
    return {"post": post, "completion": completion}


def resource_envelope() -> dict[str, Any]:
    envelope = dict(ORIG_RESOURCE_ENVELOPE())
    envelope.update(
        {
            "lane_id": LANE_ID,
            "task_stack_limit": BASE.metric(
                "requested", STACK_SIZE_BYTES, "bytes"
            ),
            "task_stack_policy": "universal-LEAN_STACK_SIZE_KB-environment",
            "task_stack_enforcement": STACK_ENV,
        }
    )
    return envelope


def build_spec(
    *,
    implementation_revision: str,
    source_root: Path,
    toolchain_root: Path,
    harness_build: Path,
    junit_path: Path,
) -> dict[str, Any]:
    if not M2.HEX40.fullmatch(implementation_revision):
        raise R3Error("R3 implementation revision must be a full Git hash")
    contract = M2.selected_contract()
    source = source_root.resolve()
    toolchain = toolchain_root.resolve()
    harness = harness_build.resolve()
    junit = junit_path.resolve()
    environment = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "LEAN_NUM_THREADS": "1",
        STACK_ENV: str(STACK_SIZE_KB),
        "PATH": f"{toolchain / 'bin'}:/usr/bin:/bin",
        "TZ": "UTC",
    }
    return BASE.seal(
        {
            "schema": M2.SPEC_SCHEMA,
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "implementation_revision": implementation_revision,
            "target_commit": M2.LEAN_COMMIT,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "shard_id": M2.SHARD_ID,
            "shard_sha256": M2.SHARD_SHA256,
            "shard_case_ids_sha256": M2.SHARD_CASE_IDS_SHA256,
            "prior_history": {
                "r1_authority_sha256": R1_AUTHORITY_SHA256,
                "r1_authority_record_sha256": R1_AUTHORITY_RECORD,
                "r2_post_record_sha256": R2_POST_RECORD,
                "r2_completion_record_sha256": R2_COMPLETION_RECORD,
                "credited_outcomes": 0,
            },
            "parent": {
                "context_id": M2.PARENT_CONTEXT_ID,
                "context_sha256": M2.PARENT_CONTEXT_SHA256,
                "cell_id": M2.PARENT_CELL_ID,
                "cell_sha256": M2.PARENT_CELL_SHA256,
                "attempt_id": M2.PARENT_ATTEMPT_ID,
                "attempt_sha256": M2.PARENT_ATTEMPT_SHA256,
                "selection_id": M2.PARENT_SELECTION_ID,
                "selection_sha256": M2.PARENT_SELECTION_SHA256,
                "selected_count": M2.PARENT_SELECTED_COUNT,
                "completed": False,
            },
            "case_refs": [
                {"id": row["id"], "registration_sha256": row["sha256"]}
                for row in contract["cases"]
            ],
            "source_root": str(source),
            "toolchain_root": str(toolchain),
            "harness_build": str(harness),
            "junit_path": str(junit),
            "command": [
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
            ],
            "working_directory": str(source),
            "environment": environment,
            "forbidden_environment_keys": ["LEAN_CC", "PYTHONPATH", "TEST_BENCH"],
            "resource_envelope": resource_envelope(),
            "credit_class": "local-official-shard-outcomes-only",
            "record_sha256": "",
        },
        M2.SPEC_SCHEMA,
    )


def validate_spec(spec: Any) -> list[str]:
    if not isinstance(spec, dict) or not BASE.valid_seal(spec, M2.SPEC_SCHEMA):
        return ["R3 spec identity drift"]
    try:
        expected = build_spec(
            implementation_revision=spec["implementation_revision"],
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_build=Path(spec["harness_build"]),
            junit_path=Path(spec["junit_path"]),
        )
    except (KeyError, TypeError, R3Error) as error:
        return [f"R3 spec cannot be reconstructed: {error}"]
    failures = [] if spec == expected else ["R3 spec field or linkage drift"]
    environment = spec.get("environment", {})
    if environment.get(STACK_ENV) != str(STACK_SIZE_KB):
        failures.append("R3 universal stack environment drift")
    if any(key in environment for key in spec.get("forbidden_environment_keys", [])):
        failures.append("R3 spec contains a forbidden environment override")
    return failures


def render_environment_wrapper(source_root: Path, toolchain_root: Path) -> bytes:
    wrapper = TOOLCHAIN.render_environment_wrapper(source_root, toolchain_root)
    needle = b"TEST_LEANI_ARGS=(-j1)\n"
    if wrapper.count(needle) != 1:
        raise R3Error("R3 wrapper worker-array anchor drift")
    wrapper = wrapper.replace(
        needle, needle + f"export {STACK_ENV}={STACK_SIZE_KB}\n".encode(), 1
    )
    export = f"export {STACK_ENV}={STACK_SIZE_KB}\n".encode()
    validate_environment_wrapper(wrapper)
    return wrapper


def validate_environment_wrapper(wrapper: bytes) -> None:
    if not isinstance(wrapper, bytes):
        raise R3Error("R3 wrapper is not bytes")
    export = f"export {STACK_ENV}={STACK_SIZE_KB}\n".encode()
    stack_lines = [
        line for line in wrapper.splitlines() if STACK_ENV.encode() in line
    ]
    if (
        wrapper.count(export) != 1
        or stack_lines != [export.rstrip(b"\n")]
        or wrapper.count(b"TEST_LEAN_ARGS=(-j1)") != 1
        or wrapper.count(b"TEST_LEANI_ARGS=(-j1)") != 1
        or any(item in wrapper for item in (b"LEAN_CC", b"TEST_BENCH", b"PYTHONPATH"))
    ):
        raise R3Error("R3 wrapper stack, worker, or forbidden override drift")


def build_harness_record(
    *,
    source_root: Path,
    toolchain_root: Path,
    harness_root: Path,
    discovery_payload: dict[str, Any],
) -> dict[str, Any]:
    wrapper = render_environment_wrapper(source_root, toolchain_root)
    ctest = M2.render_ctest_file(
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    )
    discovery = M2.normalize_discovery(
        discovery_payload,
        source_root=source_root,
        toolchain_root=toolchain_root,
        harness_root=harness_root,
    )
    return BASE.seal(
        {
            "schema": M2.HARNESS_SCHEMA,
            "shard_id": M2.SHARD_ID,
            "case_count": M2.SHARD_CASE_COUNT,
            "case_ids_sha256": M2.SHARD_CASE_IDS_SHA256,
            "wrapper": {
                "bytes": len(wrapper),
                "sha256": BASE.sha256_bytes(wrapper),
                "mode": 0o755,
            },
            "ctest_file": {"bytes": len(ctest), "sha256": BASE.sha256_bytes(ctest)},
            "discovery": discovery,
            "discovery_sha256": BASE.domain_digest(
                "axeyum-lean-u2-official-execution-m2-discovery-v1", discovery
            ),
            "record_sha256": "",
        },
        M2.HARNESS_SCHEMA,
    )


def case_generated_paths(case: dict[str, Any]) -> list[str]:
    return R2_DIAGNOSTIC.case_generated_paths(case)


def declared_generated_paths() -> list[str]:
    paths = {"tests/with_stage1_test_env.sh", *BASE.CTEST_SOURCE_PATHS}
    for case in M2.selected_contract()["cases"]:
        paths.update(case_generated_paths(case))
    return sorted(paths)


def _split_generated(
    generated_files: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    failures = BASE._validate_manifest_rows(generated_files, "R3 generated artifact")
    if failures:
        raise R3Error("; ".join(failures))
    if [row["path"] for row in generated_files] != declared_generated_paths():
        raise R3Error("R3 generated path closure drift")
    if any(row["kind"] != "file" or row["target"] is not None for row in generated_files):
        raise R3Error("R3 generated artifact identity is malformed")
    retained = [
        row
        for row in generated_files
        if row["path"].endswith(".out.produced")
        or row["path"].startswith("build/release/Testing/Temporary/")
    ]
    metadata = [
        row
        for row in generated_files
        if row["path"].endswith(".c") or row["path"].endswith(".out")
    ]
    wrapper = [
        row for row in generated_files if row["path"] == "tests/with_stage1_test_env.sh"
    ]
    if (len(generated_files), len(retained), len(metadata), len(wrapper)) != (124, 67, 56, 1):
        raise R3Error("R3 generated assurance split count drift")
    return retained, metadata, wrapper


def build_post_record(
    *,
    original_files: list[dict[str, Any]],
    generated_files: list[dict[str, Any]],
    junit: dict[str, Any],
) -> dict[str, Any]:
    failures = BASE._validate_manifest_rows(original_files, "R3 original source")
    failures.extend(M2.validate_junit_projection(junit))
    if failures:
        raise R3Error("; ".join(failures))
    retained, metadata, wrapper = _split_generated(generated_files)
    retained_with_paths = [
        row | {"evidence_path": OLD_STORE.generated_path(row["path"])}
        for row in retained
    ]
    return BASE.seal(
        {
            "schema": M2.POST_SCHEMA,
            "original_files_sha256": BASE.domain_digest(
                "axeyum-lean-u2-source-files-v1", original_files
            ),
            "original_file_count": len(original_files),
            "original_files_unchanged": True,
            "generated_files": generated_files,
            "generated_files_sha256": BASE.domain_digest(FULL_DOMAIN, generated_files),
            "retained_generated": retained_with_paths,
            "retained_generated_sha256": BASE.domain_digest(RETAINED_DOMAIN, retained),
            "manifest_only_generated": metadata,
            "manifest_only_generated_sha256": BASE.domain_digest(METADATA_DOMAIN, metadata),
            "existing_wrapper": wrapper,
            "allowed_paths_sha256": BASE.domain_digest(
                ALLOWED_DOMAIN, declared_generated_paths()
            ),
            "undeclared_paths": [],
            "junit_sha256": junit["record_sha256"],
            "assurance": {
                "retained_payload_count": 67,
                "metadata_only_count": 56,
                "wrapper_retained_as_harness_artifact": True,
                "metadata_only_independently_replayable": False,
            },
            "record_sha256": "",
        },
        M2.POST_SCHEMA,
    )


def result_projection(junit: dict[str, Any], post: dict[str, Any]) -> dict[str, Any]:
    failures = M2.validate_junit_projection(junit)
    if failures:
        raise R3Error("; ".join(failures))
    if (
        not BASE.valid_seal(post, M2.POST_SCHEMA)
        or post.get("junit_sha256") != junit["record_sha256"]
        or post.get("original_files_unchanged") is not True
        or post.get("undeclared_paths") != []
        or post.get("assurance", {}).get("retained_payload_count") != 67
        or post.get("assurance", {}).get("metadata_only_count") != 56
    ):
        raise R3Error("R3 post-run projection identity or linkage drift")
    summary = junit["summary"]
    credits = {
        "official_cases": M2.SHARD_CASE_COUNT,
        "official_outcomes": M2.SHARD_CASE_COUNT,
        "official_passes": summary["official_passes"],
        "official_failures": summary["official_failures"],
        "unique_new_official_cases": M2.SHARD_CASE_COUNT,
        "local_physical_shards_completed": 1,
        **M2.ZERO_TERMINAL_CREDITS,
    }
    return BASE.seal(
        {
            "schema": M2.PROJECTION_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "shard_id": M2.SHARD_ID,
            "shard_complete": True,
            "parent_selection_id": M2.PARENT_SELECTION_ID,
            "parent_selected_count": M2.PARENT_SELECTED_COUNT,
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
        M2.PROJECTION_SCHEMA,
    )


@contextmanager
def r3_bindings() -> Iterator[None]:
    bindings = {
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "resource_envelope": resource_envelope,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "render_environment_wrapper": render_environment_wrapper,
        "build_harness_record": build_harness_record,
        "case_generated_paths": case_generated_paths,
        "declared_generated_paths": declared_generated_paths,
        "build_post_record": build_post_record,
        "result_projection": result_projection,
    }
    previous = {name: getattr(M2, name) for name in bindings}
    try:
        for name, value in bindings.items():
            setattr(M2, name, value)
        yield
    finally:
        for name, value in previous.items():
            setattr(M2, name, value)


def probe_stack_environment(
    toolchain_root: Path,
    *,
    run_command: Callable[..., subprocess.CompletedProcess[bytes]] = subprocess.run,
) -> dict[str, Any]:
    toolchain = toolchain_root.resolve()
    lean = toolchain / "bin/lean"
    if not lean.is_file() or lean.is_symlink():
        raise R3Error("R3 direct-runtime probe lacks regular released Lean")
    with tempfile.TemporaryDirectory(prefix="axeyum-m2-r3-stack-probe-") as temporary:
        probe = Path(temporary) / "probe.lean"
        probe.write_bytes(PROBE_SOURCE)
        environment = {
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            STACK_ENV: str(STACK_SIZE_KB),
            "PATH": f"{toolchain / 'bin'}:/usr/bin:/bin",
            "TZ": "UTC",
        }
        command = [str(lean), "--run", str(probe)]
        completed = run_command(
            command,
            cwd=Path(temporary),
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    if completed.returncode != 0 or completed.stdout != b"524288\n":
        raise R3Error("R3 direct-runtime stack probe failed")
    return {
        "command": [str(lean), "--run", "<temporary>/probe.lean"],
        "environment": environment,
        "source_sha256": BASE.sha256_bytes(PROBE_SOURCE),
        "stdout_sha256": BASE.sha256_bytes(completed.stdout),
        "stderr_sha256": BASE.sha256_bytes(completed.stderr),
        "exit_code": completed.returncode,
        "selected_case": False,
    }


def _load(root: Path, relative: str) -> Any:
    try:
        return BASE.load_canonical(root / relative)
    except BASE.U2ExecutionError as error:
        raise R3Error(f"cannot load R3 evidence record: {relative}") from error


def _descriptor(path: str, payload: bytes) -> dict[str, Any]:
    return {"path": path, "bytes": len(payload), "sha256": BASE.sha256_bytes(payload)}


def validate_dependencies(root: Path, *, allow_completion: bool = False) -> dict[str, Any]:
    if not allow_completion and (root / "completion.json").exists():
        raise R3Error("R3 completion exists before dependency validation")
    required = {
        *OLD_STORE.FIXED_JSON_PATHS,
        *OLD_STORE.FIXED_RAW_PATHS,
        *OLD_STORE.FIXED_ARTIFACT_PATHS,
        *(OLD_STORE.case_path(index) for index in range(M2.SHARD_CASE_COUNT)),
    }
    missing = sorted(path for path in required if not (root / path).is_file())
    if missing:
        raise R3Error(f"missing R3 evidence dependency: {missing[0]}")
    inventory = OLD_STORE.accepted_inventory(root, include_completion=False)
    spec = _load(root, "spec.json")
    terminal = _load(root, "terminal.json")
    junit = _load(root, "junit.json")
    post = _load(root, "post.json")
    projection = _load(root, "projection.json")
    harness = _load(root, "harness.json")
    if validate_spec(spec):
        raise R3Error("R3 retained spec drift")
    for relative in OLD_STORE.FIXED_JSON_PATHS:
        value = _load(root, relative)
        schema = value.get("schema") if isinstance(value, dict) else None
        if not isinstance(schema, str) or not BASE.valid_seal(value, schema):
            raise R3Error(f"R3 evidence record seal drift: {relative}")
    if not BASE.valid_seal(harness, M2.HARNESS_SCHEMA):
        raise R3Error("R3 retained harness drift")
    if M2.validate_junit_projection(junit):
        raise R3Error("R3 retained JUnit drift")
    if projection != result_projection(junit, post):
        raise R3Error("R3 retained result projection drift")
    cases = [_load(root, OLD_STORE.case_path(i)) for i in range(M2.SHARD_CASE_COUNT)]
    if M2.validate_case_records(cases, spec=spec, terminal=terminal, junit=junit):
        raise R3Error("R3 retained case records drift")

    discovery = _load(root, "discovery.json")
    raw_discovery = (root / "raw/discovery.json").read_bytes()
    if discovery.get("raw") != _descriptor("raw/discovery.json", raw_discovery):
        raise R3Error("R3 discovery payload drift")
    if junit.get("raw") != _descriptor(
        "raw/junit.xml", (root / "raw/junit.xml").read_bytes()
    ):
        raise R3Error("R3 JUnit payload drift")
    expected_raw = [
        _descriptor(path, (root / path).read_bytes())
        for path in ("raw/stderr.bin", "raw/stdout.bin")
    ]
    if terminal.get("raw_outputs") != expected_raw:
        raise R3Error("R3 terminal payload drift")

    retained, metadata, wrapper = _split_generated(post.get("generated_files", []))
    if (
        post.get("retained_generated")
        != [row | {"evidence_path": OLD_STORE.generated_path(row["path"])} for row in retained]
        or post.get("manifest_only_generated") != metadata
        or post.get("existing_wrapper") != wrapper
        or post.get("generated_files_sha256")
        != BASE.domain_digest(FULL_DOMAIN, post["generated_files"])
        or post.get("retained_generated_sha256")
        != BASE.domain_digest(RETAINED_DOMAIN, retained)
        or post.get("manifest_only_generated_sha256")
        != BASE.domain_digest(METADATA_DOMAIN, metadata)
    ):
        raise R3Error("R3 post assurance split drift")
    generated_paths = set()
    for row in retained:
        relative = OLD_STORE.generated_path(row["path"])
        generated_paths.add(relative)
        payload = (root / relative).read_bytes()
        if len(payload) != row["bytes"] or BASE.sha256_bytes(payload) != row["sha256"]:
            raise R3Error(f"R3 retained generated payload drift: {row['path']}")
    forbidden_metadata = [
        OLD_STORE.generated_path(row["path"])
        for row in metadata
        if (root / OLD_STORE.generated_path(row["path"])).exists()
    ]
    if forbidden_metadata:
        raise R3Error(f"R3 metadata-only payload was retained: {forbidden_metadata[0]}")
    wrapper_payload = (root / OLD_STORE.FIXED_ARTIFACT_PATHS[0]).read_bytes()
    if (
        len(wrapper) != 1
        or wrapper[0]["bytes"] != len(wrapper_payload)
        or wrapper[0]["sha256"] != BASE.sha256_bytes(wrapper_payload)
        or harness.get("wrapper")
        != {"bytes": len(wrapper_payload), "sha256": BASE.sha256_bytes(wrapper_payload), "mode": 0o755}
    ):
        raise R3Error("R3 wrapper artifact closure drift")
    ctest_payload = (root / OLD_STORE.FIXED_ARTIFACT_PATHS[1]).read_bytes()
    if harness.get("ctest_file") != {
        "bytes": len(ctest_payload),
        "sha256": BASE.sha256_bytes(ctest_payload),
    }:
        raise R3Error("R3 CTest artifact closure drift")
    inventory_paths = {row["path"] for row in inventory}
    expected_inventory = {
        *required,
        *generated_paths,
    }
    if inventory_paths != expected_inventory:
        raise R3Error("R3 evidence namespace closure drift")
    return {"spec": spec, "terminal": terminal, "junit": junit, "post": post, "projection": projection, "cases": cases}


def build_completion(root: Path) -> dict[str, Any]:
    bundle = validate_dependencies(root)
    dependencies = OLD_STORE.accepted_inventory(root, include_completion=False)
    return BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "shard_id": M2.SHARD_ID,
            "state": "complete-local-official-shard-outcomes",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(RECORD_SET_DOMAIN, dependencies),
            "case_records": [
                {
                    "ordinal": index,
                    "case_id": record["case_id"],
                    "path": OLD_STORE.case_path(index),
                    "record_sha256": record["record_sha256"],
                }
                for index, record in enumerate(bundle["cases"])
            ],
            "projection_sha256": bundle["projection"]["record_sha256"],
            "credits": bundle["projection"]["credits"],
            "assurance": {
                "retained_payload_count": 67,
                "metadata_only_count": 56,
                "metadata_only_independently_replayable": False,
            },
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def install_completion(root: Path) -> dict[str, Any]:
    completion = build_completion(root)
    BASE.install_json(root, "completion.json", completion)
    return completion


def validate_complete_store(root: Path) -> dict[str, Any]:
    completion_path = root / "completion.json"
    if (
        not completion_path.is_file()
        or completion_path.is_symlink()
        or completion_path.stat().st_mode & 0o777 != 0o444
    ):
        raise R3Error("missing, linked, or mutable R3 completion record")
    completion = _load(root, "completion.json")
    if not BASE.valid_seal(completion, COMPLETION_SCHEMA):
        raise R3Error("R3 completion identity drift")
    bundle = validate_dependencies(root, allow_completion=True)
    dependencies = OLD_STORE.accepted_inventory(root, include_completion=False)
    expected = BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "shard_id": M2.SHARD_ID,
            "state": "complete-local-official-shard-outcomes",
            "completion_installed_last": True,
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(RECORD_SET_DOMAIN, dependencies),
            "case_records": [
                {
                    "ordinal": index,
                    "case_id": record["case_id"],
                    "path": OLD_STORE.case_path(index),
                    "record_sha256": record["record_sha256"],
                }
                for index, record in enumerate(bundle["cases"])
            ],
            "projection_sha256": bundle["projection"]["record_sha256"],
            "credits": bundle["projection"]["credits"],
            "assurance": {
                "retained_payload_count": 67,
                "metadata_only_count": 56,
                "metadata_only_independently_replayable": False,
            },
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )
    if completion != expected:
        raise R3Error("R3 completion dependency or credit drift")
    return completion


def capture_post(
    *,
    source_root: Path,
    source: dict[str, Any],
    wrapper: bytes,
    junit: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bytes]]:
    before = {row["path"]: row for row in source["files"]}
    after = {row["path"]: row for row in BASE.manifest_tree(source_root)}
    changed = [path for path, row in before.items() if after.get(path) != row]
    if changed or set(before) - set(after):
        raise R3Error("official source or sidecar mutated")
    generated = [after[path] for path in sorted(set(after) - set(before))]
    post = build_post_record(
        original_files=source["files"], generated_files=generated, junit=junit
    )
    retained, _, wrapper_rows = _split_generated(generated)
    payloads = {row["path"]: (source_root / row["path"]).read_bytes() for row in retained}
    if (
        len(wrapper_rows) != 1
        or (source_root / wrapper_rows[0]["path"]).read_bytes() != wrapper
    ):
        raise R3Error("R3 generated environment wrapper mutated")
    return post, payloads


def validate_revision_preflight(implementation_revision: str) -> None:
    OLD_RUN.validate_revision_preflight(implementation_revision)
    branch = OLD_RUN._git(ROOT, "branch", "--show-current")
    remote = OLD_RUN._git(ROOT, "ls-remote", "--heads", "origin", branch)
    fields = remote.split()
    if len(fields) != 2 or fields[0] != implementation_revision:
        raise R3Error("R3 implementation revision is not remote-equal")


def validate_live_paths(args: argparse.Namespace) -> None:
    expected_work = Path(WORK_ROOT_PREFIX + args.implementation_revision[:8])
    if args.work_root.resolve() != expected_work:
        raise R3Error("R3 work root is not the frozen revision-named path")
    if args.evidence_root.resolve() != DEFAULT_EVIDENCE_ROOT.resolve():
        raise R3Error("R3 evidence root substitution")
    if args.source_repo.resolve() != DEFAULT_SOURCE_REPO.resolve():
        raise R3Error("R3 source repository substitution")
    if args.toolchain_root.resolve() != DEFAULT_TOOLCHAIN_ROOT.resolve():
        raise R3Error("R3 released toolchain substitution")


def validate_complete_evidence(root: Path) -> dict[str, Any]:
    with r3_bindings():
        completion = validate_complete_store(root)
        spec = _load(root, "spec.json")
        source = _load(root, "source.json")
        toolchain = _load(root, "toolchain.json")
        tools = _load(root, "tools.json")
        platform = _load(root, "platform.json")
        lane = _load(root, "lane.json")
        run = _load(root, "run.json")
        shard = _load(root, "shard.json")
        harness = _load(root, "harness.json")
        discovery = _load(root, "discovery.json")
        prelaunch = _load(root, "prelaunch.json")
        terminal = _load(root, "terminal.json")
        raw_discovery = (root / "raw/discovery.json").read_bytes()
        stdout = (root / "raw/stdout.bin").read_bytes()
        stderr = (root / "raw/stderr.bin").read_bytes()
        failures = [
            *OLD_RUN.validate_selected_source(source),
            *TOOLCHAIN.validate_toolchain_record(toolchain),
            *BASE.validate_local_tools(tools),
            *OLD_RUN.validate_platform_record(platform),
            *OLD_RUN.validate_lane_record(lane),
            *OLD_RUN.validate_shard_record(shard),
            *OLD_RUN.validate_discovery_record(discovery, spec=spec, harness=harness, raw=raw_discovery),
            *OLD_RUN.validate_run_record(
                run,
                spec=spec,
                source=source,
                toolchain=toolchain,
                tools=tools,
                platform=platform,
                lane=lane,
                shard=shard,
                harness=harness,
                discovery=discovery,
            ),
            *OLD_RUN.validate_prelaunch_record(prelaunch, spec=spec, run=run, shard=shard),
            *OLD_RUN.validate_terminal_record(
                terminal,
                prelaunch=prelaunch,
                stdout=stdout,
                stderr=stderr,
                require_eligible=True,
            ),
        ]
        try:
            payload = json.loads(raw_discovery)
            expected_harness = build_harness_record(
                source_root=Path(spec["source_root"]),
                toolchain_root=Path(spec["toolchain_root"]),
                harness_root=Path(spec["harness_build"]),
                discovery_payload=payload,
            )
            expected_wrapper = render_environment_wrapper(
                Path(spec["source_root"]), Path(spec["toolchain_root"])
            )
            expected_ctest = M2.render_ctest_file(
                source_root=Path(spec["source_root"]),
                toolchain_root=Path(spec["toolchain_root"]),
                harness_root=Path(spec["harness_build"]),
            )
        except (KeyError, TypeError, json.JSONDecodeError, M2.M2ContractError, R3Error) as error:
            failures.append(f"R3 retained harness cannot be reconstructed: {error}")
        else:
            if harness != expected_harness:
                failures.append("R3 retained harness semantic drift")
            if (root / OLD_STORE.FIXED_ARTIFACT_PATHS[0]).read_bytes() != expected_wrapper:
                failures.append("R3 retained wrapper semantic drift")
            if (root / OLD_STORE.FIXED_ARTIFACT_PATHS[1]).read_bytes() != expected_ctest:
                failures.append("R3 retained CTest file semantic drift")
        if failures:
            raise R3Error("; ".join(failures))
        return completion


def validate_incomplete_evidence(root: Path) -> dict[str, Any]:
    """Validate an immutable terminal failure that stopped before JUnit credit."""
    validate_history()
    forbidden = {
        "raw/junit.xml",
        "junit.json",
        "post.json",
        "projection.json",
        "completion.json",
    }
    forbidden.update(OLD_STORE.case_path(i) for i in range(M2.SHARD_CASE_COUNT))
    present_forbidden = sorted(path for path in forbidden if (root / path).exists())
    if present_forbidden:
        raise R3Error(f"R3 incomplete evidence gained {present_forbidden[0]}")
    expected_paths = {
        "source.json",
        "toolchain.json",
        "tools.json",
        "platform.json",
        "lane.json",
        "run.json",
        "shard.json",
        "harness.json",
        "discovery.json",
        "spec.json",
        "prelaunch.json",
        "terminal.json",
        "artifacts/with_stage1_test_env.sh",
        "artifacts/CTestTestfile.cmake",
        "raw/discovery.json",
        "raw/stdout.bin",
        "raw/stderr.bin",
    }
    inventory = OLD_STORE.accepted_inventory(root, include_completion=False)
    if {row["path"] for row in inventory} != expected_paths:
        raise R3Error("R3 incomplete evidence namespace drift")
    with r3_bindings():
        spec = _load(root, "spec.json")
        source = _load(root, "source.json")
        toolchain = _load(root, "toolchain.json")
        tools = _load(root, "tools.json")
        platform = _load(root, "platform.json")
        lane = _load(root, "lane.json")
        run = _load(root, "run.json")
        shard = _load(root, "shard.json")
        harness = _load(root, "harness.json")
        discovery = _load(root, "discovery.json")
        prelaunch = _load(root, "prelaunch.json")
        terminal = _load(root, "terminal.json")
        raw_discovery = (root / "raw/discovery.json").read_bytes()
        stdout = (root / "raw/stdout.bin").read_bytes()
        stderr = (root / "raw/stderr.bin").read_bytes()
        failures = [
            *validate_spec(spec),
            *OLD_RUN.validate_selected_source(source),
            *TOOLCHAIN.validate_toolchain_record(toolchain),
            *BASE.validate_local_tools(tools),
            *OLD_RUN.validate_platform_record(platform),
            *OLD_RUN.validate_lane_record(lane),
            *OLD_RUN.validate_shard_record(shard),
            *OLD_RUN.validate_discovery_record(
                discovery, spec=spec, harness=harness, raw=raw_discovery
            ),
            *OLD_RUN.validate_run_record(
                run,
                spec=spec,
                source=source,
                toolchain=toolchain,
                tools=tools,
                platform=platform,
                lane=lane,
                shard=shard,
                harness=harness,
                discovery=discovery,
            ),
            *OLD_RUN.validate_prelaunch_record(
                prelaunch, spec=spec, run=run, shard=shard
            ),
            *OLD_RUN.validate_terminal_record(
                terminal,
                prelaunch=prelaunch,
                stdout=stdout,
                stderr=stderr,
                require_eligible=False,
            ),
        ]
        expected_events = [
            "prelaunch-record-installed",
            "rlimit-as-installed",
            "wall-timeout-observed",
            "process-group-sigterm-sent",
            "direct-child-reaped",
            "process-group-no-live-members-observed",
        ]
        process = terminal.get("process", {})
        if (
            terminal.get("class") != "wall-timeout"
            or terminal.get("exit_code") is not None
            or terminal.get("signal") != 15
            or terminal.get("events") != expected_events
            or process.get("watchdog_fired") is not True
            or process.get("sigterm_sent") is not True
            or process.get("sigkill_sent") is not False
            or process.get("direct_child_reaped") is not True
            or process.get("live_non_zombie_pids_after_cleanup") != []
            or terminal.get("wall_time", {}).get("value", 0) < M2.WALL_TIMEOUT_MS
        ):
            failures.append("R3 incomplete timeout or cleanup drift")
        try:
            payload = json.loads(raw_discovery)
            expected_harness = build_harness_record(
                source_root=Path(spec["source_root"]),
                toolchain_root=Path(spec["toolchain_root"]),
                harness_root=Path(spec["harness_build"]),
                discovery_payload=payload,
            )
            expected_wrapper = render_environment_wrapper(
                Path(spec["source_root"]), Path(spec["toolchain_root"])
            )
            expected_ctest = M2.render_ctest_file(
                source_root=Path(spec["source_root"]),
                toolchain_root=Path(spec["toolchain_root"]),
                harness_root=Path(spec["harness_build"]),
            )
        except (KeyError, TypeError, json.JSONDecodeError, M2.M2ContractError, R3Error) as error:
            failures.append(f"R3 incomplete harness cannot be reconstructed: {error}")
        else:
            if harness != expected_harness:
                failures.append("R3 incomplete harness semantic drift")
            if (root / OLD_STORE.FIXED_ARTIFACT_PATHS[0]).read_bytes() != expected_wrapper:
                failures.append("R3 incomplete wrapper semantic drift")
            if (root / OLD_STORE.FIXED_ARTIFACT_PATHS[1]).read_bytes() != expected_ctest:
                failures.append("R3 incomplete CTest semantic drift")
        if failures:
            raise R3Error("; ".join(failures))
    return {
        "terminal": terminal,
        "inventory": inventory,
        "files": len(inventory),
        "bytes": sum(row["bytes"] for row in inventory),
        "manifest_sha256": BASE.domain_digest(
            "axeyum-lean-u2-official-execution-m2-r3-incomplete-evidence-v1",
            R2_DIAGNOSTIC.portable_manifest(root),
        ),
        "official_outcomes": 0,
        "parity_credit": 0,
    }


def run_r3(args: argparse.Namespace) -> None:
    validate_offline_contract()
    validate_revision_preflight(args.implementation_revision)
    validate_live_paths(args)
    if args.work_root.exists() or args.work_root.is_symlink():
        raise R3Error("R3 private work root must be new")
    if args.evidence_root.exists() or args.evidence_root.is_symlink():
        raise R3Error("R3 evidence root must be new")
    probe_stack_environment(args.toolchain_root)
    args.work_root.mkdir(parents=True, mode=0o700)
    source_root = args.work_root / "source"
    harness_root = args.work_root / "harness"
    private_root = args.work_root / "attempt"
    junit_path = private_root / "test-results.xml"
    with r3_bindings():
        source = OLD_RUN.capture_source(args.source_repo, source_root)
        toolchain = OLD_RUN.capture_toolchain(args.toolchain_root, args.work_root)
        tools = BASE.capture_local_tools()
        failures = BASE.validate_local_tools(tools)
        if failures:
            raise R3Error("; ".join(failures))
        harness, discovery, wrapper, ctest, raw_discovery = OLD_RUN.prepare_harness(
            source_root=source_root,
            toolchain_root=args.toolchain_root,
            harness_root=harness_root,
        )
        spec = build_spec(
            implementation_revision=args.implementation_revision,
            source_root=source_root,
            toolchain_root=args.toolchain_root,
            harness_build=harness_root,
            junit_path=junit_path,
        )
        failures = validate_spec(spec)
        if failures:
            raise R3Error("; ".join(failures))
        platform = OLD_RUN.build_platform_record(source_root)
        lane = OLD_RUN.build_lane_record()
        shard = OLD_RUN.build_shard_record()
        storage = BASE.STORE.capture_storage_class(BASE.STORE.STORAGE_CLASS_IDS[0], ROOT)
        BASE.STORE.preflight_storage_class(storage)
        run = OLD_RUN.build_run_record(
            spec=spec,
            source=source,
            toolchain=toolchain,
            tools=tools,
            platform=platform,
            lane=lane,
            shard=shard,
            harness=harness,
            discovery=discovery,
            storage=storage,
        )
        prelaunch = OLD_RUN.build_prelaunch_record(spec=spec, run=run, shard=shard)
        OLD_RUN._install_prelaunch(
            args.evidence_root,
            records={
                "source.json": source,
                "toolchain.json": toolchain,
                "tools.json": tools,
                "platform.json": platform,
                "lane.json": lane,
                "run.json": run,
                "shard.json": shard,
                "harness.json": harness,
                "discovery.json": discovery,
                "spec.json": spec,
                "prelaunch.json": prelaunch,
            },
            wrapper=wrapper,
            ctest=ctest,
            raw_discovery=raw_discovery,
        )
        terminal, stdout, stderr = OLD_RUN.execute_process(
            spec, private_root, prelaunch["record_sha256"]
        )
        BASE.install_bytes(args.evidence_root, "raw/stdout.bin", stdout)
        BASE.install_bytes(args.evidence_root, "raw/stderr.bin", stderr)
        BASE.install_json(args.evidence_root, "terminal.json", terminal)
        process = terminal["process"]
        if (
            terminal["class"] != "exited"
            or terminal["exit_code"] not in {0, 8}
            or terminal["signal"] is not None
            or process["watchdog_fired"]
            or not process["direct_child_reaped"]
            or process["live_non_zombie_pids_after_cleanup"] != []
        ):
            raise R3Error("R3 CTest process did not close as an eligible exited group")
        if not junit_path.is_file() or junit_path.is_symlink():
            raise R3Error("R3 CTest process produced no regular JUnit file")
        raw_junit = junit_path.read_bytes()
        BASE.install_bytes(args.evidence_root, "raw/junit.xml", raw_junit)
        junit = M2.parse_junit(raw_junit, terminal)
        BASE.install_json(args.evidence_root, "junit.json", junit)
        cases = M2.build_case_records(spec=spec, terminal=terminal, junit=junit)
        for ordinal, case in enumerate(cases):
            BASE.install_json(args.evidence_root, OLD_STORE.case_path(ordinal), case)
        post, retained = capture_post(
            source_root=source_root, source=source, wrapper=wrapper, junit=junit
        )
        for source_path, payload in retained.items():
            BASE.install_bytes(
                args.evidence_root, OLD_STORE.generated_path(source_path), payload
            )
        BASE.install_json(args.evidence_root, "post.json", post)
        projection = result_projection(junit, post)
        BASE.install_json(args.evidence_root, "projection.json", projection)
        completion = install_completion(args.evidence_root)
        validate_complete_evidence(args.evidence_root)
        BASE.validate_live_readonly_tree(args.evidence_root)
    print(
        "LEAN_U2_M2_R3_RUN|"
        f"cases={projection['credits']['official_cases']}|"
        f"passes={projection['credits']['official_passes']}|"
        f"failures={projection['credits']['official_failures']}|"
        f"completion={completion['record_sha256']}|retained=67|metadata_only=56|"
        "parent_complete=false|provider=false|axeyum=0|pairs=0|parity=0"
    )


def validate_offline_contract() -> dict[str, Any]:
    validate_history()
    contract = M2.validate_offline_contract()
    source = Path("/r3/source")
    toolchain = Path("/r3/toolchain")
    harness = Path("/r3/harness")
    spec = build_spec(
        implementation_revision="0" * 40,
        source_root=source,
        toolchain_root=toolchain,
        harness_build=harness,
        junit_path=Path("/r3/attempt/test-results.xml"),
    )
    if validate_spec(spec):
        raise R3Error("R3 offline spec drift")
    wrapper = render_environment_wrapper(source, toolchain)
    cases = M2.selected_contract()["cases"]
    if len(cases) != 64 or len(declared_generated_paths()) != 124:
        raise R3Error("R3 shard or generated-path count drift")
    return {
        "cases": contract["case_count"],
        "generated": len(declared_generated_paths()),
        "wrapper_sha256": BASE.sha256_bytes(wrapper),
        "selected_processes": 0,
        "outcomes": 0,
        "parity": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("offline-check")
    probe = commands.add_parser("probe-stack")
    probe.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run = commands.add_parser("run-r3")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--source-repo", type=Path, default=DEFAULT_SOURCE_REPO)
    run.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    incomplete = commands.add_parser("validate-incomplete")
    incomplete.add_argument(
        "--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT
    )
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            summary = validate_offline_contract()
            print(
                "LEAN_U2_M2_R3|"
                f"cases={summary['cases']}|generated={summary['generated']}|"
                "selected_processes=0|outcomes=0|pairs=0|parity=0"
            )
        elif args.command == "probe-stack":
            result = probe_stack_environment(args.toolchain_root)
            print(
                "LEAN_U2_M2_R3_STACK_PROBE|"
                f"source={result['source_sha256']}|exit=0|value={STACK_SIZE_KB}|"
                "selected_case=false"
            )
        elif args.command == "run-r3":
            run_r3(args)
        elif args.command == "validate":
            completion = validate_complete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R3_EVIDENCE_VALID|"
                f"completion={completion['record_sha256']}|cases=64|"
                "parent_complete=false|parity=0"
            )
        elif args.command == "validate-incomplete":
            result = validate_incomplete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R3_INCOMPLETE_VALID|"
                f"terminal={result['terminal']['record_sha256']}|"
                f"class={result['terminal']['class']}|files={result['files']}|"
                f"bytes={result['bytes']}|outcomes=0|parity=0"
            )
        else:  # pragma: no cover
            raise AssertionError(args.command)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        BASE.STORE.StoreEvidenceError,
        M2.M2ContractError,
        OLD_RUN.M2RunError,
        OLD_STORE.M2StoreError,
        R2_DIAGNOSTIC.R2DiagnosticError,
        R3Error,
    ) as error:
        print(f"LEAN_U2_M2_R3_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
