#!/usr/bin/env python3
"""Qualify and run M2 R6 attempt-004 with conditional CTest log closure."""

from __future__ import annotations

import argparse
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402
from scripts import lean_u2_official_execution_m2_r3 as R3  # noqa: E402
from scripts import lean_u2_official_execution_m2_r4 as R4  # noqa: E402
from scripts import lean_u2_official_execution_m2_r5 as R5  # noqa: E402
from scripts import (  # noqa: E402
    lean_u2_official_execution_m2_r5_diagnostic as R5_DIAGNOSTIC,
)
from scripts import lean_u2_official_execution_m2_run as OLD_RUN  # noqa: E402
from scripts import lean_u2_official_execution_m2_store as OLD_STORE  # noqa: E402


PLAN = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r6-"
    "attempt-004-plan-2026-07-23.md"
)
PREREGISTRATION_COMMIT = "055a3d7fd17faa26de8d04ba896c70c5640f95c8"
PLAN_SHA256 = "80d6f4875dcd11a90c79940f4b460bd3ede25f67139f22565f79dd64d8b33754"
R5_RESULT = ROOT / (
    "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r5-"
    "diagnostic-closure-result-2026-07-23.md"
)
R5_RESULT_SHA256 = "25d102e6ead0d43ad69f3eb3e5064281e20fb86368ba2be4f0b49168869eeab2"
R5_COMPLETION_SHA256 = (
    "2d5d43a7787ccf4333b152be8794a12b45edc7527e32732abb2cf1cce1ffce3c"
)

RUN_ID = "tl0.6.3-m2-release-linux-shard-0001-v5"
ATTEMPT_ID = "attempt-004"
SEQUENCE = 4
LANE_ID = "official-ctest-local-32g-lean-j1-stack512m-shard64-v5"
MEMORY_LIMIT_BYTES = R5.MEMORY_LIMIT_BYTES
STACK_SIZE_KB = R5.STACK_SIZE_KB
STACK_ENV = R5.STACK_ENV

DEFAULT_SOURCE_REPO = R5.DEFAULT_SOURCE_REPO
DEFAULT_TOOLCHAIN_ROOT = R5.DEFAULT_TOOLCHAIN_ROOT
DEFAULT_EVIDENCE_ROOT = ROOT / (
    "docs/plan/evidence/"
    "lean-u2-official-execution-tl0.6.3-m2-shard-0001-r6-attempt-004"
)
CONTROL_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r6-control-"
WORK_ROOT_PREFIX = "/home/mjbommar/.cache/axeyum-tl063-m2-r6-"

COMPLETION_SCHEMA = "axeyum-lean-u2-official-execution-m2-r6-completion-v1"
RECORD_SET_DOMAIN = "axeyum-lean-u2-official-execution-m2-r6-record-set-v1"
FULL_DOMAIN = "axeyum-lean-u2-official-execution-m2-r6-generated-files-v1"
RETAINED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r6-retained-files-v1"
METADATA_DOMAIN = "axeyum-lean-u2-official-execution-m2-r6-metadata-files-v1"
ALLOWED_DOMAIN = "axeyum-lean-u2-official-execution-m2-r6-allowed-paths-v1"

CONTROL_SPEC_SCHEMA = "axeyum-lean-u2-official-execution-m2-r6-control-spec-v1"
CONTROL_PRELAUNCH_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r6-control-prelaunch-v1"
)
CONTROL_TERMINAL_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r6-control-terminal-v1"
)
CONTROL_COMPLETION_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r6-control-completion-v1"
)
CONTROL_RECORD_SET_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r6-control-record-set-v1"
)

FAILURE_LOG = "build/release/Testing/Temporary/LastTestsFailed.log"
UNCONDITIONAL_PATHS = tuple(
    path for path in R3.declared_generated_paths() if path != FAILURE_LOG
)
_R5_VALIDATE_REVISION_PREFLIGHT = R5.validate_revision_preflight


class R6Error(ValueError):
    """The R6 preregistration, control, execution, or evidence drifted."""


def validate_history() -> dict[str, Any]:
    completion = R5_DIAGNOSTIC.validate_completed(R5.DEFAULT_EVIDENCE_ROOT)
    if (
        not M2.HEX40.fullmatch(PREREGISTRATION_COMMIT)
        or not PLAN.is_file()
        or BASE.sha256_file(PLAN) != PLAN_SHA256
        or not R5_RESULT.is_file()
        or BASE.sha256_file(R5_RESULT) != R5_RESULT_SHA256
        or completion["record_sha256"] != R5_COMPLETION_SHA256
    ):
        raise R6Error("R6 preregistration, R5 closure, or fresh-root history drift")
    return completion


def resource_envelope() -> dict[str, Any]:
    envelope = dict(R5.resource_envelope())
    envelope["lane_id"] = LANE_ID
    return envelope


def build_spec(**kwargs: Any) -> dict[str, Any]:
    spec = R5.build_spec(**kwargs)
    spec.update(
        {
            "preregistration_commit": PREREGISTRATION_COMMIT,
            "plan_sha256": PLAN_SHA256,
            "run_id": RUN_ID,
            "attempt_id": ATTEMPT_ID,
            "sequence": SEQUENCE,
            "resource_envelope": resource_envelope(),
        }
    )
    spec["prior_history"].update(
        {
            "selected_attempt_unconsumed": False,
            "r5_attempt_id": R5.ATTEMPT_ID,
            "r5_selected_attempt_consumed": True,
            "r5_selected_outcome_credit": 0,
            "r5_diagnostic_completion_sha256": R5_COMPLETION_SHA256,
        }
    )
    spec["record_sha256"] = ""
    return BASE.seal(spec, M2.SPEC_SCHEMA)


def validate_spec(spec: Any) -> list[str]:
    if not isinstance(spec, dict) or not BASE.valid_seal(spec, M2.SPEC_SCHEMA):
        return ["R6 spec identity drift"]
    try:
        expected = build_spec(
            implementation_revision=spec["implementation_revision"],
            source_root=Path(spec["source_root"]),
            toolchain_root=Path(spec["toolchain_root"]),
            harness_build=Path(spec["harness_build"]),
            junit_path=Path(spec["junit_path"]),
        )
    except (KeyError, TypeError, R5.R5Error, R6Error) as error:
        return [f"R6 spec cannot be reconstructed: {error}"]
    return [] if spec == expected else ["R6 spec field or linkage drift"]


def expected_generated_paths(junit: dict[str, Any]) -> list[str]:
    failures = M2.validate_junit_projection(junit)
    if failures:
        raise R6Error("; ".join(failures))
    paths = list(UNCONDITIONAL_PATHS)
    if junit["summary"]["official_failures"] > 0:
        paths.append(FAILURE_LOG)
    return sorted(paths)


def split_generated(
    generated_files: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    failures = BASE._validate_manifest_rows(generated_files, "R6 generated artifact")
    if failures:
        raise R6Error("; ".join(failures))
    paths = [row["path"] for row in generated_files]
    if paths not in (list(UNCONDITIONAL_PATHS), R3.declared_generated_paths()):
        raise R6Error("R6 generated path closure drift")
    if any(
        row["kind"] != "file" or row["target"] is not None
        for row in generated_files
    ):
        raise R6Error("R6 generated artifact identity is malformed")
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
        row
        for row in generated_files
        if row["path"] == "tests/with_stage1_test_env.sh"
    ]
    expected_retained = 67 if FAILURE_LOG in paths else 66
    if (len(retained), len(metadata), len(wrapper)) != (expected_retained, 56, 1):
        raise R6Error("R6 generated assurance split count drift")
    return retained, metadata, wrapper


def build_post_record(
    *,
    original_files: list[dict[str, Any]],
    generated_files: list[dict[str, Any]],
    junit: dict[str, Any],
) -> dict[str, Any]:
    failures = BASE._validate_manifest_rows(original_files, "R6 original source")
    failures.extend(M2.validate_junit_projection(junit))
    if failures:
        raise R6Error("; ".join(failures))
    expected_paths = expected_generated_paths(junit)
    if [row["path"] for row in generated_files] != expected_paths:
        raise R6Error("R6 generated paths disagree with JUnit failure state")
    retained, metadata, wrapper = split_generated(generated_files)
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
            "retained_generated": [
                row | {"evidence_path": OLD_STORE.generated_path(row["path"])}
                for row in retained
            ],
            "retained_generated_sha256": BASE.domain_digest(RETAINED_DOMAIN, retained),
            "manifest_only_generated": metadata,
            "manifest_only_generated_sha256": BASE.domain_digest(
                METADATA_DOMAIN, metadata
            ),
            "existing_wrapper": wrapper,
            "allowed_paths_sha256": BASE.domain_digest(ALLOWED_DOMAIN, expected_paths),
            "undeclared_paths": [],
            "junit_sha256": junit["record_sha256"],
            "conditional_artifact": {
                "path": FAILURE_LOG,
                "predicate": "official_failures > 0",
                "required": junit["summary"]["official_failures"] > 0,
            },
            "assurance": {
                "retained_payload_count": len(retained),
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
        raise R6Error("; ".join(failures))
    expected_paths = expected_generated_paths(junit)
    expected_retained = 67 if junit["summary"]["official_failures"] else 66
    if (
        not BASE.valid_seal(post, M2.POST_SCHEMA)
        or post.get("junit_sha256") != junit["record_sha256"]
        or post.get("original_files_unchanged") is not True
        or post.get("undeclared_paths") != []
        or [row.get("path") for row in post.get("generated_files", [])]
        != expected_paths
        or post.get("allowed_paths_sha256")
        != BASE.domain_digest(ALLOWED_DOMAIN, expected_paths)
        or post.get("conditional_artifact")
        != {
            "path": FAILURE_LOG,
            "predicate": "official_failures > 0",
            "required": junit["summary"]["official_failures"] > 0,
        }
        or post.get("assurance", {}).get("retained_payload_count")
        != expected_retained
        or post.get("assurance", {}).get("metadata_only_count") != 56
    ):
        raise R6Error("R6 post-run projection identity or conditional linkage drift")
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
                "provider_profile_complete": False,
                "axeyum_native_outcomes_observed": False,
                "paired_parity_observed": False,
                "performance_claimed": False,
            },
            "record_sha256": "",
        },
        M2.PROJECTION_SCHEMA,
    )


def capture_post(
    *, source_root: Path, source: dict[str, Any], wrapper: bytes, junit: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bytes]]:
    before = {row["path"]: row for row in source["files"]}
    after = {row["path"]: row for row in BASE.manifest_tree(source_root)}
    changed = [path for path, row in before.items() if after.get(path) != row]
    if changed or set(before) - set(after):
        raise R6Error("official source or sidecar mutated")
    generated = [after[path] for path in sorted(set(after) - set(before))]
    post = build_post_record(
        original_files=source["files"], generated_files=generated, junit=junit
    )
    retained, _, wrapper_rows = split_generated(generated)
    payloads = {
        row["path"]: (source_root / row["path"]).read_bytes() for row in retained
    }
    if (
        len(wrapper_rows) != 1
        or (source_root / wrapper_rows[0]["path"]).read_bytes() != wrapper
    ):
        raise R6Error("R6 generated environment wrapper mutated")
    return post, payloads


def _completion_assurance(bundle: dict[str, Any]) -> dict[str, Any]:
    return {
        "retained_payload_count": bundle["post"]["assurance"][
            "retained_payload_count"
        ],
        "metadata_only_count": 56,
        "metadata_only_independently_replayable": False,
    }


def build_completion(root: Path) -> dict[str, Any]:
    bundle = R3.validate_dependencies(root)
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
            "assurance": _completion_assurance(bundle),
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def validate_complete_store(root: Path) -> dict[str, Any]:
    path = root / "completion.json"
    if (
        not path.is_file()
        or path.is_symlink()
        or path.stat().st_mode & 0o777 != 0o444
    ):
        raise R6Error("missing, linked, or mutable R6 completion record")
    completion = BASE.load_canonical(path)
    if completion != build_completion(root):
        raise R6Error("R6 completion dependency or credit drift")
    return completion


@contextmanager
def r6_bindings() -> Iterator[None]:
    bindings = {
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "MEMORY_LIMIT_BYTES": MEMORY_LIMIT_BYTES,
        "resource_envelope": resource_envelope,
        "build_spec": build_spec,
        "validate_spec": validate_spec,
        "render_environment_wrapper": R4.render_environment_wrapper,
        "build_harness_record": R4.build_harness_record,
        "case_generated_paths": R3.case_generated_paths,
        "declared_generated_paths": R3.declared_generated_paths,
        "build_post_record": build_post_record,
        "result_projection": result_projection,
    }
    r3_extra = {
        "PREREGISTRATION_COMMIT": PREREGISTRATION_COMMIT,
        "PLAN_SHA256": PLAN_SHA256,
        "DEFAULT_EVIDENCE_ROOT": DEFAULT_EVIDENCE_ROOT,
        "WORK_ROOT_PREFIX": WORK_ROOT_PREFIX,
        "COMPLETION_SCHEMA": COMPLETION_SCHEMA,
        "RECORD_SET_DOMAIN": RECORD_SET_DOMAIN,
        "FULL_DOMAIN": FULL_DOMAIN,
        "RETAINED_DOMAIN": RETAINED_DOMAIN,
        "METADATA_DOMAIN": METADATA_DOMAIN,
        "ALLOWED_DOMAIN": ALLOWED_DOMAIN,
        "_split_generated": split_generated,
        "capture_post": capture_post,
        "build_completion": build_completion,
        "validate_complete_store": validate_complete_store,
    }
    r3_bindings = {
        name: value
        for name, value in {**bindings, **r3_extra}.items()
        if hasattr(R3, name)
    }
    previous_m2 = {name: getattr(M2, name) for name in bindings}
    previous_r3 = {name: getattr(R3, name) for name in r3_bindings}
    try:
        for name, value in bindings.items():
            setattr(M2, name, value)
        for name, value in r3_bindings.items():
            setattr(R3, name, value)
        yield
    finally:
        for name, value in previous_r3.items():
            setattr(R3, name, value)
        for name, value in previous_m2.items():
            setattr(M2, name, value)


@contextmanager
def r6_control_bindings() -> Iterator[None]:
    bindings = {
        "PREREGISTRATION_COMMIT": PREREGISTRATION_COMMIT,
        "PLAN_SHA256": PLAN_SHA256,
        "RUN_ID": RUN_ID,
        "ATTEMPT_ID": ATTEMPT_ID,
        "SEQUENCE": SEQUENCE,
        "LANE_ID": LANE_ID,
        "CONTROL_ROOT_PREFIX": CONTROL_ROOT_PREFIX,
        "CONTROL_SPEC_SCHEMA": CONTROL_SPEC_SCHEMA,
        "CONTROL_PRELAUNCH_SCHEMA": CONTROL_PRELAUNCH_SCHEMA,
        "CONTROL_TERMINAL_SCHEMA": CONTROL_TERMINAL_SCHEMA,
        "CONTROL_COMPLETION_SCHEMA": CONTROL_COMPLETION_SCHEMA,
        "CONTROL_RECORD_SET_DOMAIN": CONTROL_RECORD_SET_DOMAIN,
        "validate_history": validate_history,
        "validate_revision_preflight": validate_revision_preflight,
    }
    previous = {name: getattr(R5, name) for name in bindings}
    try:
        for name, value in bindings.items():
            setattr(R5, name, value)
        yield
    finally:
        for name, value in previous.items():
            setattr(R5, name, value)


def run_control(**kwargs: Any) -> dict[str, Any]:
    with r6_control_bindings():
        return R5.run_control(**kwargs)


def validate_control(root: Path, *, require_authorized: bool) -> dict[str, Any]:
    with r6_control_bindings():
        return R5.validate_control(root, require_authorized=require_authorized)


def validate_revision_preflight(revision: str) -> None:
    _R5_VALIDATE_REVISION_PREFLIGHT(revision)


def validate_live_paths(args: argparse.Namespace) -> None:
    expected_work = Path(WORK_ROOT_PREFIX + args.implementation_revision[:8])
    if args.work_root.resolve() != expected_work:
        raise R6Error("R6 selected work root substitution")
    if args.evidence_root.resolve() != DEFAULT_EVIDENCE_ROOT.resolve():
        raise R6Error("R6 evidence root substitution")
    if args.source_repo.resolve() != DEFAULT_SOURCE_REPO.resolve():
        raise R6Error("R6 source repository substitution")
    if args.toolchain_root.resolve() != DEFAULT_TOOLCHAIN_ROOT.resolve():
        raise R6Error("R6 toolchain substitution")


def validate_complete_evidence(root: Path) -> dict[str, Any]:
    validate_history()
    with r6_bindings():
        return R3.validate_complete_evidence(root)


def validate_offline_contract() -> dict[str, Any]:
    validate_history()
    spec = build_spec(
        implementation_revision="0" * 40,
        source_root=Path("/r6/source"),
        toolchain_root=Path("/r6/toolchain"),
        harness_build=Path("/r6/harness"),
        junit_path=Path("/r6/attempt/test-results.xml"),
    )
    if validate_spec(spec):
        raise R6Error("R6 offline spec drift")
    if (
        resource_envelope()["memory_limit"]["value"] != MEMORY_LIMIT_BYTES
        or len(M2.selected_contract()["cases"]) != 64
        or len(UNCONDITIONAL_PATHS) != 123
        or len(R3.declared_generated_paths()) != 124
    ):
        raise R6Error("R6 resource, shard, or conditional-path contract drift")
    return {
        "cases": 64,
        "all_pass_generated": 123,
        "failing_generated": 124,
        "memory_limit_bytes": MEMORY_LIMIT_BYTES,
        "controls": 0,
        "selected_processes": 0,
        "outcomes": 0,
        "parity": 0,
    }


def run_r6(args: argparse.Namespace) -> None:
    validate_offline_contract()
    validate_revision_preflight(args.implementation_revision)
    validate_live_paths(args)
    if args.work_root.exists() or args.work_root.is_symlink():
        raise R6Error("R6 private work root must be new")
    if args.evidence_root.exists() or args.evidence_root.is_symlink():
        raise R6Error("R6 evidence root must be new")
    control = validate_control(args.control_root, require_authorized=True)
    if control["record_sha256"] != args.control_completion_sha256:
        raise R6Error("R6 explicit control completion digest mismatch")

    args.work_root.mkdir(parents=True, mode=0o700)
    source_root = args.work_root / "source"
    harness_root = args.work_root / "harness"
    private_root = args.work_root / "attempt"
    junit_path = private_root / "test-results.xml"
    with r6_bindings():
        source = OLD_RUN.capture_source(args.source_repo, source_root)
        toolchain = OLD_RUN.capture_toolchain(args.toolchain_root, args.work_root)
        tools = BASE.capture_local_tools()
        if failures := BASE.validate_local_tools(tools):
            raise R6Error("; ".join(failures))
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
        platform = OLD_RUN.build_platform_record(source_root)
        lane = OLD_RUN.build_lane_record()
        shard = OLD_RUN.build_shard_record()
        storage = BASE.STORE.capture_storage_class(
            BASE.STORE.STORAGE_CLASS_IDS[0], ROOT
        )
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
            raise R6Error("R6 CTest process did not close as an eligible exited group")
        if not junit_path.is_file() or junit_path.is_symlink():
            raise R6Error("R6 CTest process produced no regular JUnit file")
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
        completion = R3.install_completion(args.evidence_root)
        validate_complete_evidence(args.evidence_root)
        BASE.validate_live_readonly_tree(args.evidence_root)
    print(
        "LEAN_U2_M2_R6_RUN|"
        f"cases={projection['credits']['official_cases']}|"
        f"passes={projection['credits']['official_passes']}|"
        f"failures={projection['credits']['official_failures']}|"
        f"completion={completion['record_sha256']}|"
        f"retained={post['assurance']['retained_payload_count']}|"
        "metadata_only=56|parent_complete=false|provider=false|"
        "axeyum=0|pairs=0|parity=0"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("offline-check")
    stack = commands.add_parser("probe-stack")
    stack.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    control = commands.add_parser("run-control")
    control.add_argument("--implementation-revision", required=True)
    control.add_argument("--control-root", type=Path, required=True)
    control.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    validate_control_cmd = commands.add_parser("validate-control")
    validate_control_cmd.add_argument("--control-root", type=Path, required=True)
    validate_control_cmd.add_argument("--require-authorized", action="store_true")
    run = commands.add_parser("run-r6")
    run.add_argument("--implementation-revision", required=True)
    run.add_argument("--control-root", type=Path, required=True)
    run.add_argument("--control-completion-sha256", required=True)
    run.add_argument("--source-repo", type=Path, default=DEFAULT_SOURCE_REPO)
    run.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    run.add_argument("--work-root", type=Path, required=True)
    run.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    validate = commands.add_parser("validate")
    validate.add_argument("--evidence-root", type=Path, default=DEFAULT_EVIDENCE_ROOT)
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            summary = validate_offline_contract()
            print(
                "LEAN_U2_M2_R6|cases=64|all_pass_generated=123|"
                "failing_generated=124|"
                f"memory={summary['memory_limit_bytes']}|controls=0|"
                "selected_processes=0|outcomes=0|pairs=0|parity=0"
            )
        elif args.command == "probe-stack":
            result = R4.probe_stack_environment(args.toolchain_root)
            print(
                "LEAN_U2_M2_R6_STACK_PROBE|"
                f"source={result['source_sha256']}|exit=0|value={STACK_SIZE_KB}|"
                "selected_case=false"
            )
        elif args.command == "run-control":
            result = run_control(
                implementation_revision=args.implementation_revision,
                control_root=args.control_root,
                toolchain_root=args.toolchain_root,
            )
            state = (
                "AUTHORIZED" if result["authorized_selected_execution"] else "BLOCKED"
            )
            print(
                f"LEAN_U2_M2_R6_CONTROL_{state}|"
                f"completion={result['record_sha256']}|"
                "selected_attempt_consumed=false|outcomes=0|parity=0"
            )
            if not result["authorized_selected_execution"]:
                return 1
        elif args.command == "validate-control":
            result = validate_control(
                args.control_root, require_authorized=args.require_authorized
            )
            print(
                "LEAN_U2_M2_R6_CONTROL_VALID|"
                f"completion={result['record_sha256']}|"
                f"authorized={str(result['authorized_selected_execution']).lower()}|"
                "selected_attempt_consumed=false|parity=0"
            )
        elif args.command == "run-r6":
            run_r6(args)
        elif args.command == "validate":
            result = validate_complete_evidence(args.evidence_root)
            print(
                "LEAN_U2_M2_R6_EVIDENCE_VALID|"
                f"completion={result['record_sha256']}|cases=64|parity=0"
            )
        else:  # pragma: no cover
            raise AssertionError(args.command)
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        M2.M2ContractError,
        OLD_RUN.M2RunError,
        OLD_STORE.M2StoreError,
        R3.R3Error,
        R4.R4Error,
        R5.R5Error,
        R5_DIAGNOSTIC.R5DiagnosticError,
        R6Error,
    ) as error:
        print(f"LEAN_U2_M2_R6_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
