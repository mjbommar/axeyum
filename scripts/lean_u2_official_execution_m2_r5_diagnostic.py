#!/usr/bin/env python3
"""Validate and append R5 attempt-003's zero-credit diagnostic closure."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2 as M2  # noqa: E402
from scripts import lean_u2_official_execution_m2_r3 as R3  # noqa: E402
from scripts import lean_u2_official_execution_m2_r5 as R5  # noqa: E402
from scripts import lean_u2_official_execution_m2_run as OLD_RUN  # noqa: E402
from scripts import lean_u2_official_execution_m2_store as OLD_STORE  # noqa: E402


EVIDENCE_ROOT = R5.DEFAULT_EVIDENCE_ROOT
WORK_SOURCE = Path("/home/mjbommar/.cache/axeyum-tl063-m2-r5-c445027d/source")
IMPLEMENTATION_REVISION = "c445027d04c08d6c72803710d9c4e6640dc4bc5c"
RAW_FILES = 83
RAW_BYTES = 5_078_773
RAW_DOMAIN = "r5-incomplete-evidence-v1"
RAW_DIGEST = "10d3d3c5dc565331b8a2b3723d0e1155180386017a5ee1ccb17306df8cc9369d"
GENERATED_DOMAIN = "r5-generated-diagnostic-v1"
GENERATED_DIGEST = "75feb6d5520aec0286b1dac83bbd3a5047e93f238eb5c3b986c48136e00c1c67"
POST_SCHEMA = "axeyum-lean-u2-official-execution-m2-r5-diagnostic-post-v1"
COMPLETION_SCHEMA = (
    "axeyum-lean-u2-official-execution-m2-r5-diagnostic-completion-v1"
)
RECORD_SET_DOMAIN = (
    "axeyum-lean-u2-official-execution-m2-r5-diagnostic-record-set-v1"
)
FAILURE_LOG = "build/release/Testing/Temporary/LastTestsFailed.log"


class R5DiagnosticError(ValueError):
    """The frozen R5 diagnostic closure drifted."""


def _load(root: Path, path: str) -> Any:
    return BASE.load_canonical(root / path)


def _raw_inventory(root: Path) -> list[dict[str, Any]]:
    return [
        row
        for row in R3.R2_DIAGNOSTIC.portable_manifest(root)
        if not row["path"].startswith("diagnostic/")
    ]


def _descriptor(path: str, payload: bytes) -> dict[str, Any]:
    return {"path": path, "bytes": len(payload), "sha256": BASE.sha256_bytes(payload)}


def validate_raw(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    R5.validate_history()
    inventory = _raw_inventory(root)
    if (
        len(inventory) != RAW_FILES
        or sum(row["bytes"] for row in inventory) != RAW_BYTES
        or BASE.domain_digest(RAW_DOMAIN, inventory) != RAW_DIGEST
    ):
        raise R5DiagnosticError("R5 raw evidence identity drift")
    forbidden = ("post.json", "projection.json", "completion.json")
    if any((root / name).exists() for name in forbidden):
        raise R5DiagnosticError("R5 raw root gained a selected completion record")
    with R5.r5_bindings():
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
        junit = _load(root, "junit.json")
        raw_discovery = (root / "raw/discovery.json").read_bytes()
        stdout = (root / "raw/stdout.bin").read_bytes()
        stderr = (root / "raw/stderr.bin").read_bytes()
        failures = [
            *R5.validate_spec(spec),
            *OLD_RUN.validate_selected_source(source),
            *R3.TOOLCHAIN.validate_toolchain_record(toolchain),
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
                require_eligible=True,
            ),
            *M2.validate_junit_projection(junit),
        ]
        cases = [_load(root, OLD_STORE.case_path(i)) for i in range(64)]
        failures.extend(
            M2.validate_case_records(cases, spec=spec, terminal=terminal, junit=junit)
        )
    if (
        failures
        or spec["implementation_revision"] != IMPLEMENTATION_REVISION
        or terminal["record_sha256"]
        != "c108edac40fae92e61c4c35eeb5264903c67b42e86a8a0e7d6e5c5590e69b47f"
        or junit["record_sha256"]
        != "38aa3325b66b41ff9333dcffd9ecc6fe4caf1f8877d7f9470b1a6fd9c52a6302"
        or junit["summary"]
        != {
            "official_cases": 64,
            "official_outcomes": 64,
            "official_passes": 64,
            "official_failures": 0,
        }
    ):
        raise R5DiagnosticError("; ".join(failures) or "R5 terminal/JUnit identity drift")
    return {
        "inventory": inventory,
        "spec": spec,
        "source": source,
        "terminal": terminal,
        "junit": junit,
        "cases": cases,
    }


def generated_projection(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    raw = validate_raw(root)
    before = {row["path"]: row for row in raw["source"]["files"]}
    after = {row["path"]: row for row in BASE.manifest_tree(WORK_SOURCE)}
    changed = [path for path, row in before.items() if after.get(path) != row]
    generated = [after[path] for path in sorted(set(after) - set(before))]
    expected = set(R3.declared_generated_paths()) - {FAILURE_LOG}
    if (
        changed
        or set(before) - set(after)
        or {row["path"] for row in generated} != expected
        or len(generated) != 123
        or sum(row["bytes"] for row in generated) != 950_304_539
        or BASE.domain_digest(GENERATED_DOMAIN, generated) != GENERATED_DIGEST
        or raw["junit"]["summary"]["official_failures"] != 0
    ):
        raise R5DiagnosticError("R5 live generated tree or conditional-log drift")
    retained = [
        row
        for row in generated
        if row["path"].endswith(".out.produced")
        or row["path"].startswith("build/release/Testing/Temporary/")
    ]
    metadata = [
        row
        for row in generated
        if row["path"].endswith(".c") or row["path"].endswith(".out")
    ]
    wrapper = [
        row for row in generated if row["path"] == "tests/with_stage1_test_env.sh"
    ]
    if (
        (len(retained), sum(r["bytes"] for r in retained)) != (66, 83_858)
        or (len(metadata), sum(r["bytes"] for r in metadata))
        != (56, 950_219_754)
        or len(wrapper) != 1
    ):
        raise R5DiagnosticError("R5 diagnostic assurance split drift")
    return raw | {
        "generated": generated,
        "retained": retained,
        "metadata": metadata,
        "wrapper": wrapper,
    }


def build_post(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    projection = generated_projection(root)
    return BASE.seal(
        {
            "schema": POST_SCHEMA,
            "attempt_id": R5.ATTEMPT_ID,
            "selected_attempt_consumed": True,
            "selected_outcome_credit": 0,
            "invalid_reason": "all-pass-failure-log-condition-not-preregistered",
            "junit_sha256": projection["junit"]["record_sha256"],
            "generated_files": projection["generated"],
            "generated_files_sha256": BASE.domain_digest(
                GENERATED_DOMAIN, projection["generated"]
            ),
            "conditionally_absent": [FAILURE_LOG],
            "retained_generated": [
                row | {"evidence_path": f"diagnostic/generated/{row['path']}"}
                for row in projection["retained"]
            ],
            "metadata_only_generated": projection["metadata"],
            "existing_wrapper": projection["wrapper"],
            "assurance": {
                "generated_count": 123,
                "retained_payload_count": 66,
                "metadata_only_count": 56,
                "wrapper_retained_as_existing_harness_artifact": True,
            },
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        POST_SCHEMA,
    )


def _diagnostic_inventory(root: Path) -> list[dict[str, Any]]:
    return [
        row
        for row in R3.R2_DIAGNOSTIC.portable_manifest(root)
        if row["path"].startswith("diagnostic/")
        and row["path"] != "diagnostic/completion.json"
    ]


def validate_post(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    raw = validate_raw(root)
    post = _load(root, "diagnostic/post.json")
    if not BASE.valid_seal(post, POST_SCHEMA):
        raise R5DiagnosticError("R5 diagnostic post seal drift")
    generated = post.get("generated_files")
    if not isinstance(generated, list):
        raise R5DiagnosticError("R5 diagnostic generated inventory is not a list")
    expected_paths = set(R3.declared_generated_paths()) - {FAILURE_LOG}
    retained = post.get("retained_generated")
    metadata = post.get("metadata_only_generated")
    wrapper = post.get("existing_wrapper")
    expected_retained = [
        row | {"evidence_path": f"diagnostic/generated/{row['path']}"}
        for row in generated
        if row["path"].endswith(".out.produced")
        or row["path"].startswith("build/release/Testing/Temporary/")
    ]
    expected_metadata = [
        row
        for row in generated
        if row["path"].endswith(".c") or row["path"].endswith(".out")
    ]
    expected_wrapper = [
        row
        for row in generated
        if row["path"] == "tests/with_stage1_test_env.sh"
    ]
    if (
        {row.get("path") for row in generated} != expected_paths
        or len(generated) != 123
        or sum(row.get("bytes", -1) for row in generated) != 950_304_539
        or BASE.domain_digest(GENERATED_DOMAIN, generated) != GENERATED_DIGEST
        or retained != expected_retained
        or metadata != expected_metadata
        or wrapper != expected_wrapper
        or (len(retained or []), sum(row["bytes"] for row in retained or []))
        != (66, 83_858)
        or len(metadata or []) != 56
        or len(wrapper or []) != 1
        or post.get("attempt_id") != R5.ATTEMPT_ID
        or post.get("selected_attempt_consumed") is not True
        or post.get("selected_outcome_credit") != 0
        or post.get("invalid_reason")
        != "all-pass-failure-log-condition-not-preregistered"
        or post.get("junit_sha256") != raw["junit"]["record_sha256"]
        or post.get("conditionally_absent") != [FAILURE_LOG]
        or post.get("credits") != M2.ZERO_TERMINAL_CREDITS
    ):
        raise R5DiagnosticError("R5 diagnostic post semantic drift")
    return raw | {
        "post": post,
        "generated": generated,
        "retained": retained,
        "metadata": metadata,
        "wrapper": wrapper,
    }


def build_completion(root: Path) -> dict[str, Any]:
    post = _load(root, "diagnostic/post.json")
    dependencies = _diagnostic_inventory(root)
    return BASE.seal(
        {
            "schema": COMPLETION_SCHEMA,
            "state": "complete-invalid-selected-attempt-diagnostic",
            "completion_installed_last": True,
            "raw_evidence_sha256": RAW_DIGEST,
            "post_sha256": post["record_sha256"],
            "dependencies": dependencies,
            "record_set_sha256": BASE.domain_digest(RECORD_SET_DOMAIN, dependencies),
            "selected_attempt_consumed": True,
            "official_outcomes": 0,
            "diagnostic_junit_rows": 64,
            "credits": dict(M2.ZERO_TERMINAL_CREDITS),
            "record_sha256": "",
        },
        COMPLETION_SCHEMA,
    )


def append(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    if (root / "diagnostic").exists():
        raise R5DiagnosticError("R5 diagnostic namespace already exists")
    projection = generated_projection(root)
    for row in projection["retained"]:
        BASE.install_bytes(
            root,
            f"diagnostic/generated/{row['path']}",
            (WORK_SOURCE / row["path"]).read_bytes(),
        )
    BASE.install_json(root, "diagnostic/post.json", build_post(root))
    completion = build_completion(root)
    BASE.install_json(root, "diagnostic/completion.json", completion)
    validate_completed(root, require_readonly=True)
    return completion


def validate_completed(
    root: Path = EVIDENCE_ROOT, *, require_readonly: bool = False
) -> dict[str, Any]:
    projection = validate_post(root)
    for row in projection["retained"]:
        path = root / row["evidence_path"]
        if (
            not path.is_file()
            or path.is_symlink()
            or _descriptor(row["path"], path.read_bytes())["sha256"]
            != row["sha256"]
        ):
            raise R5DiagnosticError(f"R5 retained diagnostic payload drift: {row['path']}")
    completion = _load(root, "diagnostic/completion.json")
    if completion != build_completion(root):
        raise R5DiagnosticError("R5 diagnostic completion drift")
    if require_readonly:
        BASE.validate_live_readonly_tree(root)
    return completion


def validate_offline_contract(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    if (root / "diagnostic/completion.json").is_file():
        completion = validate_completed(root)
        state = completion["state"]
    else:
        validate_raw(root)
        state = "incomplete-selected-attempt"
    return {
        "state": state,
        "selected_attempt_consumed": True,
        "diagnostic_junit_rows": 64,
        "official_outcomes": 0,
        "parity_credit": 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("offline-check", "prepare-check", "append", "validate")
    )
    args = parser.parse_args()
    try:
        if args.command == "offline-check":
            result = validate_offline_contract()
            print(
                f"LEAN_U2_M2_R5_DIAGNOSTIC|state={result['state']}|"
                "processes=0|outcomes=0|parity=0"
            )
        elif args.command == "prepare-check":
            result = generated_projection()
            print(
                "LEAN_U2_M2_R5_DIAGNOSTIC_PREPARED|generated=123|retained=66|"
                "metadata_only=56|processes=0|outcomes=0|parity=0|"
                f"junit={result['junit']['record_sha256']}"
            )
        elif args.command == "append":
            result = append()
            print(
                "LEAN_U2_M2_R5_DIAGNOSTIC_APPENDED|"
                f"completion={result['record_sha256']}|processes=0|"
                "outcomes=0|parity=0"
            )
        else:
            result = validate_completed()
            print(
                "LEAN_U2_M2_R5_DIAGNOSTIC_VALID|"
                f"completion={result['record_sha256']}|diagnostic_rows=64|"
                "outcomes=0|parity=0"
            )
    except (
        BASE.U2ExecutionError,
        BASE.STORE.CheckpointConflict,
        M2.M2ContractError,
        OLD_RUN.M2RunError,
        R3.R3Error,
        R5.R5Error,
        R5DiagnosticError,
    ) as error:
        print(f"LEAN_U2_M2_R5_DIAGNOSTIC_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
