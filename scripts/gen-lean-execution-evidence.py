#!/usr/bin/env python3
"""Validate and render the TL0.7 Lean execution-evidence contract.

This module deliberately contains no process launcher.  TL0.7.1 defines the
machine contract and validates synthetic representation controls only.  Real
process observations belong to TL0.7.2 and later and cannot be created or
credited by this program.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-execution-evidence-v1.json"
OUT_JSON = ROOT / "docs" / "plan" / "generated" / "lean-execution-evidence.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-execution-evidence.md"

SCHEMA = "axeyum-lean-execution-evidence-v1"
BUNDLE_SCHEMA = "axeyum-lean-execution-bundle-v1"
PLAN_COMMIT = "ff8f8dd4b71c3c488ce53229f4301527d5e9d360"
HEX64 = re.compile(r"^[0-9a-f]{64}$")
ID = re.compile(r"^[a-z0-9]+(?:[.-][a-z0-9]+)*$")

SOURCE_INPUTS = (
    (
        "docs/plan/lean-execution-evidence-tl0.7-plan-2026-07-22.md",
        "0f38bb7944de77a0df28d122c9c1190af3865c8ecc9778cc243135df191f0c37",
        "preregistered-current-file",
    ),
    (
        "docs/plan/lean-u2-official-ci-profiles-v1.json",
        "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548",
        "current-file",
    ),
    (
        "docs/plan/lean-complete-parity-v1.json",
        "f2fc71509b4f557265a853ebb7666071b7b67d8553c0951ae1f91b736059ab78",
        "preregistered-baseline",
    ),
    (
        "scripts/mem-run.sh",
        "25740241696f08480874e7b63214d62cfdf24eef766a3169c59b3af788498c63",
        "current-file",
    ),
    (
        "docs/research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md",
        "3faef4ae21a1b61739812c524d76f1efc2d7e473b1a59d7d3921594ec0a475ed",
        "current-file",
    ),
    (
        "docs/research/09-decisions/adr-0345-preregister-lean-system-interoperability.md",
        "7af3ba0c11dd320d2ad9859dd5cac1ba06a25c26e5fee6670095d7fe51386a0a",
        "current-file",
    ),
    (
        "docs/plan/lean-system-implementation-plan-2026-07-21.md",
        "1e23a4e77be3c4ee348b7c19f88511254045ae17a53c102a5f64ba9384981de4",
        "preregistered-baseline",
    ),
)

TERMINATION_CLASSES = (
    "exited",
    "signaled",
    "wall-timeout",
    "cpu-timeout",
    "memory-limit",
    "pids-limit",
    "disk-limit",
    "cancelled",
    "runner-lost",
    "launch-failed",
    "preflight-invalid",
    "unknown-termination",
)
CASE_OUTCOMES = ("passed", "failed", "skipped", "not-run", "invalid-run")
METRIC_STATES = ("observed", "not-observed", "not-enforced")
ARTIFACT_KINDS = ("stdout", "stderr", "junit", "diagnostic", "controller")

RUN_FIELDS = (
    "id",
    "lane_id",
    "system_profile",
    "credit_class",
    "source_sha256",
    "executable_sha256",
    "configuration_sha256",
    "command",
    "command_sha256",
    "working_directory",
    "environment",
    "environment_sha256",
    "selection_set_id",
    "selection_case_ids",
    "selection_sha256",
    "resource_envelope",
    "resource_envelope_sha256",
    "platform",
    "platform_sha256",
    "artifact_policy",
    "artifact_policy_sha256",
    "identity_sha256",
)
ATTEMPT_FIELDS = (
    "id",
    "run_id",
    "sequence",
    "recorded_before_launch",
    "assigned_case_ids",
    "terminal",
    "artifact_ids",
    "sha256",
)
TERMINAL_FIELDS = (
    "class",
    "exit_code",
    "signal",
    "events",
    "wall_time_ms",
    "cpu_time_ms",
    "peak_rss_bytes",
    "metric_state",
)
CASE_FIELDS = (
    "id",
    "run_id",
    "attempt_id",
    "selection_set_id",
    "outcome",
    "junit_name",
    "artifact_ids",
    "sha256",
)
ARTIFACT_FIELDS = (
    "id",
    "kind",
    "sha256",
    "bytes",
    "provider",
    "provider_artifact_id",
    "expires_at",
    "durable_copy",
    "record_sha256",
)
COMPLETION_FIELDS = (
    "run_id",
    "state",
    "attempt_ids",
    "terminal_less_attempt_ids",
    "case_ids",
    "case_records_sha256",
    "artifact_ids",
    "artifact_records_sha256",
    "installed_last",
    "sha256",
)

CREDIT_FIELDS = (
    "real_runs",
    "executed_attempts",
    "completed_cases",
    "official_outcomes",
    "axeyum_outcomes",
    "paired_cells",
    "performance_rows",
)

MUTATION_CLASSES = (
    ("source-identity-drift", "source, schema, producer, or preregistration identity drift"),
    ("lane-policy-drift", "lane cap, concurrency, purpose, enforcement, or credit-class drift"),
    ("implicit-wrapper-default", "64 GiB wrapper default presented as an explicit 4/8 GiB lane"),
    ("malformed-resource", "missing, zero, unitless, or contradictory resource field"),
    ("runner-substitution", "runner label substituted without actual platform identity"),
    ("run-identity-drift", "command, environment, directory, selection, or resource change under one run ID"),
    ("attempt-closure", "attempt omission, duplication, sequence drift, or invalid assignment overlap"),
    ("guessed-termination", "OOM, timeout, or signal class without matching evidence"),
    ("case-closure", "missing, duplicate, unexpected, reordered, or identity-drifted case"),
    ("case-attribution", "case attributed to the wrong attempt or selection set"),
    ("artifact-identity", "stdout, stderr, JUnit, diagnostic, or controller hash/size drift"),
    ("sidecar-only-completion", "JUnit or provider conclusion substituted for case closure"),
    ("artifact-retention", "provider artifact lacks expiry and durable-copy identity"),
    ("checkpoint-conflict", "duplicate, overwritten, conflicting, or self-hash-reused checkpoint"),
    ("completion-order", "completion installed early or names a wrong record-set digest"),
    ("lost-attempt", "resumed completion omits an earlier terminal-less attempt"),
    ("incomplete-credit", "incomplete or invalid bundle receives result, denominator, performance, or parity credit"),
    ("profile-promotion", "adapter/export evidence promoted to native-system credit"),
    ("contract-outcome", "contract-only authority carries a real outcome or terminal promotion"),
)

SYNTHETIC_CONTROLS = (
    ("clean-complete", "two passed cases and completion-last closure"),
    ("failed-case-complete", "one passed and one failed case retained in a complete run"),
    ("interrupted-resumed", "terminal-less first attempt retained beside a completing retry"),
    ("incomplete", "partial diagnostic bundle with no completion or credit"),
    ("preflight-invalid", "preflight-invalid attempt with no launched cases or credit"),
)


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=False) + "\n"


def object_digest(value: dict[str, Any], hash_field: str) -> str:
    return digest({key: item for key, item in value.items() if key != hash_field})


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def lane_policies() -> list[dict[str, Any]]:
    return [
        {
            "id": "standard-local-4g",
            "purpose": "bounded local development and contract evidence",
            "producer_class": "local-process",
            "memory_limit_bytes": 4_294_967_296,
            "memory_scope": "per-process-address-space",
            "memory_enforcement": "explicit-rlimit-as",
            "required_mem_limit_gb": 4,
            "worker_limit": 2,
            "durability_class": "contract-only-until-tl0.7.3",
            "credit_class": "development-only",
        },
        {
            "id": "official-export-8g",
            "purpose": "bounded official Lean exporter adapter",
            "producer_class": "official-adapter-process",
            "memory_limit_bytes": 8_589_934_592,
            "memory_scope": "per-process-address-space",
            "memory_enforcement": "explicit-rlimit-as",
            "required_mem_limit_gb": 8,
            "worker_limit": 1,
            "durability_class": "contract-only-until-tl0.7.3",
            "credit_class": "adapter-export-only",
        },
    ]


def build_authority() -> dict[str, Any]:
    return {
        "schema": SCHEMA,
        "as_of": "2026-07-22",
        "scope": "execution-evidence-contract-only-no-process-or-parity-outcome",
        "preregistration": {
            "commit": PLAN_COMMIT,
            "published_before_implementation": True,
            "plan_sha256": SOURCE_INPUTS[0][1],
        },
        "source_inputs": [
            {"path": path, "sha256": sha256, "binding": binding}
            for path, sha256, binding in SOURCE_INPUTS
        ],
        "lane_policies": lane_policies(),
        "taxonomies": {
            "termination_classes": list(TERMINATION_CLASSES),
            "case_outcomes": list(CASE_OUTCOMES),
            "metric_states": list(METRIC_STATES),
            "artifact_kinds": list(ARTIFACT_KINDS),
        },
        "record_contracts": {
            "run": list(RUN_FIELDS),
            "attempt": list(ATTEMPT_FIELDS),
            "attempt_terminal": list(TERMINAL_FIELDS),
            "case": list(CASE_FIELDS),
            "artifact": list(ARTIFACT_FIELDS),
            "completion": list(COMPLETION_FIELDS),
            "credits": list(CREDIT_FIELDS),
        },
        "checkpoint_policy": {
            "canonical_json": True,
            "self_hashes": True,
            "temporary_same_directory": True,
            "flush_and_fsync_file": True,
            "atomic_install": True,
            "fsync_directory": True,
            "overwrite_existing": False,
            "duplicate_is_conflict": True,
            "resume_skips_only_valid_record": True,
            "completion_installed_last": True,
            "junit_is_sidecar_not_authority": True,
            "ctest_failover_is_not_checkpoint_authority": True,
        },
        "credit_predicates": [
            "prelaunch-run-identity-required",
            "all-and-only-assigned-cases-required",
            "raw-artifact-and-case-record-required",
            "resource-classification-requires-enforcement-evidence",
            "all-attempts-including-terminal-less-accounted",
            "actual-platform-identity-required",
            "matched-effective-resources-required-for-performance",
            "adapter-evidence-cannot-fill-native-profile",
            "incomplete-or-invalid-zero-credit",
            "synthetic-controls-zero-credit",
        ],
        "synthetic_controls": [
            {"id": control_id, "detail": detail}
            for control_id, detail in SYNTHETIC_CONTROLS
        ],
        "mutation_classes": [
            {"id": mutation_id, "detail": detail}
            for mutation_id, detail in MUTATION_CLASSES
        ],
        "observed": {field: 0 for field in CREDIT_FIELDS},
        "milestones": [
            {"id": "TL0.7.1", "state": "contract-only"},
            {"id": "TL0.7.2", "state": "not-run"},
            {"id": "TL0.7.3", "state": "not-run"},
            {"id": "TL0.7.4", "state": "not-run"},
            {"id": "TL0.6.3", "state": "blocked-on-tl0.7"},
        ],
        "residual": [
            "Implement forced process exit, signal, timeout, and evidence-backed limit capture in TL0.7.2.",
            "Prove immutable filesystem checkpoints, conflict handling, kill/resume, and completion-last publication in TL0.7.3.",
            "Run no-credit pinned-Lean and official-export controls in TL0.7.4 before any U2 execution.",
        ],
    }


def validate_authority(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    expected = build_authority()
    if data.get("schema") != SCHEMA:
        failures.append("schema identity drift")
    if data.get("preregistration") != expected["preregistration"]:
        failures.append("preregistration identity/order drift")
    if data.get("source_inputs") != expected["source_inputs"]:
        failures.append("source input identity/order drift")
    for source in expected["source_inputs"]:
        if source["binding"] not in {"current-file", "preregistered-current-file"}:
            continue
        path = ROOT / source["path"]
        if not path.is_file():
            failures.append(f"missing bound source {source['path']}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
            failures.append(f"bound source bytes drifted for {source['path']}")
    if data.get("lane_policies") != expected["lane_policies"]:
        failures.append("lane policy identity/order drift")
    if data.get("taxonomies") != expected["taxonomies"]:
        failures.append("execution taxonomy identity/order drift")
    if data.get("record_contracts") != expected["record_contracts"]:
        failures.append("record contract fields/order drift")
    if data.get("checkpoint_policy") != expected["checkpoint_policy"]:
        failures.append("checkpoint policy drift")
    if data.get("credit_predicates") != expected["credit_predicates"]:
        failures.append("credit predicates/order drift")
    if data.get("synthetic_controls") != expected["synthetic_controls"]:
        failures.append("synthetic control register drift")
    if data.get("mutation_classes") != expected["mutation_classes"]:
        failures.append("mutation register drift")
    if data.get("observed") != {field: 0 for field in CREDIT_FIELDS}:
        failures.append("contract-only authority cannot claim real outcomes")
    if data.get("milestones") != expected["milestones"]:
        failures.append("milestone boundary drift")
    if data.get("scope") != expected["scope"] or data.get("residual") != expected["residual"]:
        failures.append("scope/residual drift")
    if set(data) != set(expected):
        failures.append("top-level authority fields must be exact")
    return failures


def metric(state: str, value: int | None, unit: str) -> dict[str, Any]:
    return {"state": state, "value": value, "unit": unit}


def base_resource_envelope(lane_id: str = "standard-local-4g") -> dict[str, Any]:
    lane = next(item for item in lane_policies() if item["id"] == lane_id)
    return {
        "lane_id": lane_id,
        "memory_limit": metric("observed", lane["memory_limit_bytes"], "bytes"),
        "memory_scope": lane["memory_scope"],
        "memory_enforcement": lane["memory_enforcement"],
        "explicit_mem_limit_gb": lane["required_mem_limit_gb"],
        "wall_timeout": metric("observed", 60, "seconds"),
        "cpu_time_limit": metric("not-enforced", None, "seconds"),
        "worker_limit": metric("observed", 1, "workers"),
        "thread_limit": metric("observed", 1, "threads"),
        "process_limit": metric("not-enforced", None, "processes"),
        "pids_limit": metric("not-enforced", None, "pids"),
        "swap_limit": metric("not-enforced", None, "bytes"),
        "disk_limit": metric("not-enforced", None, "bytes"),
        "open_file_limit": metric("not-observed", None, "files"),
        "requested_parallelism": 1,
        "effective_parallelism": 1,
        "enforcement_artifact_ids": ["controller-main"],
    }


def platform() -> dict[str, Any]:
    return {
        "provider": "synthetic-provider",
        "runner_label": "synthetic-linux-x86-64",
        "runner_id": "synthetic-runner-001",
        "os": "synthetic-linux",
        "architecture": "x86_64",
        "kernel": "synthetic-kernel",
        "image": "synthetic-image-v1",
        "cpu": "synthetic-cpu-1",
        "memory_bytes": 8_589_934_592,
        "filesystem": "synthetic-fs",
    }


def artifact_policy() -> dict[str, Any]:
    return {
        "canonical_json": True,
        "content_addressed": True,
        "provider_retention_recorded": True,
        "durable_copy_required": True,
        "completion_installed_last": True,
    }


def make_run(case_ids: list[str], lane_id: str = "standard-local-4g") -> dict[str, Any]:
    environment = {"LANG": "C.UTF-8", "NPROC": "1", "SYNTHETIC": "1"}
    command = ["synthetic-lean-runner", "--contract-only"]
    resources = base_resource_envelope(lane_id)
    actual_platform = platform()
    policy = artifact_policy()
    run: dict[str, Any] = {
        "id": "synthetic-run",
        "lane_id": lane_id,
        "system_profile": "synthetic-contract-control",
        "credit_class": "synthetic-no-credit",
        "source_sha256": digest("synthetic-source"),
        "executable_sha256": digest("synthetic-executable"),
        "configuration_sha256": digest("synthetic-configuration"),
        "command": command,
        "command_sha256": digest(command),
        "working_directory": "/synthetic/work",
        "environment": environment,
        "environment_sha256": digest(environment),
        "selection_set_id": "synthetic-selection",
        "selection_case_ids": case_ids,
        "selection_sha256": digest(case_ids),
        "resource_envelope": resources,
        "resource_envelope_sha256": digest(resources),
        "platform": actual_platform,
        "platform_sha256": digest(actual_platform),
        "artifact_policy": policy,
        "artifact_policy_sha256": digest(policy),
        "identity_sha256": "",
    }
    run["identity_sha256"] = object_digest(run, "identity_sha256")
    return run


def make_artifact(
    artifact_id: str,
    kind: str,
    *,
    provider: bool = False,
) -> dict[str, Any]:
    payload_sha = digest({"artifact": artifact_id, "kind": kind})
    row: dict[str, Any] = {
        "id": artifact_id,
        "kind": kind,
        "sha256": payload_sha,
        "bytes": len(artifact_id) + len(kind),
        "provider": "synthetic-provider" if provider else None,
        "provider_artifact_id": f"provider-{artifact_id}" if provider else None,
        "expires_at": "2099-01-01T00:00:00Z" if provider else None,
        "durable_copy": {
            "state": "complete",
            "uri": f"content://sha256/{payload_sha}",
            "sha256": payload_sha,
        },
        "record_sha256": "",
    }
    row["record_sha256"] = object_digest(row, "record_sha256")
    return row


def terminal(
    termination_class: str = "exited",
    *,
    exit_code: int | None = 0,
    signal: int | None = None,
    events: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "class": termination_class,
        "exit_code": exit_code,
        "signal": signal,
        "events": events if events is not None else ["exit-status-observed"],
        "wall_time_ms": 10,
        "cpu_time_ms": 5,
        "peak_rss_bytes": 1_048_576,
        "metric_state": "observed",
    }


def make_attempt(
    attempt_id: str,
    sequence: int,
    case_ids: list[str],
    terminal_record: dict[str, Any] | None,
    artifact_ids: list[str],
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "id": attempt_id,
        "run_id": "synthetic-run",
        "sequence": sequence,
        "recorded_before_launch": True,
        "assigned_case_ids": case_ids,
        "terminal": terminal_record,
        "artifact_ids": artifact_ids,
        "sha256": "",
    }
    row["sha256"] = object_digest(row, "sha256")
    return row


def make_case(case_id: str, attempt_id: str, outcome: str, artifacts: list[str]) -> dict[str, Any]:
    row: dict[str, Any] = {
        "id": case_id,
        "run_id": "synthetic-run",
        "attempt_id": attempt_id,
        "selection_set_id": "synthetic-selection",
        "outcome": outcome,
        "junit_name": case_id,
        "artifact_ids": artifacts,
        "sha256": "",
    }
    row["sha256"] = object_digest(row, "sha256")
    return row


def make_completion(
    attempts: list[dict[str, Any]],
    cases: list[dict[str, Any]],
    artifacts: list[dict[str, Any]],
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "run_id": "synthetic-run",
        "state": "complete",
        "attempt_ids": [item["id"] for item in attempts],
        "terminal_less_attempt_ids": [
            item["id"] for item in attempts if item["terminal"] is None
        ],
        "case_ids": [item["id"] for item in cases],
        "case_records_sha256": digest(cases),
        "artifact_ids": [item["id"] for item in artifacts],
        "artifact_records_sha256": digest(artifacts),
        "installed_last": True,
        "sha256": "",
    }
    row["sha256"] = object_digest(row, "sha256")
    return row


def zero_credits() -> dict[str, int]:
    return {field: 0 for field in CREDIT_FIELDS}


def synthetic_bundle(control_id: str) -> dict[str, Any]:
    if control_id not in {item[0] for item in SYNTHETIC_CONTROLS}:
        raise ValueError(f"unknown synthetic control {control_id}")
    case_ids = ["case-a", "case-b"]
    run = make_run(case_ids)
    artifacts = sorted(
        [
        make_artifact("controller-main", "controller"),
        make_artifact("stdout-main", "stdout"),
        make_artifact("stderr-main", "stderr"),
        make_artifact("junit-main", "junit", provider=True),
        ],
        key=lambda item: item["id"],
    )
    attempts: list[dict[str, Any]]
    cases: list[dict[str, Any]]
    completion: dict[str, Any] | None
    if control_id == "interrupted-resumed":
        attempts = [
            make_attempt("attempt-001", 1, case_ids, None, []),
            make_attempt(
                "attempt-002",
                2,
                case_ids,
                terminal(),
                ["controller-main", "junit-main", "stderr-main", "stdout-main"],
            ),
        ]
        cases = [
            make_case("case-a", "attempt-002", "passed", ["junit-main", "stdout-main"]),
            make_case("case-b", "attempt-002", "passed", ["junit-main", "stdout-main"]),
        ]
        completion = make_completion(attempts, cases, artifacts)
    elif control_id == "incomplete":
        attempts = [
            make_attempt(
                "attempt-001",
                1,
                case_ids,
                terminal("cancelled", exit_code=None, events=["cancellation-observed"]),
                ["controller-main", "stderr-main", "stdout-main"],
            )
        ]
        cases = [
            make_case("case-a", "attempt-001", "not-run", ["stdout-main"]),
        ]
        completion = None
    elif control_id == "preflight-invalid":
        attempts = [
            make_attempt(
                "attempt-001",
                1,
                [],
                terminal(
                    "preflight-invalid",
                    exit_code=None,
                    events=["preflight-rejected"],
                ),
                ["controller-main", "stderr-main"],
            )
        ]
        cases = []
        completion = None
    else:
        attempts = [
            make_attempt(
                "attempt-001",
                1,
                case_ids,
                terminal(),
                ["controller-main", "junit-main", "stderr-main", "stdout-main"],
            )
        ]
        outcomes = ["passed", "failed"] if control_id == "failed-case-complete" else ["passed", "passed"]
        cases = [
            make_case(case_id, "attempt-001", outcome, ["junit-main", "stdout-main"])
            for case_id, outcome in zip(case_ids, outcomes, strict=True)
        ]
        completion = make_completion(attempts, cases, artifacts)
    return {
        "schema": BUNDLE_SCHEMA,
        "synthetic": True,
        "control_id": control_id,
        "run": run,
        "attempts": attempts,
        "cases": cases,
        "artifacts": artifacts,
        "completion": completion,
        "credits": zero_credits(),
    }


def validate_metric(name: str, value: Any, failures: list[str]) -> None:
    if not isinstance(value, dict) or set(value) != {"state", "value", "unit"}:
        failures.append(f"{name}: metric fields must be exact")
        return
    state = value.get("state")
    number = value.get("value")
    if state not in METRIC_STATES:
        failures.append(f"{name}: invalid metric state")
    if not isinstance(value.get("unit"), str) or not value["unit"]:
        failures.append(f"{name}: unit is required")
    if state == "observed":
        if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
            failures.append(f"{name}: observed metric must be a positive integer")
    elif number is not None:
        failures.append(f"{name}: unobserved/unenforced metric value must be null")


def validate_resource_envelope(run: dict[str, Any], lanes: dict[str, dict[str, Any]], failures: list[str]) -> None:
    envelope = run.get("resource_envelope")
    if not isinstance(envelope, dict):
        failures.append("run: resource envelope must be an object")
        return
    expected_fields = {
        "lane_id",
        "memory_limit",
        "memory_scope",
        "memory_enforcement",
        "explicit_mem_limit_gb",
        "wall_timeout",
        "cpu_time_limit",
        "worker_limit",
        "thread_limit",
        "process_limit",
        "pids_limit",
        "swap_limit",
        "disk_limit",
        "open_file_limit",
        "requested_parallelism",
        "effective_parallelism",
        "enforcement_artifact_ids",
    }
    if set(envelope) != expected_fields:
        failures.append("run: resource envelope fields must be exact")
    lane = lanes.get(str(run.get("lane_id")))
    if lane is None or envelope.get("lane_id") != run.get("lane_id"):
        failures.append("run: unknown or mismatched lane")
        return
    for field in (
        "memory_limit",
        "wall_timeout",
        "cpu_time_limit",
        "worker_limit",
        "thread_limit",
        "process_limit",
        "pids_limit",
        "swap_limit",
        "disk_limit",
        "open_file_limit",
    ):
        validate_metric("run.resource." + field, envelope.get(field), failures)
    if envelope.get("memory_limit", {}).get("value") != lane["memory_limit_bytes"]:
        failures.append("run: memory limit does not instantiate lane policy")
    if envelope.get("memory_scope") != lane["memory_scope"]:
        failures.append("run: memory scope drift")
    if envelope.get("memory_enforcement") != lane["memory_enforcement"]:
        failures.append("run: memory enforcement drift")
    if envelope.get("explicit_mem_limit_gb") != lane["required_mem_limit_gb"]:
        failures.append("run: explicit MEM_LIMIT_GB does not instantiate lane")
    if envelope.get("worker_limit", {}).get("value", lane["worker_limit"] + 1) > lane["worker_limit"]:
        failures.append("run: worker limit exceeds lane policy")
    for field in ("requested_parallelism", "effective_parallelism"):
        value = envelope.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            failures.append(f"run: {field} must be a positive integer")
    ids = envelope.get("enforcement_artifact_ids")
    if not isinstance(ids, list) or not ids:
        failures.append("run: enforcement artifact identity is required")


def validate_terminal(attempt_id: str, value: Any, failures: list[str]) -> None:
    if value is None:
        return
    if not isinstance(value, dict) or set(value) != set(TERMINAL_FIELDS):
        failures.append(f"{attempt_id}: terminal fields must be exact")
        return
    termination = value.get("class")
    events = value.get("events")
    if termination not in TERMINATION_CLASSES:
        failures.append(f"{attempt_id}: unknown termination class")
    if (
        not isinstance(events, list)
        or not events
        or not all(isinstance(item, str) and item for item in events)
    ):
        failures.append(f"{attempt_id}: termination events must be non-empty strings")
        events = []
    exit_code = value.get("exit_code")
    signal = value.get("signal")
    if termination == "exited":
        if not isinstance(exit_code, int) or isinstance(exit_code, bool) or signal is not None:
            failures.append(f"{attempt_id}: exited requires exit code and no signal")
        if "exit-status-observed" not in events:
            failures.append(f"{attempt_id}: exited lacks exit-status evidence")
    elif termination == "signaled":
        if exit_code is not None or not isinstance(signal, int) or signal <= 0:
            failures.append(f"{attempt_id}: signaled requires signal and no exit code")
        if "signal-observed" not in events:
            failures.append(f"{attempt_id}: signaled lacks signal evidence")
    elif termination in {"wall-timeout", "cpu-timeout", "memory-limit", "pids-limit", "disk-limit"}:
        required = termination + "-observed"
        if required not in events:
            failures.append(f"{attempt_id}: {termination} lacks enforcement evidence")
    for field in ("wall_time_ms", "cpu_time_ms", "peak_rss_bytes"):
        number = value.get(field)
        if not isinstance(number, int) or isinstance(number, bool) or number < 0:
            failures.append(f"{attempt_id}: {field} must be non-negative")
    if value.get("metric_state") not in METRIC_STATES:
        failures.append(f"{attempt_id}: invalid terminal metric state")


def validate_bundle(bundle: dict[str, Any], authority: dict[str, Any] | None = None) -> list[str]:
    failures: list[str] = []
    authority = authority or build_authority()
    if validate_authority(authority):
        return ["authority invalid before bundle validation"]
    expected_top = {"schema", "synthetic", "control_id", "run", "attempts", "cases", "artifacts", "completion", "credits"}
    if set(bundle) != expected_top:
        failures.append("bundle top-level fields must be exact")
    if bundle.get("schema") != BUNDLE_SCHEMA or bundle.get("synthetic") is not True:
        failures.append("TL0.7.1 accepts synthetic bundle schema only")
    if bundle.get("control_id") not in {item[0] for item in SYNTHETIC_CONTROLS}:
        failures.append("unknown synthetic control id")

    run = bundle.get("run")
    if not isinstance(run, dict) or set(run) != set(RUN_FIELDS):
        failures.append("run fields must be exact")
        return failures
    for field in ("source_sha256", "executable_sha256", "configuration_sha256", "command_sha256", "environment_sha256", "selection_sha256", "resource_envelope_sha256", "platform_sha256", "artifact_policy_sha256", "identity_sha256"):
        if not HEX64.fullmatch(str(run.get(field, ""))):
            failures.append(f"run: {field} must be lowercase 64-hex")
    if not ID.fullmatch(str(run.get("id", ""))):
        failures.append("run: invalid id")
    if run.get("command_sha256") != digest(run.get("command")):
        failures.append("run: command identity drift")
    if run.get("environment_sha256") != digest(run.get("environment")):
        failures.append("run: environment identity drift")
    selection = run.get("selection_case_ids")
    if not isinstance(selection, list) or selection != sorted(set(selection)):
        failures.append("run: selection case ids must be unique and sorted")
        selection = []
    if run.get("selection_sha256") != digest(selection):
        failures.append("run: selection identity drift")
    if run.get("resource_envelope_sha256") != digest(run.get("resource_envelope")):
        failures.append("run: resource identity drift")
    if run.get("platform_sha256") != digest(run.get("platform")):
        failures.append("run: platform identity drift")
    if run.get("artifact_policy_sha256") != digest(run.get("artifact_policy")):
        failures.append("run: artifact-policy identity drift")
    if run.get("identity_sha256") != object_digest(run, "identity_sha256"):
        failures.append("run: complete run identity drift")
    if run.get("credit_class") != "synthetic-no-credit" or run.get("system_profile") != "synthetic-contract-control":
        failures.append("synthetic bundle cannot promote adapter or native profile credit")
    actual_platform = run.get("platform")
    platform_fields = {"provider", "runner_label", "runner_id", "os", "architecture", "kernel", "image", "cpu", "memory_bytes", "filesystem"}
    if not isinstance(actual_platform, dict) or set(actual_platform) != platform_fields:
        failures.append("run: actual platform fields must be exact")
    elif any(value in (None, "") for value in actual_platform.values()):
        failures.append("run: runner label cannot substitute for actual platform identity")
    validate_resource_envelope(run, {item["id"]: item for item in authority["lane_policies"]}, failures)

    artifacts = bundle.get("artifacts")
    if not isinstance(artifacts, list):
        failures.append("artifacts must be a list")
        artifacts = []
    artifact_ids = [item.get("id") for item in artifacts if isinstance(item, dict)]
    if artifact_ids != sorted(artifact_ids) or len(artifact_ids) != len(set(artifact_ids)):
        failures.append("artifact ids must be unique and sorted")
    artifact_map: dict[str, dict[str, Any]] = {}
    for artifact in artifacts:
        if not isinstance(artifact, dict) or set(artifact) != set(ARTIFACT_FIELDS):
            failures.append("artifact fields must be exact")
            continue
        artifact_id = str(artifact.get("id", "<artifact>"))
        artifact_map[artifact_id] = artifact
        if artifact.get("kind") not in ARTIFACT_KINDS:
            failures.append(f"{artifact_id}: invalid artifact kind")
        if not HEX64.fullmatch(str(artifact.get("sha256", ""))):
            failures.append(f"{artifact_id}: invalid content hash")
        if not isinstance(artifact.get("bytes"), int) or artifact["bytes"] < 0:
            failures.append(f"{artifact_id}: invalid byte size")
        durable = artifact.get("durable_copy")
        if not isinstance(durable, dict) or set(durable) != {"state", "uri", "sha256"} or durable.get("state") != "complete" or durable.get("sha256") != artifact.get("sha256"):
            failures.append(f"{artifact_id}: durable copy identity is incomplete")
        if artifact.get("provider") is not None and (
            not artifact.get("provider_artifact_id") or not artifact.get("expires_at")
        ):
            failures.append(f"{artifact_id}: provider retention/expiry identity is required")
        if artifact.get("record_sha256") != object_digest(artifact, "record_sha256"):
            failures.append(f"{artifact_id}: artifact record hash drift")

    attempts = bundle.get("attempts")
    if not isinstance(attempts, list):
        failures.append("attempts must be a list")
        attempts = []
    attempt_ids = [item.get("id") for item in attempts if isinstance(item, dict)]
    if attempt_ids != sorted(attempt_ids) or len(attempt_ids) != len(set(attempt_ids)):
        failures.append("attempt ids must be unique and sorted")
    sequences = [item.get("sequence") for item in attempts if isinstance(item, dict)]
    if sequences != list(range(1, len(attempts) + 1)):
        failures.append("attempt sequences must be contiguous and ordered")
    attempt_map: dict[str, dict[str, Any]] = {}
    for attempt in attempts:
        if not isinstance(attempt, dict) or set(attempt) != set(ATTEMPT_FIELDS):
            failures.append("attempt fields must be exact")
            continue
        attempt_id = str(attempt.get("id", "<attempt>"))
        attempt_map[attempt_id] = attempt
        if attempt.get("run_id") != run.get("id"):
            failures.append(f"{attempt_id}: run attribution drift")
        if attempt.get("recorded_before_launch") is not True:
            failures.append(f"{attempt_id}: attempt was not recorded before launch")
        assigned = attempt.get("assigned_case_ids")
        if not isinstance(assigned, list) or assigned != sorted(set(assigned)) or not set(assigned).issubset(selection):
            failures.append(f"{attempt_id}: invalid case assignment")
        validate_terminal(attempt_id, attempt.get("terminal"), failures)
        refs = attempt.get("artifact_ids")
        if not isinstance(refs, list) or refs != sorted(set(refs)) or not set(refs).issubset(artifact_map):
            failures.append(f"{attempt_id}: invalid artifact references")
        if attempt.get("sha256") != object_digest(attempt, "sha256"):
            failures.append(f"{attempt_id}: attempt record hash drift")

    cases = bundle.get("cases")
    if not isinstance(cases, list):
        failures.append("cases must be a list")
        cases = []
    case_ids = [item.get("id") for item in cases if isinstance(item, dict)]
    if case_ids != sorted(case_ids) or len(case_ids) != len(set(case_ids)):
        failures.append("case ids must be unique and sorted")
    for case in cases:
        if not isinstance(case, dict) or set(case) != set(CASE_FIELDS):
            failures.append("case fields must be exact")
            continue
        case_id = str(case.get("id", "<case>"))
        if case_id not in selection:
            failures.append(f"{case_id}: unexpected case identity")
        if case.get("run_id") != run.get("id") or case.get("selection_set_id") != run.get("selection_set_id"):
            failures.append(f"{case_id}: run/selection attribution drift")
        attempt = attempt_map.get(str(case.get("attempt_id")))
        if attempt is None or attempt.get("terminal") is None or case_id not in attempt.get("assigned_case_ids", []):
            failures.append(f"{case_id}: invalid attempt attribution")
        if case.get("outcome") not in CASE_OUTCOMES:
            failures.append(f"{case_id}: invalid case outcome")
        refs = case.get("artifact_ids")
        if not isinstance(refs, list) or refs != sorted(set(refs)) or not set(refs).issubset(artifact_map):
            failures.append(f"{case_id}: invalid artifact references")
        if case.get("sha256") != object_digest(case, "sha256"):
            failures.append(f"{case_id}: case record hash drift")

    completion = bundle.get("completion")
    if completion is not None:
        if not isinstance(completion, dict) or set(completion) != set(COMPLETION_FIELDS):
            failures.append("completion fields must be exact")
        else:
            if completion.get("run_id") != run.get("id") or completion.get("state") != "complete":
                failures.append("completion run/state drift")
            if completion.get("attempt_ids") != attempt_ids:
                failures.append("completion attempt closure drift")
            terminal_less = [item["id"] for item in attempts if item.get("terminal") is None]
            if completion.get("terminal_less_attempt_ids") != terminal_less:
                failures.append("completion omits or invents terminal-less attempt")
            if completion.get("case_ids") != selection or case_ids != selection:
                failures.append("completion requires all and only selected case records")
            if completion.get("case_records_sha256") != digest(cases):
                failures.append("completion case-record-set digest drift")
            if completion.get("artifact_ids") != artifact_ids or completion.get("artifact_records_sha256") != digest(artifacts):
                failures.append("completion artifact closure/digest drift")
            if completion.get("installed_last") is not True:
                failures.append("completion must be installed last")
            if completion.get("sha256") != object_digest(completion, "sha256"):
                failures.append("completion record hash drift")
    elif bundle.get("control_id") in {"clean-complete", "failed-case-complete", "interrupted-resumed"}:
        failures.append("complete synthetic control requires completion record")

    if bundle.get("credits") != zero_credits():
        failures.append("synthetic/incomplete contract bundle cannot receive execution or parity credit")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    controls = []
    for control in data["synthetic_controls"]:
        failures = validate_bundle(synthetic_bundle(control["id"]), data)
        controls.append(
            {
                "id": control["id"],
                "detail": control["detail"],
                "valid": not failures,
                "failures": failures,
            }
        )
    return {
        "schema": "axeyum-lean-execution-evidence-report-v1",
        "generated_from": "docs/plan/lean-execution-evidence-v1.json",
        "generated_from_sha256": hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),
        "scope": data["scope"],
        "preregistration": data["preregistration"],
        "lane_policies": data["lane_policies"],
        "termination_classes": data["taxonomies"]["termination_classes"],
        "record_field_counts": {
            key: len(value) for key, value in data["record_contracts"].items()
        },
        "checkpoint_policy": data["checkpoint_policy"],
        "credit_predicates": data["credit_predicates"],
        "synthetic_controls": controls,
        "mutation_classes": data["mutation_classes"],
        "observed": data["observed"],
        "milestones": data["milestones"],
        "residual": data["residual"],
        "verdict": "execution evidence contract represented; no process or parity outcome observed",
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Lean execution evidence contract",
        "",
        "> **Generated; do not edit by hand.** Regenerate with `python3 "
        "scripts/gen-lean-execution-evidence.py`; validate with `--check`.",
        "",
        "> **Verdict: execution evidence contract represented; no process or "
        "parity outcome observed.** All real counters remain zero.",
        "",
        f"Preregistered at `{report['preregistration']['commit']}` before implementation.",
        "",
        "## Registered lane templates",
        "",
        "| Lane | Purpose | Memory ceiling | Scope | Workers | Credit class |",
        "|---|---|---:|---|---:|---|",
    ]
    for lane in report["lane_policies"]:
        lines.append(
            f"| `{lane['id']}` | {lane['purpose']} | "
            f"{lane['memory_limit_bytes']:,} bytes | `{lane['memory_scope']}` | "
            f"{lane['worker_limit']} | `{lane['credit_class']}` |"
        )
    lines.extend(
        [
            "",
            "The generic wrapper's 64 GiB default is not either registered lane; "
            "the 4/8 GiB value must be explicit in each run identity.",
            "",
            "## Typed termination classes",
            "",
            ", ".join(f"`{item}`" for item in report["termination_classes"]) + ".",
            "",
            "A memory, timeout, PID, or disk classification requires matching "
            "enforcement evidence. A signal or nonzero exit alone is not OOM proof.",
            "",
            "## Record contracts",
            "",
            "| Record | Required fields |",
            "|---|---:|",
        ]
    )
    for name, count in report["record_field_counts"].items():
        lines.append(f"| `{name}` | {count} |")
    lines.extend(
        [
            "",
            "## Synthetic representation controls",
            "",
            "| Control | Contract result | Meaning |",
            "|---|---|---|",
        ]
    )
    for control in report["synthetic_controls"]:
        result = "valid" if control["valid"] else "invalid"
        lines.append(f"| `{control['id']}` | `{result}` | {control['detail']} |")
    lines.extend(
        [
            "",
            f"The fail-closed register contains {len(report['mutation_classes'])} mutation classes. "
            "Synthetic controls test representation only and cannot enter a Lean denominator.",
            "",
            "## Checkpoint and credit boundary",
            "",
            "- Run identity is fixed before launch; every launch is an immutable attempt.",
            "- Case and raw-artifact records are content-addressed and never overwritten.",
            "- Resume retains terminal-less attempts and may add only missing valid records.",
            "- Completion is installed last and proves all-and-only case/attempt closure.",
            "- JUnit, logs, runner labels, provider conclusions, and expiring provider "
            "artifacts are not completion by themselves.",
            "- Adapter/export evidence cannot fill a native-system parity cell.",
            "",
            "## Observed real outcomes",
            "",
        ]
    )
    for field, count in report["observed"].items():
        lines.append(f"- `{field}`: {count}")
    lines.extend(["", "## Remaining work", ""])
    lines.extend(f"- {item}" for item in report["residual"])
    lines.append("")
    return "\n".join(lines)


def write_outputs(data: dict[str, Any]) -> None:
    report = summarize(data)
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_outputs(data: dict[str, Any]) -> list[str]:
    report = summarize(data)
    expected = {OUT_JSON: json_text(report), OUT_MD: render_markdown(report)}
    failures = []
    for path, text in expected.items():
        if not path.is_file():
            failures.append(f"missing generated output {path.relative_to(ROOT)}")
        elif path.read_text(encoding="utf-8") != text:
            failures.append(f"stale generated output {path.relative_to(ROOT)}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-authority", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write_authority:
        MANIFEST.write_text(json_text(build_authority()), encoding="utf-8")
    data = load_json(MANIFEST)
    failures = validate_authority(data)
    if not failures:
        for control_id, _ in SYNTHETIC_CONTROLS:
            control_failures = validate_bundle(synthetic_bundle(control_id), data)
            failures.extend(f"{control_id}: {item}" for item in control_failures)
    if args.check:
        failures.extend(check_outputs(data))
    elif not failures:
        write_outputs(data)
    if failures:
        for failure in failures:
            print(f"lean-execution-evidence: {failure}", file=sys.stderr)
        return 1
    print(
        "lean-execution-evidence: ok "
        f"({len(data['lane_policies'])} lanes; "
        f"{len(TERMINATION_CLASSES)} termination classes; "
        f"{len(SYNTHETIC_CONTROLS)} synthetic controls; "
        f"{len(MUTATION_CLASSES)} mutation classes; zero real outcomes)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
