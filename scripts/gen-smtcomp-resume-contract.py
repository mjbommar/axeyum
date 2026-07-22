#!/usr/bin/env python3
"""Validate and render the v2 resumable SMT-COMP execution contract."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "smtcomp_repro"))

from resume_contract import (  # noqa: E402
    ATTEMPT_LAUNCH_FIELDS,
    ATTEMPT_TERMINAL_FIELDS,
    CONTRACT_SCHEMA,
    RESULT_RECORD_FIELDS,
    RESULT_SCHEMA,
    RUN_IDENTITY_FIELDS,
    RUN_SCHEMA,
    SHARD_COMPLETION_FIELDS,
    VERDICT_POLICY,
    Bundle,
    ContractError,
    canonical_bytes,
    clone_bundle,
    digest,
    merge_complete,
    record_set_sha256,
    result_key,
    seal_record,
)

SOURCE = ROOT / "docs" / "plan" / "smtcomp-resumable-run-contract-v2.json"
OUTPUT_JSON = ROOT / "docs" / "plan" / "generated" / "smtcomp-resumable-run-contract.json"
OUTPUT_MD = ROOT / "docs" / "plan" / "generated" / "smtcomp-resumable-run-contract.md"


def fake_sha(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _identity() -> dict[str, Any]:
    solver_id = "axeyum"
    solver_binary = fake_sha("solver-binary")
    solver_command = fake_sha("solver-command")
    solver_config = digest(
        {
            "solver_id": solver_id,
            "solver_binary_sha256": solver_binary,
            "solver_command_sha256": solver_command,
        }
    )
    return {
        "contract_schema": CONTRACT_SCHEMA,
        "run_schema": RUN_SCHEMA,
        "result_schema": RESULT_SCHEMA,
        "selection_manifest_sha256": fake_sha("selection-manifest"),
        "selected_list_sha256": fake_sha("selected-list"),
        "corpus_identity_sha256": fake_sha("corpus-tree"),
        "solver_id": solver_id,
        "solver_binary_sha256": solver_binary,
        "solver_command_sha256": solver_command,
        "solver_config_sha256": solver_config,
        "runner_source_sha256": fake_sha("runner-source"),
        "repository_commit": fake_sha("repository-commit"),
        "source_tree_state_sha256": fake_sha("clean-source-tree"),
        "toolchain_identity_sha256": fake_sha("toolchain"),
        "track": "single_query",
        "wall_limit_ms": 20_000,
        "cpu_limit_ms": 80_000,
        "memory_limit_bytes": 1_073_741_824,
        "cores": 4,
        "shard_count": 2,
        "shard_mapping": "striped-index-v1",
        "environment_class_sha256": fake_sha("fixture-host-class"),
        "resource_policy_sha256": fake_sha("fixture-resource-policy"),
        "output_capture_policy_sha256": fake_sha("fixture-output-policy"),
        "verdict_policy": VERDICT_POLICY,
    }


def _row(
    identity_hash: str,
    identity: dict[str, Any],
    shard_id: str,
    sequence: int,
    attempt_id: str,
) -> dict[str, Any]:
    benchmark_id = f"QF_BV/family/case-{sequence}.smt2"
    benchmark_hash = fake_sha(f"benchmark-{sequence}")
    verdict = "sat" if sequence % 2 == 0 else "unsat"
    solver_config = identity["solver_config_sha256"]
    empty_hash = hashlib.sha256(b"").hexdigest()
    return seal_record(
        {
            "schema": RESULT_SCHEMA,
            "run_identity_sha256": identity_hash,
            "result_key": result_key(benchmark_id, benchmark_hash, solver_config),
            "benchmark_id": benchmark_id,
            "benchmark_sha256": benchmark_hash,
            "solver_id": identity["solver_id"],
            "solver_config_sha256": solver_config,
            "shard_id": shard_id,
            "sequence": sequence,
            "attempt_id": attempt_id,
            "environment_class_sha256": identity["environment_class_sha256"],
            "expected_status": verdict,
            "observed_status": verdict,
            "reported_status": verdict,
            "verdict_admission": "admitted",
            "termination_class": "completed",
            "exit_code": 0,
            "signal": None,
            "resource_limit_kind": None,
            "wall_time_ns": 1_000_000 + sequence,
            "runner_elapsed_ns": 1_000_000 + sequence,
            "cpu_time_ns": 900_000 + sequence,
            "peak_rss_bytes": 8_388_608 + sequence,
            "stdout_sha256": empty_hash,
            "stdout_bytes": 0,
            "stderr_sha256": empty_hash,
            "stderr_bytes": 0,
        }
    )


def _terminal(
    rows: list[dict[str, Any]],
    assigned: set[str],
    new_keys: list[str],
    skipped_keys: list[str],
) -> dict[str, Any]:
    durable = sorted(set(new_keys) | set(skipped_keys))
    by_key = {row["result_key"]: row for row in rows}
    missing = sorted(assigned - set(durable))
    return {
        "status": "completed" if not missing else "stopped",
        "exit_code": 0 if not missing else 75,
        "signal": None,
        "wall_time_ns": 2_000_000,
        "peak_rss_bytes": 8_388_608,
        "completed_count": len(durable),
        "result_set_sha256": record_set_sha256([by_key[key] for key in durable]),
        "durable_result_keys": durable,
        "new_result_keys": sorted(new_keys),
        "skipped_result_keys": sorted(skipped_keys),
        "missing_result_keys": missing,
        "ended_at_ns": 3_000_000,
    }


def make_bundle(interrupted: bool = False) -> Bundle:
    identity = _identity()
    identity_hash = digest(identity)
    run = {
        "schema": RUN_SCHEMA,
        "identity": identity,
        "identity_sha256": identity_hash,
        "resource_enforcement": {
            "kind": "fixture-cgroup-v2",
            "enforcement_id": fake_sha("fixture-cgroup"),
            "worker_slots": 2,
            "aggregate_memory_bytes": 2_147_483_648,
        },
    }

    attempt_for_sequence = {
        0: "0-a",
        1: "1-a",
        2: "0-b" if interrupted else "0-a",
        3: "1-a",
    }
    rows = [
        _row(identity_hash, identity, str(sequence % 2), sequence, attempt_for_sequence[sequence])
        for sequence in range(4)
    ]
    assignments = []
    attempts: dict[str, list[dict[str, Any]]] = {}
    completions: dict[str, dict[str, Any]] = {}

    for shard_id in ("0", "1"):
        shard_rows = [row for row in rows if row["shard_id"] == shard_id]
        assigned = {row["result_key"] for row in shard_rows}
        assignments.append(
            {"shard_id": shard_id, "result_keys": sorted(assigned)}
        )

        def launch(
            attempt_id: str,
            *,
            terminal: dict[str, Any] | None,
            pid_offset: int,
        ) -> dict[str, Any]:
            return {
                "attempt_id": attempt_id,
                "run_identity_sha256": identity_hash,
                "shard_id": shard_id,
                "host_id": "fixture-host",
                "pid": 1000 + int(shard_id) + pid_offset,
                "assigned_count": len(assigned),
                "launched_at_ns": 1_000_000 + pid_offset,
                "enforcement_id": fake_sha("fixture-cgroup"),
                "environment_class_sha256": identity["environment_class_sha256"],
                "terminal": terminal,
            }

        if interrupted and shard_id == "0":
            first_key = next(row["result_key"] for row in shard_rows if row["sequence"] == 0)
            second_key = next(row["result_key"] for row in shard_rows if row["sequence"] == 2)
            attempts[shard_id] = [
                launch("0-a", terminal=None, pid_offset=0),
                launch(
                    "0-b",
                    terminal=_terminal(shard_rows, assigned, [second_key], [first_key]),
                    pid_offset=10,
                ),
            ]
            unclosed = ["0-a"]
        else:
            attempt_id = f"{shard_id}-a"
            attempts[shard_id] = [
                launch(
                    attempt_id,
                    terminal=_terminal(
                        shard_rows,
                        assigned,
                        [row["result_key"] for row in shard_rows],
                        [],
                    ),
                    pid_offset=0,
                )
            ]
            unclosed = []

        completions[shard_id] = {
            "state": "complete",
            "run_identity_sha256": identity_hash,
            "assigned_count": len(assigned),
            "completed_count": len(shard_rows),
            "missing_result_keys": [],
            "result_set_sha256": record_set_sha256(shard_rows),
            "attempt_ids": [attempt["attempt_id"] for attempt in attempts[shard_id]],
            "unclosed_attempt_ids": unclosed,
        }
    return Bundle(run, assignments, rows, attempts, completions)


def reseal_run(bundle: Bundle) -> None:
    bundle.run["identity_sha256"] = digest(bundle.run["identity"])


def _mutate_run_identity(bundle: Bundle, field: str, value: Any) -> None:
    bundle.run["identity"][field] = value
    reseal_run(bundle)


def refresh_record_sets(bundle: Bundle) -> None:
    for shard_id, attempts in bundle.attempts.items():
        rows = [row for row in bundle.records if row["shard_id"] == shard_id]
        by_key = {row["result_key"]: row for row in rows}
        for attempt in attempts:
            terminal = attempt["terminal"]
            if terminal is not None:
                terminal["result_set_sha256"] = record_set_sha256(
                    [by_key[key] for key in terminal["durable_result_keys"]]
                )
        bundle.completions[shard_id]["result_set_sha256"] = record_set_sha256(rows)


def scenario_bundles() -> dict[str, Bundle]:
    base = make_bundle()
    interrupted = make_bundle(interrupted=True)
    scenarios: dict[str, Bundle] = {
        "uninterrupted": base,
        "interrupted_resume": interrupted,
        "reordered_artifacts": clone_bundle(interrupted),
        "accounted_prior_crash": clone_bundle(interrupted),
    }
    scenarios["reordered_artifacts"].records.reverse()
    scenarios["reordered_artifacts"].assignments.reverse()

    for name, field, value in (
        ("solver_identity_drift", "solver_binary_sha256", fake_sha("different-solver")),
        ("selection_identity_drift", "selected_list_sha256", fake_sha("different-list")),
        ("limit_identity_drift", "wall_limit_ms", 21_000),
        ("runner_identity_drift", "runner_source_sha256", fake_sha("different-runner")),
    ):
        candidate = clone_bundle(base)
        _mutate_run_identity(candidate, field, value)
        scenarios[name] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["reported_status"] = "unknown"
    scenarios["record_hash_tamper"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["run_identity_sha256"] = fake_sha("different-run")
    candidate.records[0] = seal_record(candidate.records[0])
    scenarios["record_run_identity_drift"] = candidate

    candidate = clone_bundle(base)
    conflict = copy.deepcopy(candidate.records[0])
    conflict["wall_time_ns"] += 1
    candidate.records.append(seal_record(conflict))
    scenarios["conflicting_duplicate"] = candidate

    candidate = clone_bundle(base)
    candidate.records.append(copy.deepcopy(candidate.records[0]))
    scenarios["identical_duplicate"] = candidate

    candidate = clone_bundle(base)
    candidate.records.pop()
    scenarios["missing_record"] = candidate

    candidate = clone_bundle(base)
    extra = copy.deepcopy(candidate.records[0])
    extra["benchmark_id"] = "QF_BV/family/unassigned.smt2"
    extra["benchmark_sha256"] = fake_sha("unassigned")
    extra["result_key"] = result_key(
        extra["benchmark_id"], extra["benchmark_sha256"], extra["solver_config_sha256"]
    )
    candidate.records.append(seal_record(extra))
    scenarios["unexpected_record"] = candidate

    candidate = clone_bundle(base)
    del candidate.completions["1"]
    scenarios["missing_shard_completion"] = candidate

    candidate = clone_bundle(base)
    candidate.completions["0"]["result_set_sha256"] = fake_sha("wrong-set")
    scenarios["wrong_result_set_hash"] = candidate

    candidate = clone_bundle(base)
    candidate.assignments[1]["result_keys"].append(candidate.assignments[0]["result_keys"][0])
    scenarios["overlapping_assignment"] = candidate

    candidate = clone_bundle(interrupted)
    candidate.completions["0"]["unclosed_attempt_ids"] = []
    scenarios["unaccounted_crash"] = candidate

    candidate = clone_bundle(base)
    candidate.run["resource_enforcement"] = {"kind": "none"}
    scenarios["missing_resource_enforcement"] = candidate

    candidate = clone_bundle(base)
    candidate.run["resource_enforcement"]["aggregate_memory_bytes"] -= 1
    scenarios["aggregate_memory_overcommit"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["environment_class_sha256"] = fake_sha("other-host-class")
    candidate.records[0] = seal_record(candidate.records[0])
    scenarios["environment_class_drift"] = candidate

    candidate = clone_bundle(base)
    del candidate.records[0]["cpu_time_ns"]
    scenarios["truncated_record"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["attempt_id"] = "missing-attempt"
    candidate.records[0] = seal_record(candidate.records[0])
    refresh_record_sets(candidate)
    scenarios["attempt_attribution_drift"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["exit_code"] = 7
    candidate.records[0] = seal_record(candidate.records[0])
    scenarios["illegal_termination_state"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["stdout_sha256"] = "not-a-hash"
    candidate.records[0] = seal_record(candidate.records[0])
    scenarios["invalid_output_identity"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0].update(
        {
            "termination_class": "wall-timeout",
            "exit_code": None,
            "signal": 9,
            "resource_limit_kind": "wall",
            "wall_time_ns": candidate.run["identity"]["wall_limit_ms"] * 1_000_000,
            "runner_elapsed_ns": candidate.run["identity"]["wall_limit_ms"]
            * 1_000_000
            + 5_000_000,
        }
    )
    candidate.records[0] = seal_record(candidate.records[0])
    refresh_record_sets(candidate)
    scenarios["timeout_response_retained"] = candidate

    candidate = clone_bundle(base)
    terminal = candidate.attempts["0"][0]["terminal"]
    assert terminal is not None
    terminal["new_result_keys"].pop()
    scenarios["terminal_attribution_mismatch"] = candidate

    candidate = clone_bundle(base)
    candidate.records[0]["wall_time_ns"] = (
        candidate.run["identity"]["wall_limit_ms"] * 1_000_000 + 1
    )
    candidate.records[0]["runner_elapsed_ns"] = candidate.records[0]["wall_time_ns"]
    candidate.records[0] = seal_record(candidate.records[0])
    scenarios["scoring_time_out_of_range"] = candidate
    return scenarios


def evaluate(source: dict[str, Any]) -> dict[str, Any]:
    if source.get("schema") != CONTRACT_SCHEMA:
        raise ContractError("source contract schema mismatch")
    declared_fields = {
        "run_identity_fields": RUN_IDENTITY_FIELDS,
        "result_record_fields": RESULT_RECORD_FIELDS,
        "attempt_launch_fields": ATTEMPT_LAUNCH_FIELDS,
        "attempt_terminal_fields": ATTEMPT_TERMINAL_FIELDS,
        "shard_completion_fields": SHARD_COMPLETION_FIELDS,
    }
    for source_name, implemented in declared_fields.items():
        if set(source.get(source_name, [])) != implemented:
            raise ContractError(f"{source_name} differs from executable contract")
    invariant_ids = [row["id"] for row in source["invariants"]]
    if len(invariant_ids) != len(set(invariant_ids)):
        raise ContractError("duplicate invariant id")
    known = set(invariant_ids)
    fixtures = scenario_bundles()
    declared_names = [row["name"] for row in source["scenarios"]]
    if set(declared_names) != set(fixtures):
        raise ContractError("declared and implemented scenario sets differ")

    baseline = merge_complete(fixtures["uninterrupted"])
    equal_controls = {
        "uninterrupted",
        "interrupted_resume",
        "reordered_artifacts",
        "accounted_prior_crash",
    }
    rows = []
    for spec in source["scenarios"]:
        if not set(spec["invariants"]).issubset(known):
            raise ContractError(f"{spec['id']}: unknown invariant")
        observed = "accept"
        reason = "validated"
        output = None
        try:
            output = merge_complete(fixtures[spec["name"]])
        except ContractError as exc:
            observed = "reject"
            reason = str(exc)
        if observed != spec["expected"]:
            raise ContractError(
                f"{spec['id']} expected {spec['expected']} but observed {observed}: {reason}"
            )
        byte_equal = output == baseline if output is not None else None
        if spec["name"] in equal_controls and not byte_equal:
            raise ContractError(f"{spec['id']}: accepted fixture differs from baseline")
        rows.append(
            {
                **spec,
                "observed": observed,
                "reason": reason,
                "canonical_byte_equal": byte_equal,
            }
        )

    covered = {invariant for row in rows for invariant in row["invariants"]}
    if covered != known:
        raise ContractError(f"uncovered invariants: {sorted(known - covered)}")
    return {
        "schema": "axeyum.smtcomp-resumable-run-contract-report.v2",
        "source_schema": source["schema"],
        "supersedes": source["supersedes"],
        "status": source["status"],
        "invariant_count": len(source["invariants"]),
        "scenario_count": len(rows),
        "accepted_scenarios": sum(row["observed"] == "accept" for row in rows),
        "rejected_scenarios": sum(row["observed"] == "reject" for row in rows),
        "deterministic_resume_byte_equal": next(
            row["canonical_byte_equal"] for row in rows if row["name"] == "interrupted_resume"
        ),
        "timeout_response_retained": next(
            row["observed"] == "accept" for row in rows if row["name"] == "timeout_response_retained"
        ),
        "baseline_output_sha256": hashlib.sha256(baseline).hexdigest(),
        "v1_corrections": source["v1_corrections"],
        "invariants": source["invariants"],
        "scenarios": rows,
        "declines": source["declines"],
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Resumable SMT-COMP-style run contract v2",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/smtcomp-resumable-run-contract-v2.json`](../smtcomp-resumable-run-contract-v2.json). "
        "Regenerate with `python3 scripts/gen-smtcomp-resume-contract.py`.",
        "",
        "Status: prototype; supersedes v1 before production integration; no full-library rerun is authorized.",
        "",
        "## Result",
        "",
        f"- Invariants: **{report['invariant_count']}**",
        f"- Executable scenarios: **{report['scenario_count']}** "
        f"({report['accepted_scenarios']} accepted controls, {report['rejected_scenarios']} rejected mutations)",
        f"- Interrupted/resumed scoring projection byte-identical to uninterrupted: **{str(report['deterministic_resume_byte_equal']).lower()}**",
        f"- Response observed before a forced timeout remains admitted: **{str(report['timeout_response_retained']).lower()}**",
        f"- Canonical baseline SHA-256: `{report['baseline_output_sha256']}`",
        "",
        "## Why v1 was insufficient",
        "",
    ]
    lines.extend(f"- {item}" for item in report["v1_corrections"])
    lines.extend(["", "## Invariants", ""])
    lines.extend(f"- **{row['id']}** — {row['statement']}" for row in report["invariants"])
    lines.extend(
        [
            "",
            "## Failure and recovery matrix",
            "",
            "| ID | Scenario | Expected | Observed | Baseline bytes | Contract result |",
            "|---|---|---:|---:|---:|---|",
        ]
    )
    for row in report["scenarios"]:
        byte_equal = (
            "n/a"
            if row["canonical_byte_equal"] is None
            else str(row["canonical_byte_equal"]).lower()
        )
        lines.append(
            f"| {row['id']} | `{row['name']}` | {row['expected']} | {row['observed']} | "
            f"{byte_equal} | {row['reason']} |"
        )
    lines.extend(["", "## Explicit declines", ""])
    lines.extend(f"- {decline}" for decline in report["declines"])
    lines.extend(
        [
            "",
            "## Implementation boundary",
            "",
            "The v2 in-memory and E1a filesystem prototypes validate evidence shape, attribution, no-overwrite persistence, and canonical scoring projection. E1b still has to integrate one-solver run manifests, exact benchmark IDs/hashes, output sidecars, typed process outcomes, attempt lifecycle, completion-last export, duplicate rejection, and a fake solver into `compete.py` without changing central scoring semantics.",
            "",
            "The current runner drops a parsed response on wall timeout and labels any other signal as memory exhaustion. V2 deliberately cannot encode those guesses as valid SMT-COMP evidence: observed and admitted verdicts are separate, and memory-limit classification requires actual enforcement evidence.",
            "",
        ]
    )
    return "\n".join(lines)


def write_or_check(path: Path, data: bytes, check: bool) -> None:
    if check:
        if not path.exists() or path.read_bytes() != data:
            raise ContractError(f"generated artifact stale: {path.relative_to(ROOT)}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    report = evaluate(source)
    write_or_check(
        OUTPUT_JSON,
        json.dumps(report, indent=2, sort_keys=True).encode() + b"\n",
        args.check,
    )
    write_or_check(OUTPUT_MD, render_markdown(report).encode("utf-8"), args.check)
    print(
        "smtcomp-resume-contract|"
        f"version=2|invariants={report['invariant_count']}|"
        f"scenarios={report['scenario_count']}|"
        f"accept={report['accepted_scenarios']}|reject={report['rejected_scenarios']}|"
        f"resume_byte_equal={str(report['deterministic_resume_byte_equal']).lower()}|"
        f"timeout_response_retained={str(report['timeout_response_retained']).lower()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
