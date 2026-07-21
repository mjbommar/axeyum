#!/usr/bin/env python3
"""Validate and render the resumable SMT-COMP execution contract."""

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
    Bundle,
    ATTEMPT_LAUNCH_FIELDS,
    ATTEMPT_TERMINAL_FIELDS,
    ContractError,
    RESULT_SCHEMA,
    RESULT_RECORD_FIELDS,
    RUN_SCHEMA,
    RUN_IDENTITY_FIELDS,
    SHARD_COMPLETION_FIELDS,
    canonical_bytes,
    clone_bundle,
    digest,
    merge_complete,
    record_set_sha256,
    result_key,
    seal_record,
)

SOURCE = ROOT / "docs" / "plan" / "smtcomp-resumable-run-contract-v1.json"
OUTPUT_JSON = ROOT / "docs" / "plan" / "generated" / "smtcomp-resumable-run-contract.json"
OUTPUT_MD = ROOT / "docs" / "plan" / "generated" / "smtcomp-resumable-run-contract.md"


def fake_sha(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def _identity() -> dict[str, Any]:
    return {
        "contract_schema": "axeyum.smtcomp-resumable-run-contract.v1",
        "benchmark_schema": RESULT_SCHEMA,
        "selection_manifest_sha256": fake_sha("selection-manifest"),
        "selected_list_sha256": fake_sha("selected-list"),
        "corpus_identity_sha256": fake_sha("corpus-tree"),
        "solver_binary_sha256": fake_sha("solver-binary"),
        "solver_command_sha256": fake_sha("solver-command"),
        "runner_source_sha256": fake_sha("runner-source"),
        "repository_commit": fake_sha("repository-commit"),
        "track": "single_query",
        "wall_limit_ms": 20_000,
        "cpu_limit_ms": 80_000,
        "memory_limit_bytes": 1_073_741_824,
        "cores": 4,
        "shard_count": 2,
        "shard_mapping": "striped-index-v1",
        "environment_class_sha256": fake_sha("fixture-host-class"),
    }


def _row(identity_hash: str, shard_id: str, sequence: int) -> dict[str, Any]:
    benchmark_id = f"QF_BV/family/case-{sequence}.smt2"
    benchmark_hash = fake_sha(f"benchmark-{sequence}")
    solver_id = "axeyum"
    return seal_record(
        {
            "schema": RESULT_SCHEMA,
            "run_identity_sha256": identity_hash,
            "result_key": result_key(benchmark_id, benchmark_hash, solver_id),
            "benchmark_id": benchmark_id,
            "benchmark_sha256": benchmark_hash,
            "solver_id": solver_id,
            "shard_id": shard_id,
            "sequence": sequence,
            "environment_class_sha256": fake_sha("fixture-host-class"),
            "expected_status": "sat" if sequence % 2 == 0 else "unsat",
            "reported_status": "sat" if sequence % 2 == 0 else "unsat",
            "wall_time_ns": 1_000_000 + sequence,
            "cpu_time_ns": 900_000 + sequence,
        }
    )


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
    rows = [
        _row(identity_hash, "0", 0),
        _row(identity_hash, "1", 1),
        _row(identity_hash, "0", 2),
        _row(identity_hash, "1", 3),
    ]
    assignments = []
    attempts: dict[str, list[dict[str, Any]]] = {}
    completions: dict[str, dict[str, Any]] = {}
    for shard_id in ("0", "1"):
        shard_rows = [row for row in rows if row["shard_id"] == shard_id]
        assignments.append(
            {"shard_id": shard_id, "result_keys": [row["result_key"] for row in shard_rows]}
        )
        def attempt(attempt_id: str, terminal: bool) -> dict[str, Any]:
            terminal_value = None
            if terminal:
                terminal_value = {
                    "status": "completed",
                    "exit_code": 0,
                    "signal": None,
                    "wall_time_ns": 2_000_000,
                    "peak_rss_bytes": 8_388_608,
                    "completed_count": len(shard_rows),
                    "result_set_sha256": record_set_sha256(shard_rows),
                    "missing_result_keys": [],
                    "ended_at_ns": 3_000_000,
                }
            return {
                "attempt_id": attempt_id,
                "run_identity_sha256": identity_hash,
                "shard_id": shard_id,
                "host_id": "fixture-host",
                "pid": 1000 + int(shard_id),
                "assigned_count": len(shard_rows),
                "launched_at_ns": 1_000_000,
                "enforcement_id": fake_sha("fixture-cgroup"),
                "environment_class_sha256": fake_sha("fixture-host-class"),
                "terminal": terminal_value,
            }

        if interrupted and shard_id == "0":
            attempts[shard_id] = [attempt("0-a", False), attempt("0-b", True)]
            unclosed = ["0-a"]
        else:
            attempts[shard_id] = [attempt(f"{shard_id}-a", True)]
            unclosed = []
        completions[shard_id] = {
            "state": "complete",
            "run_identity_sha256": identity_hash,
            "assigned_count": len(shard_rows),
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
    extra["result_key"] = result_key(extra["benchmark_id"], extra["benchmark_sha256"], extra["solver_id"])
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
    return scenarios


def evaluate(source: dict[str, Any]) -> dict[str, Any]:
    if source.get("schema") != "axeyum.smtcomp-resumable-run-contract.v1":
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
        if spec["name"] in {
            "uninterrupted",
            "interrupted_resume",
            "reordered_artifacts",
            "accounted_prior_crash",
        } and not byte_equal:
            raise ContractError(f"{spec['id']}: accepted fixture differs from baseline")
        rows.append(
            {
                **spec,
                "observed": observed,
                "reason": reason,
                "canonical_byte_equal": byte_equal,
            }
        )

    covered = {inv for row in rows for inv in row["invariants"]}
    if covered != known:
        raise ContractError(f"uncovered invariants: {sorted(known - covered)}")
    return {
        "schema": "axeyum.smtcomp-resumable-run-contract-report.v1",
        "source_schema": source["schema"],
        "status": source["status"],
        "invariant_count": len(source["invariants"]),
        "scenario_count": len(rows),
        "accepted_scenarios": sum(row["observed"] == "accept" for row in rows),
        "rejected_scenarios": sum(row["observed"] == "reject" for row in rows),
        "deterministic_resume_byte_equal": next(
            row["canonical_byte_equal"] for row in rows if row["name"] == "interrupted_resume"
        ),
        "baseline_output_sha256": hashlib.sha256(baseline).hexdigest(),
        "invariants": source["invariants"],
        "scenarios": rows,
        "declines": source["declines"],
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Resumable SMT-COMP-style run contract",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/smtcomp-resumable-run-contract-v1.json`](../smtcomp-resumable-run-contract-v1.json). "
        "Regenerate with `python3 scripts/gen-smtcomp-resume-contract.py`.",
        "",
        "Status: prototype; no full-library rerun is authorized by this artifact.",
        "",
        "## Result",
        "",
        f"- Invariants: **{report['invariant_count']}**",
        f"- Executable scenarios: **{report['scenario_count']}** "
        f"({report['accepted_scenarios']} accepted controls, {report['rejected_scenarios']} rejected mutations)",
        f"- Interrupted/resumed deterministic fixture byte-identical to uninterrupted: **{str(report['deterministic_resume_byte_equal']).lower()}**",
        f"- Canonical baseline SHA-256: `{report['baseline_output_sha256']}`",
        "",
        "## Invariants",
        "",
    ]
    lines.extend(f"- **{row['id']}** — {row['statement']}" for row in report["invariants"])
    lines.extend(
        [
            "",
            "## Failure and recovery matrix",
            "",
            "| ID | Scenario | Expected | Observed | Canonical bytes | Contract result |",
            "|---|---|---:|---:|---:|---|",
        ]
    )
    for row in report["scenarios"]:
        byte_equal = "n/a" if row["canonical_byte_equal"] is None else str(row["canonical_byte_equal"]).lower()
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
            "The prototype validates the data and lifecycle contract in memory. Production work still has to implement same-directory temporary writes plus fsync/rename, immutable launch and terminal manifests, single-owner shard leases, cgroup-v2 (or equivalent) aggregate enforcement, signal-safe best-effort terminal emission, conflict quarantine, and strict central merge over real filesystem artifacts. A tiny fake-solver process test must kill an actual worker at fixed record boundaries before the 64,345-case candidate can be rerun.",
            "",
            "BenchExec remains the external reference execution layer for official-style rehearsal; this local protocol exists to make Axeyum's pre-rehearsal distributed evidence durable and auditable.",
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
    write_or_check(OUTPUT_JSON, json.dumps(report, indent=2, sort_keys=True).encode() + b"\n", args.check)
    write_or_check(OUTPUT_MD, render_markdown(report).encode("utf-8"), args.check)
    print(
        "smtcomp-resume-contract|"
        f"invariants={report['invariant_count']}|scenarios={report['scenario_count']}|"
        f"accept={report['accepted_scenarios']}|reject={report['rejected_scenarios']}|"
        f"resume_byte_equal={str(report['deterministic_resume_byte_equal']).lower()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
