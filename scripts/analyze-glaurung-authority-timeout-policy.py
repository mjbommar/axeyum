#!/usr/bin/env python3
"""Validate the preregistered wider Glaurung authority/timeout policy matrix."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


REPORT_SCHEMA = "axeyum.glaurung-authoritative-finding-parity.v6"
ANALYSIS_SCHEMA = "axeyum.glaurung-authority-timeout-policy.v1"
EXPECTED_GLAURUNG_REVISION = "ff3c0a767a0b085f8552bdb2b363c0b7fa273cbe"
EXPECTED_Z3_BINARY_SHA256 = (
    "63863636b1cd064c664c593b15a29f9e5ab791b013dbf925666481df1861772a"
)
EXPECTED_AXEYUM_BINARY_SHA256 = (
    "f4f9312fb0257b0a8f4e2a6422247b7dfc279c1a9b308177fa1b9fda2f1c57a5"
)
EXPECTED_DRIVER_SHA256 = (
    "ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea"
)
POLICIES = ("any-model", "min-unsigned")
TIMEOUTS_MS = (100, 250, 1000)
POLICY_IDS = {
    "any-model": "glaurung-any-model-v1",
    "min-unsigned": "glaurung-min-unsigned-v1",
}
EXPECTED_BASE_ENVIRONMENT = {
    "IOCTLANCE_ALL": "1",
    "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
    "IOCTLANCE_DEADLINE_SECS": "2400",
    "IOCTLANCE_SOLVE_BUDGET": "400000",
    "IOCTLANCE_SOLVE_SECS": "900",
    "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": "20",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def expected_cells() -> set[tuple[str, int]]:
    return {(policy, timeout) for policy in POLICIES for timeout in TIMEOUTS_MS}


def validate_exploration_partition(summary: dict[str, Any], *, label: str) -> None:
    require(
        summary.get("deterministic_worklists_verified") is True,
        f"{label} did not verify deterministic worklists",
    )
    exploration = summary.get("exploration_limits")
    require(isinstance(exploration, dict), f"{label} lacks exploration limits")
    backends = exploration.get("backends")
    require(isinstance(backends, dict), f"{label} lacks backend stop partitions")
    for backend in ("z3", "axeyum"):
        row = backends.get(backend)
        require(isinstance(row, dict), f"{label} lacks {backend} stop partition")
        classified = sum(
            int(row.get(key, -1))
            for key in (
                "completed",
                "state_budget",
                "solve_budget",
                "timeout_budget",
                "deadline",
            )
        )
        require(
            classified == int(row.get("runs", -2)),
            f"{label} {backend} stop partition is inconsistent",
        )
        require(
            int(row.get("timeout_budget", -1)) == 0
            and int(row.get("deadline", -1)) == 0,
            f"{label} {backend} has a deadline/timeout worklist stop",
        )


def validate_report(
    report: dict[str, Any],
    *,
    policy: str,
    timeout_ms: int,
    expected_axeyum_revision: str,
) -> dict[str, Any]:
    label = f"{policy}/{timeout_ms}ms"
    require(report.get("schema") == REPORT_SCHEMA, f"{label} schema mismatch")
    require(report.get("accepted") is True, f"{label} report was not accepted")
    require(report.get("failures") == [], f"{label} contains failures")
    require(
        report.get("post_run_source_identity", {}).get("stable") is True,
        f"{label} source identity changed during measurement",
    )
    glaurung = report.get("glaurung", {})
    axeyum = report.get("axeyum", {})
    require(
        glaurung.get("revision") == EXPECTED_GLAURUNG_REVISION
        and glaurung.get("tracked_dirty") is False,
        f"{label} Glaurung revision mismatch",
    )
    require(
        axeyum.get("revision") == expected_axeyum_revision
        and axeyum.get("tracked_dirty") is False,
        f"{label} Axeyum revision mismatch",
    )
    binaries = report.get("binaries", {})
    require(
        binaries.get("z3", {}).get("sha256") == EXPECTED_Z3_BINARY_SHA256,
        f"{label} Z3 authority binary mismatch",
    )
    require(
        binaries.get("axeyum", {}).get("sha256")
        == EXPECTED_AXEYUM_BINARY_SHA256,
        f"{label} Axeyum authority binary mismatch",
    )
    require(report.get("repetitions") == 3, f"{label} repetition count mismatch")
    require(
        report.get("process_timeout_seconds") == 2700,
        f"{label} process timeout mismatch",
    )
    require(
        report.get("check_timeout_ms_required") == timeout_ms,
        f"{label} check timeout mismatch",
    )
    require(
        report.get("deterministic_worklists_required") is True,
        f"{label} did not require deterministic worklists",
    )
    require(
        report.get("acceptance_population") == "high-confidence",
        f"{label} acceptance population mismatch",
    )

    environment = report.get("environment")
    require(isinstance(environment, dict), f"{label} lacks environment")
    expected_environment = dict(EXPECTED_BASE_ENVIRONMENT)
    expected_environment["GLAURUNG_CHECK_TIMEOUT_MS"] = str(timeout_ms)
    if policy == "min-unsigned":
        expected_environment["GLAURUNG_CONCRETIZATION_POLICY"] = "min-unsigned"
    require(environment == expected_environment, f"{label} environment mismatch")

    if policy == "any-model":
        require(
            report.get("canonical_model_choice_required") is False
            and report.get("canonical_model_choice_policy") is None
            and report.get("concretization_policy_source") == "default",
            f"{label} default-policy metadata mismatch",
        )
    else:
        require(
            report.get("canonical_model_choice_required") is True
            and report.get("canonical_model_choice_policy") == POLICY_IDS[policy]
            and report.get("concretization_policy_source") == "preferred"
            and report.get("concretization_policy_label") == policy
            and report.get("concretization_policy_id") == POLICY_IDS[policy],
            f"{label} selected-policy metadata mismatch",
        )

    drivers = report.get("drivers")
    require(isinstance(drivers, list) and len(drivers) == 1, f"{label} driver count mismatch")
    driver = drivers[0]
    require(
        driver.get("driver", {}).get("sha256") == EXPECTED_DRIVER_SHA256,
        f"{label} driver identity mismatch",
    )
    require(driver.get("summary_error") is None, f"{label} has a summary error")
    summary = driver.get("summary")
    require(isinstance(summary, dict), f"{label} has no summary")
    require(
        summary.get("within_backend_stable") is True,
        f"{label} finding population is unstable",
    )
    require(
        summary.get("exact_high_confidence_finding_parity") is True,
        f"{label} high-confidence authority findings differ",
    )
    coverage = summary.get("coverage")
    require(
        coverage == {
            "analyzed": 20,
            "reachable": 338,
            "boundary": "fixed-work-limit",
        },
        f"{label} coverage boundary mismatch",
    )
    require(
        summary.get("check_timeout_ms") == timeout_ms,
        f"{label} summary timeout mismatch",
    )
    validate_exploration_partition(summary, label=label)

    canonical = summary.get("canonical_model_choice")
    require(isinstance(canonical, dict), f"{label} lacks policy telemetry")
    require(
        canonical.get("policy") == POLICY_IDS[policy],
        f"{label} policy telemetry mismatch",
    )
    canonical_backends = canonical.get("backends")
    require(isinstance(canonical_backends, dict), f"{label} lacks backend policy telemetry")
    for backend in ("z3", "axeyum"):
        row = canonical_backends.get(backend)
        require(isinstance(row, dict), f"{label} lacks {backend} policy telemetry")
        require(
            row.get("policy") == POLICY_IDS[policy]
            and int(row.get("inconclusive", -1)) == 0,
            f"{label} {backend} policy was inconclusive",
        )

    backend_rows = summary.get("backends")
    require(isinstance(backend_rows, dict), f"{label} lacks backend work summaries")
    return {
        "policy": policy,
        "policy_id": POLICY_IDS[policy],
        "timeout_ms": timeout_ms,
        "raw_exact_authority_parity": summary.get("exact_raw_finding_parity") is True,
        "high_confidence_exact_authority_parity": True,
        "raw_z3_only_count": len(summary.get("raw", {}).get("z3_only", [])),
        "raw_axeyum_only_count": len(summary.get("raw", {}).get("axeyum_only", [])),
        "coverage": coverage,
        "exploration_limits": summary["exploration_limits"],
        "canonical_model_choice": canonical,
        "backends": {
            backend: {
                key: backend_rows[backend].get(key)
                for key in (
                    "finding_count",
                    "high_confidence_finding_count",
                    "solves",
                    "elapsed_seconds",
                    "max_rss_kib",
                )
            }
            for backend in ("z3", "axeyum")
        },
    }


def analyze_reports(
    reports: dict[tuple[str, int], dict[str, Any]],
    expected_axeyum_revision: str,
) -> dict[str, Any]:
    require(set(reports) == expected_cells(), "authority timeout/policy matrix is incomplete")
    cells = [
        validate_report(
            reports[(policy, timeout)],
            policy=policy,
            timeout_ms=timeout,
            expected_axeyum_revision=expected_axeyum_revision,
        )
        for policy in POLICIES
        for timeout in TIMEOUTS_MS
    ]
    by_policy = {
        policy: [cell for cell in cells if cell["policy"] == policy]
        for policy in POLICIES
    }
    return {
        "schema": ANALYSIS_SCHEMA,
        "valid": True,
        "claim": (
            "wider fixed-prefix sole-authority finding sensitivity across explicit "
            "timeout and concretization-policy cells"
        ),
        "claim_limits": [
            "tcpip first 20 of 338 reachable functions only",
            "high-confidence output remains the validity gate; raw divergence is reported",
            "wall-clock timeout cells are sensitivity evidence, not deterministic work equivalence",
            "backend resource units are not compared in this campaign",
        ],
        "glaurung_revision": EXPECTED_GLAURUNG_REVISION,
        "axeyum_revision": expected_axeyum_revision,
        "driver_sha256": EXPECTED_DRIVER_SHA256,
        "repetitions_per_cell_authority": 3,
        "timeouts_ms": list(TIMEOUTS_MS),
        "policies": list(POLICIES),
        "any_model_raw_parity_all_timeouts": all(
            cell["raw_exact_authority_parity"] for cell in by_policy["any-model"]
        ),
        "least_unsigned_raw_parity_all_timeouts": all(
            cell["raw_exact_authority_parity"]
            for cell in by_policy["min-unsigned"]
        ),
        "high_confidence_parity_all_cells": True,
        "cells": cells,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path, required=True)
    parser.add_argument("--expected-axeyum-revision", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    reports: dict[tuple[str, int], dict[str, Any]] = {}
    for policy in POLICIES:
        for timeout in TIMEOUTS_MS:
            path = args.report_dir / f"{policy}-{timeout}ms-report.json"
            with path.open() as source:
                reports[(policy, timeout)] = json.load(source)
    analysis = analyze_reports(reports, args.expected_axeyum_revision)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w") as destination:
        json.dump(analysis, destination, indent=2, sort_keys=True)
        destination.write("\n")


if __name__ == "__main__":
    main()
