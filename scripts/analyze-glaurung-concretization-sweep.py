#!/usr/bin/env python3
"""Fail-closed analysis for the preregistered Glaurung A0 policy sweep."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REGISTRATION_SCHEMA = "axeyum.glaurung-concretization-sweep-preregistration.v1"
AUTHORITY_SCHEMA = "axeyum.glaurung-authoritative-finding-parity.v5"
VALIDATION_SCHEMA = "axeyum.glaurung-validated-finding-population.v1"
OUTPUT_SCHEMA = "axeyum.glaurung-concretization-sweep.v1"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def text_sha256(lines: list[str]) -> str:
    return hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def _clean_identity(identity: Any) -> bool:
    return (
        isinstance(identity, dict)
        and isinstance(identity.get("revision"), str)
        and bool(identity["revision"])
        and identity.get("tracked_dirty") is False
    )


def _expected_environment(
    work: dict[str, Any], policy: dict[str, Any]
) -> dict[str, str]:
    environment = {
        "IOCTLANCE_ALL": "1",
        "IOCTLANCE_ANNOTATE_CONFIDENCE": "1",
        "IOCTLANCE_DEADLINE_SECS": str(work["deadline_secs"]),
        "IOCTLANCE_SOLVE_BUDGET": str(work["solve_budget"]),
        "IOCTLANCE_SOLVE_SECS": str(work["solve_secs"]),
        "IOCTLANCE_MAX_ANALYZED_FUNCTIONS": str(
            work["max_analyzed_functions"]
        ),
        "GLAURUNG_CHECK_TIMEOUT_MS": str(work["check_timeout_ms"]),
    }
    if policy["harness_choice"] is not None:
        environment["GLAURUNG_CONCRETIZATION_POLICY"] = policy["harness_choice"]
    return environment


def _validate_policy_metadata(
    report: dict[str, Any], policy: dict[str, Any], label: str
) -> None:
    deterministic = policy["harness_choice"] is not None
    expected_id = policy["policy_id"]
    if deterministic:
        require(
            report.get("concretization_policy_source") == "preferred",
            f"{label} did not use the preferred concretization policy surface",
        )
        require(
            report.get("concretization_policy_label") == policy["harness_choice"],
            f"{label} policy label differs",
        )
        require(
            report.get("concretization_policy_id") == expected_id,
            f"{label} policy ID differs",
        )
        require(
            report.get("canonical_model_choice_required") is True,
            f"{label} did not require model-choice telemetry",
        )
        require(
            report.get("canonical_model_choice_policy") == expected_id,
            f"{label} telemetry policy ID differs",
        )
    else:
        require(
            report.get("concretization_policy_source") == "default",
            f"{label} did not preserve the default AnyModel surface",
        )
        require(
            report.get("concretization_policy_label") is None
            and report.get("concretization_policy_id") is None,
            f"{label} unexpectedly selected a nondefault policy",
        )
        require(
            report.get("canonical_model_choice_required") is False
            and report.get("canonical_model_choice_policy") is None,
            f"{label} unexpectedly required canonical model choice",
        )


def _stable_driver_populations(
    report: dict[str, Any],
    driver: dict[str, Any],
    *,
    label: str,
    policy: dict[str, Any],
    repetitions: int,
    expected_boundary: str,
) -> dict[str, Any]:
    require(driver.get("summary_error") is None, f"{label} driver summary failed")
    summary = driver.get("summary")
    require(isinstance(summary, dict), f"{label} driver summary is missing")
    require(
        summary.get("confidence_partition_available") is True,
        f"{label} confidence partition is unavailable",
    )
    require(
        summary.get("exact_high_confidence_finding_parity") is True,
        f"{label} high-confidence authority findings differ",
    )
    coverage = summary.get("coverage")
    require(isinstance(coverage, dict), f"{label} coverage summary is missing")
    require(
        coverage.get("boundary") == expected_boundary,
        f"{label} coverage boundary differs",
    )

    runs = driver.get("runs")
    require(isinstance(runs, list) and runs, f"{label} has no runs")
    by_backend: dict[str, dict[int, dict[str, Any]]] = {"z3": {}, "axeyum": {}}
    for index, run in enumerate(runs):
        require(isinstance(run, dict), f"{label} run {index} is malformed")
        require("run_error" not in run, f"{label} contains a process failure")
        backend = run.get("backend")
        require(backend in by_backend, f"{label} has an unknown backend")
        repetition = run.get("repetition")
        require(
            isinstance(repetition, int) and 1 <= repetition <= repetitions,
            f"{label} has an invalid repetition",
        )
        require(
            repetition not in by_backend[backend],
            f"{label} repeats a backend/repetition cell",
        )
        require(
            run.get("confidence_partition_available") is True,
            f"{label} run lacks a confidence partition",
        )
        require(
            run.get("coverage_boundary") == expected_boundary,
            f"{label} run coverage boundary differs",
        )
        require(
            run.get("check_timeout_ms")
            == report.get("check_timeout_ms_required"),
            f"{label} run check timeout differs",
        )
        if policy["harness_choice"] is not None:
            telemetry = run.get("canonical_model_choice")
            require(isinstance(telemetry, dict), f"{label} run lacks policy telemetry")
            require(
                telemetry.get("policy") == policy["policy_id"],
                f"{label} run policy ID differs",
            )
            require(
                telemetry.get("inconclusive") == 0,
                f"{label} run contains inconclusive policy choices",
            )
        else:
            telemetry = run.get("canonical_model_choice")
            require(
                isinstance(telemetry, dict)
                and telemetry.get("policy") == policy["policy_id"],
                f"{label} run lacks AnyModel compatibility telemetry",
            )
            require(
                all(
                    telemetry.get(key) == 0
                    for key in (
                        "attempts",
                        "completed",
                        "infeasible",
                        "probes",
                        "inconclusive",
                        "unsupported_width",
                        "unknown",
                        "no_solver",
                        "error",
                        "final_unsat",
                    )
                ),
                f"{label} AnyModel unexpectedly performed canonical-choice work",
            )
        by_backend[backend][repetition] = run

    populations: dict[str, dict[str, Any]] = {}
    for backend, rows in by_backend.items():
        require(
            set(rows) == set(range(1, repetitions + 1)),
            f"{label} {backend} repetition population is incomplete",
        )
        ordered_runs = [rows[index] for index in range(1, repetitions + 1)]
        population: dict[str, Any] = {}
        for prefix, list_key, count_key in (
            ("raw", "findings", "finding_count"),
            (
                "high_confidence",
                "high_confidence_findings",
                "high_confidence_finding_count",
            ),
            ("diagnostic", "diagnostic_findings", "diagnostic_finding_count"),
        ):
            candidates = [run.get(list_key) for run in ordered_runs]
            require(
                all(
                    isinstance(candidate, list)
                    and all(isinstance(item, str) for item in candidate)
                    for candidate in candidates
                ),
                f"{label} {backend} {prefix} population is malformed",
            )
            first = candidates[0]
            require(
                all(candidate == first for candidate in candidates[1:]),
                f"{label} {backend} {prefix} output is unstable",
            )
            require(
                len(first) == len(set(first)),
                f"{label} {backend} {prefix} output contains duplicates",
            )
            require(
                all(run.get(count_key) == len(first) for run in ordered_runs),
                f"{label} {backend} {prefix} count is inconsistent",
            )
            hash_key = (
                "findings_sha256"
                if prefix == "raw"
                else f"{prefix}_findings_sha256"
            )
            require(
                all(run.get(hash_key) == text_sha256(first) for run in ordered_runs),
                f"{label} {backend} {prefix} hash is inconsistent",
            )
            population[f"{prefix}_findings"] = first
            population[f"{prefix}_count"] = len(first)
        require(
            not (
                set(population["high_confidence_findings"])
                & set(population["diagnostic_findings"])
            )
            and set(population["raw_findings"])
            == set(population["high_confidence_findings"])
            | set(population["diagnostic_findings"]),
            f"{label} {backend} confidence partition is not an exact disjoint union",
        )
        solves = [run.get("solves") for run in ordered_runs]
        require(
            all(isinstance(value, int) and value >= 0 for value in solves)
            and len(set(solves)) == 1,
            f"{label} {backend} solve work is unstable",
        )
        population["solves"] = solves
        for metric in ("solver_time_ms", "elapsed_seconds", "max_rss_kib"):
            values = [run.get(metric) for run in ordered_runs]
            require(
                all(
                    isinstance(value, (int, float))
                    and not isinstance(value, bool)
                    and math.isfinite(value)
                    and value >= 0
                    for value in values
                ),
                f"{label} {backend} {metric} population is malformed",
            )
            population[metric] = values
        populations[backend] = population

    require(
        populations["z3"]["high_confidence_findings"]
        == populations["axeyum"]["high_confidence_findings"],
        f"{label} stable high-confidence authority findings differ",
    )
    if policy["harness_choice"] is not None:
        require(
            populations["z3"]["solves"] == populations["axeyum"]["solves"],
            f"{label} deterministic-policy solve work differs by authority",
        )
    return {"coverage": coverage, "backends": populations}


def _validate_report(
    registration: dict[str, Any],
    policy: dict[str, Any],
    stratum: dict[str, Any],
    report: dict[str, Any],
) -> dict[str, Any]:
    label = f"{policy['label']}/{stratum['name']}"
    require(report.get("schema") == AUTHORITY_SCHEMA, f"{label} schema differs")
    require(report.get("accepted") is True, f"{label} authority report was not accepted")
    require(report.get("failures") == [], f"{label} authority report contains failures")
    require(
        report.get("acceptance_population") == "high-confidence",
        f"{label} acceptance population differs",
    )
    require(
        report.get("all_drivers_exact_high_confidence_finding_parity") is True,
        f"{label} lacks exact high-confidence authority parity",
    )
    require(
        _clean_identity(report.get("glaurung"))
        and report["glaurung"]["revision"] == registration["glaurung_revision"],
        f"{label} Glaurung revision or cleanliness differs",
    )
    require(_clean_identity(report.get("axeyum")), f"{label} Axeyum source is dirty")
    post = report.get("post_run_source_identity")
    require(
        isinstance(post, dict) and post.get("stable") is True,
        f"{label} source identity changed during measurement",
    )
    for source in ("glaurung", "axeyum"):
        require(
            _clean_identity(post.get(source))
            and post[source].get("revision") == report[source].get("revision"),
            f"{label} post-run {source} identity differs",
        )
    for backend in ("z3", "axeyum"):
        require(
            report.get("binaries", {}).get(backend, {}).get("sha256")
            == registration["authority_binary_sha256"][backend],
            f"{label} {backend} binary identity differs",
        )

    work = stratum["work"]
    require(
        report.get("repetitions") == work["repetitions"],
        f"{label} repetition count differs",
    )
    require(
        report.get("process_timeout_seconds") == work["process_timeout_secs"],
        f"{label} process timeout differs",
    )
    require(
        report.get("check_timeout_ms_required") == work["check_timeout_ms"],
        f"{label} check timeout differs",
    )
    require(
        report.get("environment") == _expected_environment(work, policy),
        f"{label} environment or fixed-work configuration differs",
    )
    require(
        report.get("order")
        == "odd repetitions Z3/Axeyum; even repetitions Axeyum/Z3",
        f"{label} execution order differs",
    )
    _validate_policy_metadata(report, policy, label)

    drivers = report.get("drivers")
    require(isinstance(drivers, list), f"{label} driver population is missing")
    by_sha: dict[str, dict[str, Any]] = {}
    for driver in drivers:
        identity = driver.get("driver") if isinstance(driver, dict) else None
        sha256 = identity.get("sha256") if isinstance(identity, dict) else None
        require(isinstance(sha256, str), f"{label} driver identity is malformed")
        require(sha256 not in by_sha, f"{label} repeats a driver identity")
        by_sha[sha256] = driver
    require(
        set(by_sha) == set(stratum["driver_sha256"]),
        f"{label} driver population differs",
    )
    driver_results = {
        sha256: _stable_driver_populations(
            report,
            driver,
            label=f"{label}/{sha256}",
            policy=policy,
            repetitions=work["repetitions"],
            expected_boundary=stratum["coverage_boundary"],
        )
        for sha256, driver in by_sha.items()
    }
    return {
        "axeyum": report["axeyum"],
        "glaurung": report["glaurung"],
        "binaries": report["binaries"],
        "drivers": driver_results,
    }


def _flatten_population(
    cell: dict[str, Any], backend: str, key: str
) -> list[str]:
    flattened: list[str] = []
    for sha256, driver in cell["drivers"].items():
        for finding in driver["backends"][backend][f"{key}_findings"]:
            flattened.append(f"{sha256}:{finding}")
    return sorted(flattened)


def _display_finding(row: str) -> str:
    return row.split(":", 1)[1]


def analyze_sweep(
    registration: dict[str, Any],
    reports: dict[str, dict[str, dict[str, Any]]],
    validations: dict[str, dict[str, Any]],
    report_hashes: dict[str, dict[str, str]],
) -> dict[str, Any]:
    """Validate all preregistered cells and summarize without outcome gates."""

    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "preregistration schema differs",
    )
    policy_rows = registration.get("policies")
    stratum_rows = registration.get("strata")
    require(isinstance(policy_rows, list) and policy_rows, "no policies preregistered")
    require(isinstance(stratum_rows, list) and stratum_rows, "no strata preregistered")
    policies = {row["label"]: row for row in policy_rows}
    strata = {row["name"]: row for row in stratum_rows}
    require(len(policies) == len(policy_rows), "duplicate policy registration")
    require(len(strata) == len(stratum_rows), "duplicate stratum registration")
    require(
        set(reports) == set(policies)
        and set(validations) == set(policies)
        and set(report_hashes) == set(policies),
        "policy population differs from preregistration",
    )

    cells: dict[str, dict[str, Any]] = {}
    axeyum_identity: dict[str, Any] | None = None
    binaries: dict[str, Any] | None = None
    for policy_label, policy in policies.items():
        require(
            set(reports[policy_label]) == set(strata)
            and set(report_hashes[policy_label]) == set(strata),
            f"{policy_label} stratum population differs from preregistration",
        )
        cells[policy_label] = {}
        for stratum_label, stratum in strata.items():
            cell = _validate_report(
                registration, policy, stratum, reports[policy_label][stratum_label]
            )
            if axeyum_identity is None:
                axeyum_identity = cell["axeyum"]
                binaries = cell["binaries"]
            else:
                require(
                    cell["axeyum"].get("revision") == axeyum_identity.get("revision"),
                    "Axeyum revision drift across sweep cells",
                )
                require(cell["binaries"] == binaries, "authority binary drift across cells")
            cells[policy_label][stratum_label] = cell

    positive_rows = [
        row for row in stratum_rows if row.get("kind") == "validated-positive"
    ]
    require(len(positive_rows) == 1, "exactly one validated-positive stratum is required")
    positive = positive_rows[0]
    expected_count = positive["expected_validated_finding_count"]
    expected_population: dict[str, list[str]] | None = None
    positive_summaries: dict[str, Any] = {}
    for policy_label in policies:
        validation = validations[policy_label]
        require(
            validation.get("schema") == VALIDATION_SCHEMA,
            f"{policy_label} positive validation schema differs",
        )
        require(
            validation.get("accepted") is True,
            f"{policy_label} positive validation was not accepted",
        )
        require(
            validation.get("validated_finding_count") == expected_count
            and validation.get("observed_high_confidence_count") == expected_count
            and validation.get("true_positive_count") == expected_count,
            f"{policy_label} positive population count differs",
        )
        require(
            validation.get("false_negative_count") == 0
            and validation.get("unexpected_high_confidence_count") == 0,
            f"{policy_label} positive population is not exact",
        )
        source = validation.get("source_verification")
        require(
            isinstance(source, dict)
            and source.get("accepted") is True
            and source.get("verified_file_count")
            == registration["source_verified_file_count"],
            f"{policy_label} source verification differs",
        )
        inputs = validation.get("inputs")
        require(isinstance(inputs, dict), f"{policy_label} validation inputs are missing")
        require(
            inputs.get("manifest", {}).get("sha256")
            == registration["source_manifest_sha256"],
            f"{policy_label} source manifest hash differs",
        )
        require(
            inputs.get("authority_report", {}).get("sha256")
            == report_hashes[policy_label][positive["name"]],
            f"{policy_label} positive authority report hash differs",
        )
        validation_drivers = validation.get("drivers")
        require(
            isinstance(validation_drivers, list),
            f"{policy_label} validation driver population is missing",
        )
        population: dict[str, list[str]] = {}
        for row in validation_drivers:
            require(
                isinstance(row, dict)
                and isinstance(row.get("sha256"), str)
                and isinstance(row.get("observed_high_confidence_findings"), list)
                and all(
                    isinstance(item, str)
                    for item in row["observed_high_confidence_findings"]
                ),
                f"{policy_label} validation driver row is malformed",
            )
            require(
                row["sha256"] not in population,
                f"{policy_label} validation repeats a driver identity",
            )
            population[row["sha256"]] = row["observed_high_confidence_findings"]
        require(
            set(population) == set(positive["driver_sha256"]),
            f"{policy_label} validated positive driver population differs",
        )
        if expected_population is None:
            expected_population = population
        else:
            require(
                population == expected_population,
                f"{policy_label} validated positive bytes differ",
            )
        positive_summaries[policy_label] = {
            "true_positive_count": validation["true_positive_count"],
            "false_negative_count": validation["false_negative_count"],
            "unexpected_high_confidence_count": validation[
                "unexpected_high_confidence_count"
            ],
            "recall": validation.get("recall"),
            "precision": validation.get("precision"),
            "authority_report_sha256": report_hashes[policy_label][positive["name"]],
        }

    discovery: dict[str, Any] = {}
    for stratum_label, stratum in strata.items():
        if stratum.get("kind") != "unlabeled-discovery":
            continue
        policy_summaries: dict[str, Any] = {}
        unions: dict[str, set[str]] = {"z3": set(), "axeyum": set()}
        for policy_label in policies:
            cell = cells[policy_label][stratum_label]
            backend_summaries: dict[str, Any] = {}
            for backend in ("z3", "axeyum"):
                raw = _flatten_population(cell, backend, "raw")
                high = _flatten_population(cell, backend, "high_confidence")
                diagnostic = _flatten_population(cell, backend, "diagnostic")
                unions[backend].update(raw)
                backend_summaries[backend] = {
                    "raw_count": len(raw),
                    "high_confidence_count": len(high),
                    "diagnostic_count": len(diagnostic),
                    "raw_findings": [_display_finding(row) for row in raw],
                    "high_confidence_findings": [
                        _display_finding(row) for row in high
                    ],
                    "diagnostic_findings": [
                        _display_finding(row) for row in diagnostic
                    ],
                    "drivers": {
                        sha256: driver["backends"][backend]
                        for sha256, driver in cell["drivers"].items()
                    },
                }
            policy_summaries[policy_label] = backend_summaries
        discovery[stratum_label] = {
            "classification": "unlabeled discovery output; not recall ground truth",
            "policies": policy_summaries,
            "raw_union": {
                "z3_count": len(unions["z3"]),
                "axeyum_count": len(unions["axeyum"]),
                "shared": [
                    _display_finding(row)
                    for row in sorted(unions["z3"] & unions["axeyum"])
                ],
                "z3_only": [
                    _display_finding(row)
                    for row in sorted(unions["z3"] - unions["axeyum"])
                ],
                "axeyum_only": [
                    _display_finding(row)
                    for row in sorted(unions["axeyum"] - unions["z3"])
                ],
            },
        }

    return {
        "schema": OUTPUT_SCHEMA,
        "accepted": True,
        "registration_name": registration.get("name"),
        "glaurung_revision": registration["glaurung_revision"],
        "axeyum_revision": axeyum_identity["revision"] if axeyum_identity else None,
        "authority_binaries": binaries,
        "policy_order": list(policies),
        "positive_control": {
            "stratum": positive["name"],
            "validated_finding_count": expected_count,
            "policies": positive_summaries,
        },
        "discovery": discovery,
        "claim_limits": [
            "The validated denominator contains planted fixtures, not a representative real-driver sample.",
            "Policy-dependent discovery rows remain unlabeled until source and machine validation.",
            "Five deterministic settings do not enumerate all satisfying models.",
            "Policy-dependent solve work and process time are descriptive integration costs, not solver-speed cells.",
            "BoundarySet and DiverseEnum remain unmeasured until bounded set forking is executable; symbolic memory remains conditional.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, required=True)
    parser.add_argument("--reports-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    registration = load_json(args.registration)
    policies = [row["label"] for row in registration["policies"]]
    strata = [row["name"] for row in registration["strata"]]
    reports: dict[str, dict[str, dict[str, Any]]] = {}
    validations: dict[str, dict[str, Any]] = {}
    hashes: dict[str, dict[str, str]] = {}
    for policy in policies:
        policy_dir = args.reports_dir / policy
        reports[policy] = {}
        hashes[policy] = {}
        for stratum in strata:
            path = policy_dir / f"{stratum}-report.json"
            reports[policy][stratum] = load_json(path)
            hashes[policy][stratum] = file_sha256(path)
        validations[policy] = load_json(
            policy_dir / "positive-control-validation.json"
        )
    result = analyze_sweep(registration, reports, validations, hashes)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
