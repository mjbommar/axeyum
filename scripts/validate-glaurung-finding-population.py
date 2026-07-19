#!/usr/bin/env python3
"""Join a source-validated finding manifest to a Glaurung authority report.

The producer's confidence partition is useful triage metadata, but it is not
ground truth.  This validator therefore accepts only an exact, non-empty join
between an independently reviewed manifest and the stable high-confidence set
reported by both solver-authoritative executions.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


MANIFEST_SCHEMA = "axeyum.glaurung-validated-finding-manifest.v1"
AUTHORITY_SCHEMA_V5 = "axeyum.glaurung-authoritative-finding-parity.v5"
AUTHORITY_SCHEMA_V6 = "axeyum.glaurung-authoritative-finding-parity.v6"
AUTHORITY_SCHEMAS = {AUTHORITY_SCHEMA_V5, AUTHORITY_SCHEMA_V6}
OUTPUT_SCHEMA = "axeyum.glaurung-validated-finding-population.v1"
VALIDATION_POLICY = "exact-high-confidence-set"
EXPLORATION_LIMIT_KEYS = (
    "runs",
    "completed",
    "state_budget",
    "solve_budget",
    "timeout_budget",
    "deadline",
)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _string_list(value: Any) -> list[str] | None:
    if not isinstance(value, list) or not all(isinstance(row, str) for row in value):
        return None
    return value


def _identity_is_clean(report: dict[str, Any], name: str) -> bool:
    identity = report.get(name)
    return (
        isinstance(identity, dict)
        and isinstance(identity.get("revision"), str)
        and bool(identity["revision"])
        and identity.get("tracked_dirty") is False
    )


def _safe_relative_path(value: Any) -> str | None:
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        return None
    return value


def verify_source_repository(
    manifest: dict[str, Any], repository: Path
) -> dict[str, Any]:
    """Verify that every manifest source/binary is tracked, clean, and exact."""

    failures: list[str] = []
    repository = repository.resolve()
    source_repository = manifest.get("source_repository")
    expected_revision = (
        source_repository.get("revision")
        if isinstance(source_repository, dict)
        else None
    )
    try:
        observed_revision = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repository,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as error:
        return {
            "accepted": False,
            "expected_revision": expected_revision,
            "observed_revision": None,
            "verified_file_count": 0,
            "files": [],
            "failures": [f"cannot identify source repository: {error}"],
        }
    if not isinstance(expected_revision, str) or not expected_revision:
        failures.append("manifest has no source repository revision")
    elif observed_revision != expected_revision:
        failures.append(
            "source repository revision differs: "
            f"expected {expected_revision}, observed {observed_revision}"
        )

    file_expectations: dict[str, str] = {}

    def add_file_expectation(path_value: Any, sha_value: Any, label: str) -> None:
        relative_path = _safe_relative_path(path_value)
        if relative_path is None:
            failures.append(f"unsafe source fixture path: {path_value!r}")
            return
        if not isinstance(sha_value, str) or not sha_value:
            failures.append(f"{label} lacks a SHA-256 identity")
            return
        previous = file_expectations.get(relative_path)
        if previous is not None and previous != sha_value:
            failures.append(f"conflicting source fixture identity: {relative_path}")
            return
        file_expectations[relative_path] = sha_value

    drivers = manifest.get("drivers")
    if not isinstance(drivers, list):
        drivers = []
    for index, driver in enumerate(drivers):
        if not isinstance(driver, dict):
            continue
        binary_path = driver.get("binary_path")
        binary_sha256 = driver.get("sha256")
        add_file_expectation(
            binary_path, binary_sha256, f"manifest driver {index} binary"
        )
        source = driver.get("source")
        if isinstance(source, dict):
            add_file_expectation(
                source.get("path"),
                source.get("sha256"),
                f"manifest driver {index} source",
            )
        else:
            failures.append(f"manifest driver {index} lacks source-file identity")

    relative_paths = sorted(file_expectations)
    if relative_paths:
        status = subprocess.run(
            [
                "git",
                "status",
                "--porcelain",
                "--untracked-files=all",
                "--",
                *relative_paths,
            ],
            cwd=repository,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        if status:
            failures.append("source repository tracked fixture tree is dirty")

    verified_files: list[dict[str, Any]] = []
    for relative_path in relative_paths:
        candidate = repository / relative_path
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", "--", relative_path],
            cwd=repository,
            capture_output=True,
            text=True,
        ).returncode == 0
        if not tracked:
            failures.append(f"source fixture is not tracked: {relative_path}")
        observed_sha256 = file_sha256(candidate) if candidate.is_file() else None
        expected_sha256 = file_expectations[relative_path]
        if observed_sha256 is None:
            failures.append(f"source fixture is missing: {relative_path}")
        elif observed_sha256 != expected_sha256:
            failures.append(f"source fixture SHA-256 mismatch: {relative_path}")
        verified_files.append(
            {
                "path": relative_path,
                "tracked": tracked,
                "expected_sha256": expected_sha256,
                "observed_sha256": observed_sha256,
            }
        )

    return {
        "accepted": not failures,
        "expected_revision": expected_revision,
        "observed_revision": observed_revision,
        "verified_file_count": len(verified_files),
        "files": verified_files,
        "failures": failures,
    }


def _stable_high_findings(
    driver: dict[str, Any], failures: list[str], label: str
) -> list[str]:
    """Return the common high-confidence set after rechecking every v5 run."""

    if driver.get("summary_error") is not None:
        failures.append(f"{label}: authority summary contains an error")
    summary = driver.get("summary")
    if not isinstance(summary, dict):
        failures.append(f"{label}: authority summary is missing")
        return []
    if summary.get("confidence_partition_available") is not True:
        failures.append(f"{label}: confidence partition is unavailable")
    if summary.get("exact_high_confidence_finding_parity") is not True:
        failures.append(f"{label}: summary does not report exact high-confidence parity")

    high_summary = summary.get("high_confidence")
    if not isinstance(high_summary, dict):
        failures.append(f"{label}: high-confidence summary is missing")
    else:
        if high_summary.get("exact_finding_parity") is not True:
            failures.append(f"{label}: high-confidence authority sets diverge")
        stability = high_summary.get("stability")
        if not isinstance(stability, dict):
            failures.append(f"{label}: high-confidence stability summary is missing")
        else:
            for backend in ("z3", "axeyum"):
                backend_stability = stability.get(backend)
                if not isinstance(backend_stability, dict) or backend_stability.get(
                    "output_stable"
                ) is not True:
                    failures.append(
                        f"{label}: {backend} high-confidence output is not stable"
                    )

    runs = driver.get("runs")
    if not isinstance(runs, list) or not runs:
        failures.append(f"{label}: authority runs are missing")
        return []

    per_backend: dict[str, dict[int, list[str]]] = {"z3": {}, "axeyum": {}}
    for index, run in enumerate(runs):
        if not isinstance(run, dict):
            failures.append(f"{label}: authority run {index} is malformed")
            continue
        backend = run.get("backend")
        if backend not in per_backend:
            failures.append(f"{label}: authority run {index} has unknown backend")
            continue
        repetition = run.get("repetition")
        if not isinstance(repetition, int) or repetition < 1:
            failures.append(f"{label}: {backend} run {index} has invalid repetition")
            continue
        if repetition in per_backend[backend]:
            failures.append(
                f"{label}: {backend} repeats repetition {repetition}"
            )
            continue
        if run.get("confidence_partition_available") is not True:
            failures.append(
                f"{label}: {backend} run {index} lacks a confidence partition"
            )
        findings = _string_list(run.get("high_confidence_findings"))
        if findings is None:
            failures.append(
                f"{label}: {backend} run {index} has malformed high-confidence findings"
            )
            continue
        if len(findings) != len(set(findings)):
            failures.append(
                f"{label}: {backend} run {index} repeats a high-confidence finding"
            )
        if run.get("high_confidence_finding_count") != len(findings):
            failures.append(
                f"{label}: {backend} run {index} high-confidence count is inconsistent"
            )
        per_backend[backend][repetition] = sorted(set(findings))

    stable: dict[str, list[str]] = {}
    for backend, observations in per_backend.items():
        if not observations:
            failures.append(f"{label}: no {backend} authority run is present")
            stable[backend] = []
            continue
        if len(observations) < 2:
            failures.append(f"{label}: {backend} requires at least two repetitions")
        ordered = [observations[key] for key in sorted(observations)]
        first = ordered[0]
        if any(row != first for row in ordered[1:]):
            failures.append(
                f"{label}: {backend} high-confidence findings vary across repetitions"
            )
        stable[backend] = first

    if set(per_backend["z3"]) != set(per_backend["axeyum"]):
        failures.append(f"{label}: authority repetition populations differ")

    if stable["z3"] != stable["axeyum"]:
        failures.append(f"{label}: stable high-confidence authority sets diverge")
    return stable["z3"] if stable["z3"] == stable["axeyum"] else []


def _validate_deterministic_worklists(
    driver: dict[str, Any], failures: list[str], label: str
) -> None:
    """Recheck every required v6 worklist partition without trusting summary flags."""

    summary = driver.get("summary")
    if not isinstance(summary, dict):
        failures.append(f"{label}: deterministic-worklist summary is missing")
        return
    if summary.get("deterministic_worklists_verified") is not True:
        failures.append(f"{label}: deterministic worklists are not verified")
    summary_limits = summary.get("exploration_limits")
    summary_backends = (
        summary_limits.get("backends")
        if isinstance(summary_limits, dict)
        else None
    )
    if not isinstance(summary_backends, dict):
        failures.append(f"{label}: exploration-limit summary is missing")
        summary_backends = {}

    runs = driver.get("runs")
    if not isinstance(runs, list) or not runs:
        failures.append(f"{label}: authority runs are missing")
        return
    per_backend: dict[str, list[tuple[int, ...]]] = {"z3": [], "axeyum": []}
    for index, run in enumerate(runs):
        if not isinstance(run, dict):
            continue
        backend = run.get("backend")
        if backend not in per_backend:
            continue
        telemetry = run.get("exploration_limits")
        if not isinstance(telemetry, dict):
            failures.append(
                f"{label}: {backend} run {index} lacks exploration-limit telemetry"
            )
            continue
        if any(
            type(telemetry.get(key)) is not int or telemetry[key] < 0
            for key in EXPLORATION_LIMIT_KEYS
        ):
            failures.append(
                f"{label}: {backend} run {index} has malformed exploration-limit telemetry"
            )
            continue
        row = tuple(telemetry[key] for key in EXPLORATION_LIMIT_KEYS)
        if sum(row[1:]) != row[0]:
            failures.append(
                f"{label}: {backend} run {index} has inconsistent exploration-limit accounting"
            )
        if telemetry["timeout_budget"] or telemetry["deadline"]:
            failures.append(f"{label}: {backend} run {index} has a deadline/timeout stop")
        per_backend[backend].append(row)

    for backend, rows in per_backend.items():
        if not rows:
            continue
        if len(set(rows)) != 1:
            failures.append(f"{label}: {backend} exploration-limit telemetry drifts")
            continue
        observed = dict(zip(EXPLORATION_LIMIT_KEYS, rows[0]))
        if summary_backends.get(backend) != observed:
            failures.append(
                f"{label}: {backend} exploration-limit summary differs from runs"
            )


def validate_population(
    manifest: dict[str, Any], authority_report: dict[str, Any]
) -> dict[str, Any]:
    """Validate and summarize an exact source-backed finding population."""

    failures: list[str] = []
    if manifest.get("schema") != MANIFEST_SCHEMA:
        failures.append("unsupported validated-finding manifest schema")
    if manifest.get("validation_policy") != VALIDATION_POLICY:
        failures.append("manifest does not select exact-high-confidence-set validation")

    source_repository = manifest.get("source_repository")
    source_revision = (
        source_repository.get("revision")
        if isinstance(source_repository, dict)
        else None
    )
    if not isinstance(source_revision, str) or not source_revision:
        failures.append("manifest has no source repository revision")
    if (
        not isinstance(source_repository, dict)
        or source_repository.get("tracked_fixture_tree_clean") is not True
    ):
        failures.append("manifest does not attest a clean tracked fixture tree")

    manifest_drivers = manifest.get("drivers")
    if not isinstance(manifest_drivers, list):
        failures.append("validated-finding manifest has no driver list")
        manifest_drivers = []

    validated_by_sha: dict[str, dict[str, Any]] = {}
    validated_count = 0
    for index, driver in enumerate(manifest_drivers):
        label = f"manifest driver {index}"
        if not isinstance(driver, dict):
            failures.append(f"{label} is malformed")
            continue
        sha256 = driver.get("sha256")
        if not isinstance(sha256, str) or not sha256:
            failures.append(f"{label} has no SHA-256 identity")
            continue
        if sha256 in validated_by_sha:
            failures.append(f"manifest repeats driver SHA-256 {sha256}")
            continue

        expected = _string_list(driver.get("expected_findings"))
        if expected is None:
            failures.append(f"{label} has malformed expected findings")
            expected = []
        if len(expected) != len(set(expected)):
            failures.append(f"{label} repeats an expected finding")
        expected = sorted(set(expected))

        source = driver.get("source")
        if not isinstance(source, dict) or any(
            not isinstance(source.get(key), str) or not source[key]
            for key in ("repository_revision", "path", "sha256")
        ):
            failures.append(f"{label} lacks complete source identity")
        elif source.get("repository_revision") != source_revision:
            failures.append(f"{label} source revision differs from repository revision")
        if not isinstance(driver.get("binary_path"), str) or not driver.get(
            "binary_path"
        ):
            failures.append(f"{label} lacks a binary path")

        basis = driver.get("validation_basis")
        basis_findings: list[str] = []
        if not isinstance(basis, list):
            failures.append(f"{label} lacks a validation basis")
        else:
            for basis_index, row in enumerate(basis):
                if not isinstance(row, dict) or not isinstance(row.get("finding"), str):
                    failures.append(
                        f"{label} validation basis {basis_index} is malformed"
                    )
                    continue
                if not row["finding"]:
                    failures.append(
                        f"{label} validation basis {basis_index} has an empty finding"
                    )
                if not isinstance(row.get("source_lines"), str) or not row.get(
                    "source_lines"
                ):
                    failures.append(
                        f"{label} validation basis {basis_index} lacks source lines"
                    )
                if not isinstance(row.get("machine_evidence"), str) or not row.get(
                    "machine_evidence"
                ):
                    failures.append(
                        f"{label} validation basis {basis_index} lacks machine evidence"
                    )
                basis_findings.append(row["finding"])
        if sorted(basis_findings) != expected:
            failures.append(
                f"{label} validation basis does not exactly cover expected findings"
            )

        validated_count += len(expected)
        validated_by_sha[sha256] = {**driver, "expected_findings": expected}

    if validated_count == 0:
        failures.append("validated denominator is empty")

    authority_schema = authority_report.get("schema")
    if authority_schema not in AUTHORITY_SCHEMAS:
        failures.append("unsupported authority report schema")
    require_deterministic_worklists = authority_schema == AUTHORITY_SCHEMA_V6
    if require_deterministic_worklists and (
        authority_report.get("deterministic_worklists_required") is not True
    ):
        failures.append("v6 authority report does not require deterministic worklists")
    if authority_report.get("accepted") is not True:
        failures.append("authority report was not accepted")
    if authority_report.get("acceptance_population") != "high-confidence":
        failures.append("authority report did not accept the high-confidence population")
    if (
        authority_report.get("all_drivers_exact_high_confidence_finding_parity")
        is not True
    ):
        failures.append("authority report lacks exact high-confidence parity")
    post_identity = authority_report.get("post_run_source_identity")
    if not isinstance(post_identity, dict) or post_identity.get("stable") is not True:
        failures.append("authority source identity changed during measurement")
    if not _identity_is_clean(authority_report, "glaurung"):
        failures.append("authority report does not identify a clean Glaurung revision")
    if not _identity_is_clean(authority_report, "axeyum"):
        failures.append("authority report does not identify a clean Axeyum revision")
    if isinstance(post_identity, dict):
        for name in ("glaurung", "axeyum"):
            before = authority_report.get(name)
            after = post_identity.get(name)
            if not isinstance(after, dict) or not _identity_is_clean(
                post_identity, name
            ):
                failures.append(
                    f"authority post-run identity does not identify clean {name} source"
                )
            elif not isinstance(before, dict) or any(
                before.get(key) != after.get(key)
                for key in ("revision", "tracked_dirty", "tracked_status_sha256")
            ):
                failures.append(f"authority {name} source identity changed during measurement")

    authority_drivers = authority_report.get("drivers")
    if not isinstance(authority_drivers, list):
        failures.append("authority report has no driver list")
        authority_drivers = []
    authority_by_sha: dict[str, dict[str, Any]] = {}
    for index, driver in enumerate(authority_drivers):
        if not isinstance(driver, dict):
            failures.append(f"authority driver {index} is malformed")
            continue
        identity = driver.get("driver")
        sha256 = identity.get("sha256") if isinstance(identity, dict) else None
        if not isinstance(sha256, str) or not sha256:
            failures.append(f"authority driver {index} has no SHA-256 identity")
            continue
        if sha256 in authority_by_sha:
            failures.append(f"authority report repeats driver SHA-256 {sha256}")
            continue
        authority_by_sha[sha256] = driver

    if set(validated_by_sha) != set(authority_by_sha):
        failures.append("validated and authority driver population differs")

    driver_results: list[dict[str, Any]] = []
    observed_count = 0
    true_positive_count = 0
    false_negative_count = 0
    unexpected_count = 0
    for sha256, validated in validated_by_sha.items():
        expected = validated["expected_findings"]
        authority_driver = authority_by_sha.get(sha256)
        driver_label = f"driver {validated.get('name', sha256)}"
        if authority_driver is not None and require_deterministic_worklists:
            _validate_deterministic_worklists(
                authority_driver, failures, driver_label
            )
        observed = (
            _stable_high_findings(authority_driver, failures, driver_label)
            if authority_driver is not None
            else []
        )
        true_positives = sorted(set(expected) & set(observed))
        false_negatives = sorted(set(expected) - set(observed))
        unexpected = sorted(set(observed) - set(expected))
        if false_negatives:
            failures.append(
                f"driver {validated.get('name', sha256)}: validated findings were missed"
            )
        if unexpected:
            failures.append(
                f"driver {validated.get('name', sha256)}: unexpected high-confidence findings were observed"
            )
        observed_count += len(observed)
        true_positive_count += len(true_positives)
        false_negative_count += len(false_negatives)
        unexpected_count += len(unexpected)
        driver_results.append(
            {
                "name": validated.get("name"),
                "sha256": sha256,
                "source": validated.get("source"),
                "validation_basis": validated.get("validation_basis"),
                "expected_findings": expected,
                "observed_high_confidence_findings": observed,
                "true_positives": true_positives,
                "false_negatives": false_negatives,
                "unexpected_high_confidence": unexpected,
            }
        )

    result: dict[str, Any] = {
        "schema": OUTPUT_SCHEMA,
        "accepted": not failures,
        "validation_policy": VALIDATION_POLICY,
        "manifest_name": manifest.get("name"),
        "glaurung_revision": authority_report.get("glaurung", {}).get("revision"),
        "axeyum_revision": authority_report.get("axeyum", {}).get("revision"),
        "validated_finding_count": validated_count,
        "observed_high_confidence_count": observed_count,
        "true_positive_count": true_positive_count,
        "false_negative_count": false_negative_count,
        "unexpected_high_confidence_count": unexpected_count,
        "recall": (
            true_positive_count / validated_count if validated_count else None
        ),
        "precision": true_positive_count / observed_count if observed_count else None,
        "drivers": driver_results,
        "failures": failures,
    }
    if require_deterministic_worklists:
        result.update(
            {
                "authority_report_schema": authority_schema,
                "deterministic_worklists_required": True,
            }
        )
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--authority-report", type=Path, required=True)
    parser.add_argument("--source-repository", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    with args.manifest.open(encoding="utf-8") as source:
        manifest = json.load(source)
    with args.authority_report.open(encoding="utf-8") as source:
        authority_report = json.load(source)
    result = validate_population(manifest, authority_report)
    source_verification = verify_source_repository(manifest, args.source_repository)
    result["source_verification"] = source_verification
    result["failures"].extend(source_verification["failures"])
    result["accepted"] = not result["failures"]
    result["inputs"] = {
        "manifest": {
            "sha256": file_sha256(args.manifest),
        },
        "authority_report": {
            "sha256": file_sha256(args.authority_report),
        },
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is None:
        print(rendered, end="")
    else:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
