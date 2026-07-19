#!/usr/bin/env python3
"""Run the preregistered point-major usbprint policy/resource frontier."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


REGISTRATION_SCHEMA = "axeyum.glaurung-usbprint-frontier-preregistration.v1"
EXECUTION_SCHEMA = "axeyum.glaurung-usbprint-frontier-execution.v1"
EXPECTED_POLICIES = [
    ("any-model", "glaurung-any-model-v1", None),
    ("min-unsigned", "glaurung-min-unsigned-v1", "min-unsigned"),
    ("max-unsigned", "glaurung-max-unsigned-v1", "max-unsigned"),
    ("site-hash-0", "glaurung-site-hash-0-v1", "site-hash-0"),
    ("site-hash-1", "glaurung-site-hash-1-v1", "site-hash-1"),
]
EXPECTED_POINTS = [("prefix-5", 5), ("prefix-10", 10), ("prefix-15", 15)]
RESOURCE_ERROR = "analysis hit the wall-clock safety deadline"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def git_identity(repository: Path) -> dict[str, Any]:
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=repository,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return {
        "revision": revision,
        "tracked_dirty": bool(status),
        "tracked_status_sha256": hashlib.sha256(status.encode()).hexdigest(),
    }


def prepare_output_directory(path: Path) -> None:
    if path.exists():
        require(path.is_dir(), f"output path is not a directory: {path}")
        require(not any(path.iterdir()), f"output directory is nonempty: {path}")
    else:
        path.mkdir(parents=True)


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "unsupported usbprint frontier preregistration schema",
    )
    policies = registration.get("policies")
    require(isinstance(policies, list), "preregistration has no policies")
    observed_policies = [
        (row.get("label"), row.get("policy_id"), row.get("harness_choice"))
        for row in policies
        if isinstance(row, dict)
    ]
    require(observed_policies == EXPECTED_POLICIES, "policy order or identity differs")
    points = registration.get("points")
    require(isinstance(points, list), "preregistration has no frontier points")
    observed_points = [
        (row.get("label"), row.get("max_analyzed_functions"))
        for row in points
        if isinstance(row, dict)
    ]
    require(observed_points == EXPECTED_POINTS, "frontier points differ")
    require(
        registration.get("acceptance", {}).get("population") == "high-confidence",
        "frontier must accept only on the high-confidence population",
    )
    require(
        isinstance(registration.get("claim_limits"), list)
        and bool(registration["claim_limits"])
        and all(isinstance(row, str) and row for row in registration["claim_limits"]),
        "preregistration has no claim limits",
    )
    for point in points:
        work = point.get("work") if isinstance(point, dict) else None
        require(isinstance(work, dict), "frontier point has no work boundary")
        for key in (
            "repetitions",
            "deadline_secs",
            "solve_budget",
            "solve_secs",
            "process_timeout_secs",
            "check_timeout_ms",
        ):
            require(
                isinstance(work.get(key), int)
                and not isinstance(work[key], bool)
                and work[key] > 0,
                f"frontier point has invalid work field {key}",
            )
        require(work["repetitions"] >= 2, "frontier requires at least two repetitions")
        require(
            work["process_timeout_secs"] > work["deadline_secs"],
            "process timeout must exceed the in-process deadline",
        )
    driver = registration.get("driver")
    require(
        isinstance(driver, dict)
        and isinstance(driver.get("sha256"), str)
        and bool(driver["sha256"]),
        "preregistration has no driver identity",
    )
    binary_hashes = registration.get("authority_binary_sha256")
    require(
        isinstance(binary_hashes, dict)
        and set(binary_hashes) == {"z3", "axeyum"}
        and all(isinstance(value, str) and value for value in binary_hashes.values()),
        "preregistration has no exact authority binary identity",
    )
    require(
        isinstance(registration.get("glaurung_revision"), str)
        and bool(registration["glaurung_revision"]),
        "preregistration has no Glaurung revision",
    )


def cell_order(registration: dict[str, Any]) -> list[tuple[str, str]]:
    return [
        (point["label"], policy["label"])
        for point in registration["points"]
        for policy in registration["policies"]
    ]


def measure_command(
    *,
    python_executable: str,
    measure_script: Path,
    glaurung_repo: Path,
    z3_binary: Path,
    axeyum_binary: Path,
    driver: Path,
    policy: dict[str, Any],
    point: dict[str, Any],
    out: Path,
) -> list[str]:
    work = point["work"]
    command = [
        python_executable,
        str(measure_script),
        "--glaurung-repo",
        str(glaurung_repo),
        "--z3-binary",
        str(z3_binary),
        "--axeyum-binary",
        str(axeyum_binary),
        "--driver",
        str(driver),
        "--repetitions",
        str(work["repetitions"]),
        "--deadline-secs",
        str(work["deadline_secs"]),
        "--max-analyzed-functions",
        str(point["max_analyzed_functions"]),
        "--solve-budget",
        str(work["solve_budget"]),
        "--solve-secs",
        str(work["solve_secs"]),
        "--process-timeout-secs",
        str(work["process_timeout_secs"]),
        "--check-timeout-ms",
        str(work["check_timeout_ms"]),
        "--acceptance-population",
        "high-confidence",
    ]
    if policy["harness_choice"] is not None:
        command.extend(("--concretization-policy", policy["harness_choice"]))
    command.extend(("--out", str(out)))
    return command


def classify_report(report: dict[str, Any]) -> str:
    if report.get("accepted") is True:
        return "complete"
    drivers = report.get("drivers")
    if not isinstance(drivers, list) or len(drivers) != 1:
        return "protocol-failure"
    runs = drivers[0].get("runs") if isinstance(drivers[0], dict) else None
    if not isinstance(runs, list) or len(runs) != 4:
        return "protocol-failure"
    expected = [
        ("z3", 1, 1),
        ("axeyum", 1, 2),
        ("axeyum", 2, 1),
        ("z3", 2, 2),
    ]
    observed = [
        (run.get("backend"), run.get("repetition"), run.get("position"))
        for run in runs
        if isinstance(run, dict)
    ]
    if observed != expected:
        return "protocol-failure"
    if all(run.get("run_error") == RESOURCE_ERROR for run in runs):
        post = report.get("post_run_source_identity")
        if isinstance(post, dict) and post.get("stable") is True:
            return "resource-bound"
    return "protocol-failure"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--glaurung-repo", type=Path, required=True)
    parser.add_argument("--z3-binary", type=Path, required=True)
    parser.add_argument("--axeyum-binary", type=Path, required=True)
    parser.add_argument("--driver", type=Path, required=True)
    args = parser.parse_args()

    repository_root = Path(__file__).resolve().parents[1]
    registration_path = args.registration.resolve()
    registration = load_json(registration_path)
    validate_registration(registration)
    glaurung_repo = args.glaurung_repo.resolve()
    z3_binary = args.z3_binary.resolve()
    axeyum_binary = args.axeyum_binary.resolve()
    driver = args.driver.resolve()
    for path in (glaurung_repo,):
        require(path.is_dir(), f"repository does not exist: {path}")
    for path in (z3_binary, axeyum_binary, driver):
        require(path.is_file(), f"input does not exist: {path}")
    for path in (z3_binary, axeyum_binary):
        require(os.access(path, os.X_OK), f"authority binary is not executable: {path}")

    axeyum_identity = git_identity(repository_root)
    glaurung_identity = git_identity(glaurung_repo)
    require(not axeyum_identity["tracked_dirty"], "Axeyum source is tracked-dirty")
    require(not glaurung_identity["tracked_dirty"], "Glaurung source is tracked-dirty")
    require(
        glaurung_identity["revision"] == registration["glaurung_revision"],
        "Glaurung revision differs from preregistration",
    )
    require(
        file_sha256(driver) == registration["driver"]["sha256"],
        "usbprint driver differs from preregistration",
    )
    for label, path in (("z3", z3_binary), ("axeyum", axeyum_binary)):
        require(
            file_sha256(path) == registration["authority_binary_sha256"][label],
            f"{label} authority binary differs from preregistration",
        )

    out_dir = args.out_dir.resolve()
    prepare_output_directory(out_dir)
    shutil.copyfile(registration_path, out_dir / "preregistration.json")
    measure_script = repository_root / "scripts/measure-glaurung-authoritative-findings.py"
    cells: list[dict[str, Any]] = []
    stop = False
    for point in registration["points"]:
        for policy in registration["policies"]:
            cell_dir = out_dir / point["label"] / policy["label"]
            cell_dir.mkdir(parents=True)
            report_path = cell_dir / "report.json"
            command = measure_command(
                python_executable=sys.executable,
                measure_script=measure_script,
                glaurung_repo=glaurung_repo,
                z3_binary=z3_binary,
                axeyum_binary=axeyum_binary,
                driver=driver,
                policy=policy,
                point=point,
                out=report_path,
            )
            with (cell_dir / "stdout.log").open("w") as stdout, (
                cell_dir / "stderr.log"
            ).open("w") as stderr:
                completed = subprocess.run(command, stdout=stdout, stderr=stderr, text=True)
            if report_path.is_file():
                report = load_json(report_path)
                classification = classify_report(report)
                report_hash = file_sha256(report_path)
            else:
                classification = "protocol-failure"
                report_hash = None
            cells.append(
                {
                    "point": point["label"],
                    "max_analyzed_functions": point["max_analyzed_functions"],
                    "policy": policy["label"],
                    "policy_id": policy["policy_id"],
                    "returncode": completed.returncode,
                    "classification": classification,
                    "report": str(report_path.relative_to(out_dir)),
                    "report_sha256": report_hash,
                }
            )
            if classification != "complete":
                stop = True
                break
        if stop:
            break

    post_axeyum = git_identity(repository_root)
    post_glaurung = git_identity(glaurung_repo)
    identity_stable = axeyum_identity == post_axeyum and glaurung_identity == post_glaurung
    execution = {
        "schema": EXECUTION_SCHEMA,
        "registration_sha256": file_sha256(registration_path),
        "axeyum": axeyum_identity,
        "glaurung": glaurung_identity,
        "post_run_axeyum": post_axeyum,
        "post_run_glaurung": post_glaurung,
        "source_identity_stable": identity_stable,
        "authority_binaries": {
            "z3": {"path": str(z3_binary), "sha256": file_sha256(z3_binary)},
            "axeyum": {"path": str(axeyum_binary), "sha256": file_sha256(axeyum_binary)},
        },
        "driver": {"path": str(driver), "sha256": file_sha256(driver)},
        "cell_order": cell_order(registration),
        "cells": cells,
    }
    (out_dir / "execution-manifest.json").write_text(
        json.dumps(execution, indent=2, sort_keys=True) + "\n"
    )
    return 0 if identity_stable and all(
        cell["classification"] != "protocol-failure" for cell in cells
    ) else 1


if __name__ == "__main__":
    raise SystemExit(main())
