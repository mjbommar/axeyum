#!/usr/bin/env python3
"""Run the preregistered Glaurung A0 policy sweep without outcome adaptation."""

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


REGISTRATION_SCHEMA = "axeyum.glaurung-concretization-sweep-preregistration.v1"
EXPECTED_POLICIES = [
    ("any-model", "glaurung-any-model-v1", None),
    ("min-unsigned", "glaurung-min-unsigned-v1", "min-unsigned"),
    ("max-unsigned", "glaurung-max-unsigned-v1", "max-unsigned"),
    ("site-hash-0", "glaurung-site-hash-0-v1", "site-hash-0"),
    ("site-hash-1", "glaurung-site-hash-1-v1", "site-hash-1"),
]


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
    with path.open(encoding="utf-8") as source:
        value = json.load(source)
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


def _resolve_repository_path(repository_root: Path, value: str) -> Path:
    path = Path(value)
    return path.resolve() if path.is_absolute() else (repository_root / path).resolve()


def resolve_driver_inputs(
    registration: dict[str, Any],
    *,
    repository_root: Path,
    source_repository: Path,
    named_inputs: dict[str, Path],
) -> dict[str, list[Path]]:
    """Resolve and hash-check positive-manifest and named discovery drivers."""

    manifest_path = _resolve_repository_path(
        repository_root, registration["source_manifest_path"]
    )
    require(manifest_path.is_file(), f"source manifest does not exist: {manifest_path}")
    require(
        file_sha256(manifest_path) == registration["source_manifest_sha256"],
        "source manifest hash differs from preregistration",
    )
    manifest = load_json(manifest_path)
    manifest_drivers = manifest.get("drivers")
    require(isinstance(manifest_drivers, list), "source manifest has no driver list")
    positive_paths: list[Path] = []
    positive_sha256: list[str] = []
    for index, row in enumerate(manifest_drivers):
        require(isinstance(row, dict), f"source manifest driver {index} is malformed")
        relative = row.get("binary_path")
        expected_sha256 = row.get("sha256")
        require(
            isinstance(relative, str) and relative and not Path(relative).is_absolute(),
            f"source manifest driver {index} has an unsafe binary path",
        )
        require(".." not in Path(relative).parts, f"unsafe binary path: {relative}")
        driver = (source_repository / relative).resolve()
        require(driver.is_file(), f"source manifest binary does not exist: {driver}")
        require(
            isinstance(expected_sha256, str)
            and file_sha256(driver) == expected_sha256,
            f"source manifest binary hash differs: {driver}",
        )
        positive_paths.append(driver)
        positive_sha256.append(expected_sha256)

    resolved: dict[str, list[Path]] = {}
    used_named_inputs: set[str] = set()
    for stratum in registration["strata"]:
        name = stratum["name"]
        source = stratum["driver_source"]
        expected = stratum["driver_sha256"]
        if source == "source-manifest":
            require(
                positive_sha256 == expected,
                f"{name} manifest driver population differs from preregistration",
            )
            resolved[name] = positive_paths
            continue
        require(source in named_inputs, f"missing named driver input: {source}")
        used_named_inputs.add(source)
        driver = named_inputs[source].resolve()
        require(driver.is_file(), f"named driver input does not exist: {driver}")
        require(
            expected == [file_sha256(driver)],
            f"{name} driver hash differs from preregistration",
        )
        resolved[name] = [driver]
    require(
        set(named_inputs) == used_named_inputs,
        "named driver inputs differ from preregistered discovery inputs",
    )
    return resolved


def measure_command(
    *,
    python_executable: str,
    measure_script: Path,
    glaurung_repo: Path,
    z3_binary: Path,
    axeyum_binary: Path,
    drivers: list[Path],
    policy: dict[str, Any],
    work: dict[str, Any],
    out: Path,
) -> list[str]:
    command = [
        python_executable,
        str(measure_script),
        "--glaurung-repo",
        str(glaurung_repo),
        "--z3-binary",
        str(z3_binary),
        "--axeyum-binary",
        str(axeyum_binary),
    ]
    for driver in drivers:
        command.extend(("--driver", str(driver)))
    command.extend(
        (
            "--repetitions",
            str(work["repetitions"]),
            "--deadline-secs",
            str(work["deadline_secs"]),
            "--max-analyzed-functions",
            str(work["max_analyzed_functions"]),
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
        )
    )
    if policy["harness_choice"] is not None:
        command.extend(("--concretization-policy", policy["harness_choice"]))
    command.extend(("--out", str(out)))
    return command


def validate_registration(registration: dict[str, Any]) -> None:
    require(
        registration.get("schema") == REGISTRATION_SCHEMA,
        "unsupported preregistration schema",
    )
    require(
        isinstance(registration.get("acceptance"), dict),
        "preregistration has no acceptance policy",
    )
    require(
        isinstance(registration.get("claim_limits"), list)
        and registration["claim_limits"]
        and all(isinstance(row, str) and row for row in registration["claim_limits"]),
        "preregistration has no claim limits",
    )
    policies = registration.get("policies")
    require(isinstance(policies, list), "preregistration has no policy list")
    observed_policies = [
        (row.get("label"), row.get("policy_id"), row.get("harness_choice"))
        for row in policies
        if isinstance(row, dict)
    ]
    require(
        observed_policies == EXPECTED_POLICIES,
        "preregistered policy order or identity differs from the executable A0 set",
    )
    strata = registration.get("strata")
    require(isinstance(strata, list) and strata, "preregistration has no strata")
    require(
        len({row.get("name") for row in strata if isinstance(row, dict)})
        == len(strata),
        "preregistration repeats a stratum",
    )
    require(
        sum(
            isinstance(row, dict) and row.get("kind") == "validated-positive"
            for row in strata
        )
        == 1,
        "preregistration must contain exactly one validated-positive stratum",
    )
    for row in strata:
        require(isinstance(row, dict), "preregistration stratum is malformed")
        require(
            isinstance(row.get("driver_sha256"), list)
            and bool(row["driver_sha256"])
            and all(isinstance(value, str) and value for value in row["driver_sha256"]),
            f"{row.get('name')} has no exact driver population",
        )
        require(
            isinstance(row.get("driver_source"), str) and row["driver_source"],
            f"{row.get('name')} has no driver source",
        )
        work = row.get("work")
        require(isinstance(work, dict), f"{row.get('name')} has no work boundary")
        for key in (
            "repetitions",
            "deadline_secs",
            "max_analyzed_functions",
            "solve_budget",
            "solve_secs",
            "process_timeout_secs",
            "check_timeout_ms",
        ):
            require(
                isinstance(work.get(key), int)
                and not isinstance(work[key], bool)
                and work[key] > 0,
                f"{row.get('name')} has invalid work field {key}",
            )
        require(
            work["repetitions"] >= 2,
            f"{row.get('name')} must use at least two repetitions",
        )


def run_logged(command: list[str], stdout_path: Path, stderr_path: Path) -> None:
    with stdout_path.open("w", encoding="utf-8") as stdout, stderr_path.open(
        "w", encoding="utf-8"
    ) as stderr:
        completed = subprocess.run(command, stdout=stdout, stderr=stderr, text=True)
    require(
        completed.returncode == 0,
        f"command failed with status {completed.returncode}; see {stderr_path}",
    )


def parse_named_inputs(values: list[str]) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for value in values:
        require("=" in value, f"named driver input must be NAME=PATH: {value}")
        name, path = value.split("=", 1)
        require(name and path, f"named driver input must be NAME=PATH: {value}")
        require(name not in result, f"duplicate named driver input: {name}")
        result[name] = Path(path)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--glaurung-repo", type=Path, required=True)
    parser.add_argument("--z3-binary", type=Path, required=True)
    parser.add_argument("--axeyum-binary", type=Path, required=True)
    parser.add_argument("--positive-source-repo", type=Path, required=True)
    parser.add_argument(
        "--driver-input",
        action="append",
        default=[],
        metavar="NAME=PATH",
        help="bind one preregistered discovery input name to an exact local file",
    )
    args = parser.parse_args()

    repository_root = Path(__file__).resolve().parents[1]
    scripts = repository_root / "scripts"
    registration_path = args.registration.resolve()
    registration = load_json(registration_path)
    validate_registration(registration)

    glaurung_repo = args.glaurung_repo.resolve()
    z3_binary = args.z3_binary.resolve()
    axeyum_binary = args.axeyum_binary.resolve()
    source_repository = args.positive_source_repo.resolve()
    for path in (glaurung_repo, source_repository):
        require(path.is_dir(), f"repository does not exist: {path}")
    for path in (z3_binary, axeyum_binary):
        require(path.is_file(), f"authority binary does not exist: {path}")
        require(os.access(path, os.X_OK), f"authority binary is not executable: {path}")

    axeyum_identity = git_identity(repository_root)
    glaurung_identity = git_identity(glaurung_repo)
    require(not axeyum_identity["tracked_dirty"], "Axeyum source is tracked-dirty")
    require(not glaurung_identity["tracked_dirty"], "Glaurung source is tracked-dirty")
    require(
        glaurung_identity["revision"] == registration["glaurung_revision"],
        "Glaurung revision differs from preregistration",
    )
    for label, path in (("z3", z3_binary), ("axeyum", axeyum_binary)):
        require(
            file_sha256(path) == registration["authority_binary_sha256"][label],
            f"{label} authority binary differs from preregistration",
        )

    named_inputs = parse_named_inputs(args.driver_input)
    drivers = resolve_driver_inputs(
        registration,
        repository_root=repository_root,
        source_repository=source_repository,
        named_inputs=named_inputs,
    )

    out_dir = args.out_dir.resolve()
    prepare_output_directory(out_dir)
    shutil.copyfile(registration_path, out_dir / "preregistration.json")
    execution_manifest = {
        "schema": "axeyum.glaurung-concretization-sweep-execution.v1",
        "registration_sha256": file_sha256(registration_path),
        "axeyum": axeyum_identity,
        "glaurung": glaurung_identity,
        "authority_binaries": {
            "z3": {"path": str(z3_binary), "sha256": file_sha256(z3_binary)},
            "axeyum": {
                "path": str(axeyum_binary),
                "sha256": file_sha256(axeyum_binary),
            },
        },
        "source_repository": git_identity(source_repository),
        "drivers": {
            name: [
                {"path": str(path), "sha256": file_sha256(path)} for path in paths
            ]
            for name, paths in drivers.items()
        },
        "policy_order": [row["label"] for row in registration["policies"]],
        "stratum_order": [row["name"] for row in registration["strata"]],
    }
    (out_dir / "execution-manifest.json").write_text(
        json.dumps(execution_manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    measure_script = scripts / "measure-glaurung-authoritative-findings.py"
    validator_script = scripts / "validate-glaurung-finding-population.py"
    analyzer_script = scripts / "analyze-glaurung-concretization-sweep.py"
    manifest_path = _resolve_repository_path(
        repository_root, registration["source_manifest_path"]
    )
    positive_name = next(
        row["name"]
        for row in registration["strata"]
        if row["kind"] == "validated-positive"
    )
    for policy in registration["policies"]:
        policy_dir = out_dir / policy["label"]
        policy_dir.mkdir()
        for stratum in registration["strata"]:
            name = stratum["name"]
            report_path = policy_dir / f"{name}-report.json"
            command = measure_command(
                python_executable=sys.executable,
                measure_script=measure_script,
                glaurung_repo=glaurung_repo,
                z3_binary=z3_binary,
                axeyum_binary=axeyum_binary,
                drivers=drivers[name],
                policy=policy,
                work=stratum["work"],
                out=report_path,
            )
            run_logged(
                command,
                policy_dir / f"{name}.stdout.log",
                policy_dir / f"{name}.stderr.log",
            )
        validation_path = policy_dir / "positive-control-validation.json"
        validation_command = [
            sys.executable,
            str(validator_script),
            "--manifest",
            str(manifest_path),
            "--authority-report",
            str(policy_dir / f"{positive_name}-report.json"),
            "--source-repository",
            str(source_repository),
            "--out",
            str(validation_path),
        ]
        run_logged(
            validation_command,
            policy_dir / "positive-control-validation.stdout.log",
            policy_dir / "positive-control-validation.stderr.log",
        )

    analysis_command = [
        sys.executable,
        str(analyzer_script),
        "--registration",
        str(registration_path),
        "--reports-dir",
        str(out_dir),
        "--out",
        str(out_dir / "analysis.json"),
    ]
    run_logged(
        analysis_command,
        out_dir / "analysis.stdout.log",
        out_dir / "analysis.stderr.log",
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1) from error
