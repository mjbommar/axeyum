#!/usr/bin/env python3
"""Run the ADR-0356 pinned official producer twice in fresh environments."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.smtcomp_repro.official_producer import (
    EXPECTED_RUNTIME_PACKAGES,
    OfficialProducerError,
    authority_bundle_entries,
    hash_file,
    locked_runtime_requirements,
    materialize_bundle,
    validate_repetition,
    validate_selected_output,
)
from scripts.smtcomp_repro.official_selection import canonical_json_bytes


SCHEMA = "axeyum-smtcomp-official-producer-v1"
EXPECTED_PYTHON_SHA256 = "9ba4d70d34523a0bc8a95885f35f8974df4eb15ccb2251063bfb7656588db52f"
EXPECTED_UV_SHA256 = "d86fc2769298a09dcd6d3a93b7765e3d12671426199e3812e374b99c7be4f53c"
EXPECTED_UV_VERSION = "uv 0.11.1 (x86_64-unknown-linux-gnu)"
IMPLEMENTATION_PATHS = (
    "docs/plan/smtcomp-official-selection-authority-v1.json",
    "scripts/produce-smtcomp-official-selection.py",
    "scripts/smtcomp_repro/official_producer.py",
    "scripts/smtcomp_repro/official_producer_worker.py",
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_document(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or raw != canonical_json_bytes(value):
        raise OfficialProducerError(f"noncanonical JSON document: {path}")
    return value


def verify_completion(
    root: Path,
    name: str,
    schema: str,
    authority_sha256: str,
) -> tuple[dict[str, Any], str]:
    path = root / name
    document = canonical_document(path)
    if (
        document.get("schema") != schema
        or document.get("status") != "complete"
        or document.get("selection_observed") is not False
        or document.get("authority_sha256") != authority_sha256
    ):
        raise OfficialProducerError(f"prior-stage completion differs: {path}")
    payload = {key: value for key, value in document.items() if key != "payload_sha256"}
    if sha256_bytes(canonical_json_bytes(payload)) != document.get("payload_sha256"):
        raise OfficialProducerError(f"prior-stage completion payload differs: {path}")
    artifacts = document.get("artifacts")
    if not isinstance(artifacts, dict):
        raise OfficialProducerError(f"prior-stage artifact map is missing: {path}")
    for relative, expected in artifacts.items():
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise OfficialProducerError(f"invalid prior-stage artifact entry: {path}")
        _, observed = hash_file(root / relative)
        if observed != expected:
            raise OfficialProducerError(f"prior-stage artifact differs: {root / relative}")
    _, completion_sha256 = hash_file(path)
    return document, completion_sha256


def publish(path: Path, data: bytes) -> None:
    if path.exists():
        raise OfficialProducerError(f"artifact already exists: {path}")
    temporary = path.with_name(path.name + ".part")
    with temporary.open("xb") as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)


def run_logged(command: list[str], cwd: Path, log_root: Path, name: str, env: dict[str, str]) -> None:
    stdout_path = log_root / f"{name}.stdout"
    stderr_path = log_root / f"{name}.stderr"
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, check=False)
    if result.returncode != 0:
        raise OfficialProducerError(f"command failed ({result.returncode}): {' '.join(command)}")


def command_output(command: list[str]) -> str:
    return subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout.decode().strip()


def executable_identity(path: Path) -> dict[str, object]:
    size, sha256 = hash_file(path)
    return {"bytes": size, "path": str(path), "sha256": sha256}


def implementation_commit() -> str:
    for relative in IMPLEMENTATION_PATHS:
        tracked = subprocess.run(
            ["git", "ls-files", "--error-unmatch", relative],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        if tracked.returncode != 0:
            raise OfficialProducerError(f"producer implementation is not committed: {relative}")
    clean = subprocess.run(
        ["git", "diff", "--quiet", "HEAD", "--", *IMPLEMENTATION_PATHS],
        cwd=ROOT,
        check=False,
    )
    if clean.returncode != 0:
        raise OfficialProducerError("producer implementation differs from HEAD")
    return command_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"])


def run_once(
    label: str,
    attempt: Path,
    source_inputs: Path,
    bundle_entries: list[dict[str, object]],
    requirements_path: Path,
    uv: Path,
    python: Path,
    worker: Path,
    expected_freeze: list[str],
) -> dict[str, object]:
    run_root = attempt / label
    run_root.mkdir()
    bundle = run_root / "bundle"
    verified = materialize_bundle(source_inputs, bundle, bundle_entries)
    bundle_manifest = {"files": verified, "schema": f"{SCHEMA}-bundle-v1"}
    publish(run_root / "bundle.json", canonical_json_bytes(bundle_manifest))

    venv = run_root / ".venv"
    output = run_root / "output"
    environment = dict(os.environ)
    environment.update(
        {
            "LC_ALL": "C.UTF-8",
            "POLARS_MAX_THREADS": "1",
            "PYTHONHASHSEED": "0",
            "PYTHONNOUSERSITE": "1",
            "TZ": "UTC",
            "UV_CACHE_DIR": str(run_root / "uv-cache"),
        }
    )
    environment.pop("PYTHONPATH", None)
    environment.pop("VIRTUAL_ENV", None)
    commands = {
        "venv": [str(uv), "venv", "--python", str(python), str(venv)],
        "install": [
            str(uv),
            "pip",
            "install",
            "--python",
            str(venv / "bin/python"),
            "--no-deps",
            "--require-hashes",
            "-r",
            str(requirements_path),
        ],
        "freeze": [str(uv), "pip", "freeze", "--python", str(venv / "bin/python")],
        "producer": [
            str(venv / "bin/python"),
            str(worker),
            "--bundle",
            str(bundle),
            "--output",
            str(output),
        ],
    }
    run_logged(
        commands["venv"],
        ROOT,
        run_root,
        "venv",
        environment,
    )
    run_logged(
        commands["install"],
        ROOT,
        run_root,
        "install",
        environment,
    )
    run_logged(
        commands["freeze"],
        ROOT,
        run_root,
        "freeze",
        environment,
    )
    try:
        freeze = (run_root / "freeze.stdout").read_text().splitlines()
    except UnicodeDecodeError as error:
        raise OfficialProducerError(f"installed-package list is not UTF-8: {label}") from error
    if sorted(freeze) != expected_freeze:
        raise OfficialProducerError(f"installed packages differ from locked closure: {label}")
    run_logged(
        commands["producer"],
        ROOT,
        run_root,
        "producer",
        environment,
    )
    paths = validate_selected_output((output / "official-selected.txt").read_bytes(), expected_count=45_905)
    per_logic = canonical_document(output / "per-logic.json")
    worker_document = canonical_document(output / "worker.json")
    if per_logic.get("selected") != len(paths) or worker_document.get("selected") != len(paths):
        raise OfficialProducerError(f"selected count differs inside {label}")
    artifact_names = ("official-selected.txt", "per-logic.json", "worker.json")
    artifacts = {}
    for name in artifact_names:
        size, sha256 = hash_file(output / name)
        artifacts[name] = {"bytes": size, "sha256": sha256}
    logs = {}
    for command_name in commands:
        for stream in ("stdout", "stderr"):
            name = f"{command_name}.{stream}"
            size, sha256 = hash_file(run_root / name)
            logs[name] = {"bytes": size, "sha256": sha256}
    return {
        "artifacts": artifacts,
        "bundle_manifest_sha256": hash_file(run_root / "bundle.json")[1],
        "commands": commands,
        "environment": {
            key: environment[key]
            for key in ("LC_ALL", "POLARS_MAX_THREADS", "PYTHONHASHSEED", "PYTHONNOUSERSITE", "TZ")
        },
        "label": label,
        "logs": logs,
        "selected": len(paths),
        "worker": worker_document,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--authority",
        type=Path,
        default=ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json",
    )
    parser.add_argument("--input-audit", type=Path, required=True)
    parser.add_argument("--corpus-acquisition", type=Path, required=True)
    parser.add_argument("--output-parent", type=Path, required=True)
    parser.add_argument("--python", type=Path, default=Path(shutil.which("python3.11") or "python3.11"))
    parser.add_argument("--uv", type=Path, default=Path(shutil.which("uv") or "uv"))
    args = parser.parse_args()

    authority_raw = args.authority.read_bytes()
    authority = json.loads(authority_raw)
    if not isinstance(authority, dict) or authority_raw != canonical_json_bytes(authority):
        raise OfficialProducerError("authority is not canonical JSON")
    authority_sha256 = sha256_bytes(authority_raw)
    if authority_sha256 != "0fd1f479e809e0d8f740aa72cff193871b35f45c95a2eb9d96440ca7508b3d1a":
        raise OfficialProducerError("authority SHA-256 differs")
    _, input_completion_sha256 = verify_completion(
        args.input_audit,
        "input-audit.json",
        "axeyum-smtcomp-selection-input-audit-v1",
        authority_sha256,
    )
    _, corpus_completion_sha256 = verify_completion(
        args.corpus_acquisition,
        "corpus-audit.json",
        "axeyum-smtcomp-selection-corpus-acquisition-v1",
        authority_sha256,
    )
    corpus_summary = canonical_document(args.corpus_acquisition / "summary.json")
    if corpus_summary.get("input_audit_completion_sha256") != input_completion_sha256:
        raise OfficialProducerError("S2 does not bind the supplied S1 completion")

    commit = implementation_commit()
    python = args.python.resolve(strict=True)
    uv = args.uv.resolve(strict=True)
    if command_output([str(python), "--version"]) != "Python 3.11.15":
        raise OfficialProducerError("producer Python version differs")
    uv_version = command_output([str(uv), "--version"])
    if hash_file(python)[1] != EXPECTED_PYTHON_SHA256:
        raise OfficialProducerError("producer Python executable differs")
    if uv_version != EXPECTED_UV_VERSION or hash_file(uv)[1] != EXPECTED_UV_SHA256:
        raise OfficialProducerError("producer uv executable differs")
    bundle_entries = authority_bundle_entries(authority)
    if len(bundle_entries) != 88:
        raise OfficialProducerError(f"producer bundle file count differs: {len(bundle_entries)}")
    source_inputs = args.input_audit / "inputs"
    lock_path = source_inputs / "poetry.lock"
    requirements, packages = locked_runtime_requirements(lock_path.read_bytes())
    if len(packages) != EXPECTED_RUNTIME_PACKAGES:
        raise OfficialProducerError(f"locked runtime package count differs: {len(packages)}")
    polars = next((row for row in packages if row["name"] == "polars"), None)
    if polars is None or polars["version"] != "1.39.2":
        raise OfficialProducerError("locked Polars identity differs")
    expected_freeze = sorted(f"{row['name']}=={row['version']}" for row in packages)

    args.output_parent.mkdir(parents=True, exist_ok=True)
    attempt = args.output_parent / f"official-producer-{time.time_ns()}-{commit[:8]}"
    attempt.mkdir()
    requirements_path = attempt / "requirements.lock"
    publish(requirements_path, requirements)
    worker = ROOT / "scripts/smtcomp_repro/official_producer_worker.py"
    runs = [
        run_once(
            label,
            attempt,
            source_inputs,
            bundle_entries,
            requirements_path,
            uv,
            python,
            worker,
            expected_freeze,
        )
        for label in ("run-a", "run-b")
    ]
    repetition = validate_repetition(attempt / "run-a/output", attempt / "run-b/output")
    first_output = attempt / "run-a/output"
    selected_bytes = (first_output / "official-selected.txt").read_bytes()
    per_logic_bytes = (first_output / "per-logic.json").read_bytes()
    publish(attempt / "official-selected.txt", selected_bytes)
    publish(attempt / "per-logic.json", per_logic_bytes)
    producer = {
        "authority_sha256": authority_sha256,
        "bundle_files": len(bundle_entries),
        "corpus_completion_sha256": corpus_completion_sha256,
        "implementation_commit": commit,
        "input_audit_completion_sha256": input_completion_sha256,
        "packages": packages,
        "python": {
            **executable_identity(python),
            "version": "3.11.15",
        },
        "repetition": {**repetition, "equal": True},
        "requirements_sha256": sha256_bytes(requirements),
        "runs": runs,
        "schema": SCHEMA,
        "selected": 45_905,
        "selection_observed": True,
        "uv": {**executable_identity(uv), "version": uv_version},
    }
    publish(attempt / "producer.json", canonical_json_bytes(producer))
    artifacts = {}
    for name in ("official-selected.txt", "per-logic.json", "producer.json", "requirements.lock"):
        artifacts[name] = hash_file(attempt / name)[1]
    completion_payload = {
        "artifacts": artifacts,
        "authority_sha256": authority_sha256,
        "schema": SCHEMA,
        "selected": 45_905,
        "selection_observed": True,
        "status": "complete",
    }
    completion = {
        **completion_payload,
        "payload_sha256": sha256_bytes(canonical_json_bytes(completion_payload)),
    }
    publish(attempt / "producer-audit.json", canonical_json_bytes(completion))
    print(
        "SMTCOMP_OFFICIAL_PRODUCER_OK|"
        f"selected=45905|selected_sha256={repetition['official_selected_sha256']}|"
        "repetitions_equal=true|polars=1.39.2|selection_observed=true"
    )
    print(attempt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
