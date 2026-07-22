#!/usr/bin/env python3
"""Validate the preregistered official Lean construct matrix fail closed."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-official-construct-matrix-v1.json"

SCHEMA = "axeyum-lean-official-construct-matrix-v1"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "decision",
    "pins",
    "resource_policy",
    "retention_policy",
    "commands",
    "historical_controls",
    "sources",
    "cases",
    "stage_b",
    "product_measurement",
}
CASE_KEYS = {
    "id",
    "source_family",
    "role",
    "source_key",
    "module",
    "selected_root",
    "computation_witness",
    "expected_official_source",
    "stage_b_wire",
    "product_measurement",
}
HISTORICAL_CONTROL_KEYS = {
    "id",
    "source_path",
    "source_sha256",
    "stream_path",
    "stream_sha256",
    "regenerated_runs",
    "imported_runs",
    "expected_report",
}
REPORT_KEYS = {
    "names",
    "levels",
    "expressions",
    "declaration_records",
    "admitted_declarations",
    "axioms",
}
EXPECTED_PINS = {
    "lean": {
        "toolchain": "leanprover/lean4:v4.30.0",
        "version": "4.30.0",
        "git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
    },
    "lean4export": {
        "version": "v4.30.0",
        "git_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "format": "3.1.0",
    },
}
EXPECTED_RESOURCES = {
    "runner": "systemd-run --user --scope",
    "memory_high": "3G",
    "memory_max": "4G",
    "memory_swap_max": "512M",
    "lean_jobs": 1,
    "rust_jobs": 2,
}
EXPECTED_RETENTION = {
    "per_stream_max_bytes": 1_048_576,
    "aggregate_new_stream_max_bytes": 2_097_152,
}
EXPECTED_CONTROL_REPORTS = {
    "flat": {
        "names": 14,
        "levels": 2,
        "expressions": 43,
        "declaration_records": 5,
        "admitted_declarations": 8,
        "axioms": 1,
    },
    "direct-recursive-control": {
        "names": 30,
        "levels": 4,
        "expressions": 130,
        "declaration_records": 5,
        "admitted_declarations": 11,
        "axioms": 0,
    },
}
EXPECTED_CASES = [
    (
        "direct-recursive-control",
        "direct-recursive-non-indexed",
        "positive-control",
        "historical-direct-recursive-control",
        "AxeyumImportShapes",
        "AxeyumImportShapes",
        "miniOne",
        "accepted",
    ),
    (
        "recursive-indexed",
        "recursive-indexed",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.recursiveIndexedWitness",
        "AxeyumConstructMatrix.recursiveIndexedWitness",
        "accepted",
    ),
    (
        "reflexive-higher-order",
        "reflexive-higher-order",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.reflexiveWitness",
        "AxeyumConstructMatrix.reflexiveWitness",
        "accepted",
    ),
    (
        "mutual",
        "mutual",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.mutualWitness",
        "AxeyumConstructMatrix.mutualWitness",
        "accepted",
    ),
    (
        "nested",
        "nested",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.nestedWitness",
        "AxeyumConstructMatrix.nestedWitness",
        "accepted",
    ),
    (
        "well-founded",
        "well-founded",
        "measurement",
        "positive",
        "AxeyumConstructMatrix",
        "AxeyumConstructMatrix.wellFoundedWitness",
        "AxeyumConstructMatrix.wellFoundedWitness",
        "accepted",
    ),
    (
        "non-positive-source-negative",
        "non-positive-inductive",
        "official-source-negative",
        "negative",
        "AxeyumConstructMatrixNegative",
        None,
        None,
        "rejected",
    ),
]


def load_manifest(path: Path = MANIFEST) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("manifest root must be an object")
    return data


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def check_exact_keys(value: Any, expected: set[str], context: str, failures: list[str]) -> None:
    if not isinstance(value, dict):
        failures.append(f"{context} must be an object")
        return
    actual = set(value)
    if actual != expected:
        failures.append(
            f"{context} fields drift: missing={sorted(expected - actual)} "
            f"extra={sorted(actual - expected)}"
        )


def checked_repo_path(raw: Any, context: str, failures: list[str]) -> Path | None:
    if not isinstance(raw, str) or not raw:
        failures.append(f"{context} must be a non-empty repository-relative path")
        return None
    path = (ROOT / raw).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError:
        failures.append(f"{context} escapes the repository: {raw}")
        return None
    if not path.is_file():
        failures.append(f"{context} is missing: {raw}")
        return None
    return path


def validate_file_hash(entry: Any, path_key: str, hash_key: str, context: str) -> list[str]:
    failures: list[str] = []
    if not isinstance(entry, dict):
        return [f"{context} must be an object"]
    path = checked_repo_path(entry.get(path_key), f"{context}.{path_key}", failures)
    expected_hash = entry.get(hash_key)
    if not isinstance(expected_hash, str) or len(expected_hash) != 64:
        failures.append(f"{context}.{hash_key} must be a 64-character SHA-256")
    elif path is not None:
        actual_hash = sha256(path)
        if actual_hash != expected_hash:
            failures.append(
                f"{context} hash drift for {entry[path_key]}: "
                f"expected {expected_hash}, got {actual_hash}"
            )
    return failures


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    check_exact_keys(data, TOP_LEVEL_KEYS, "manifest", failures)

    if data.get("schema") != SCHEMA:
        failures.append(f"schema must be {SCHEMA!r}")
    if data.get("stage") != "source-frozen":
        failures.append("Stage A manifest must have stage=source-frozen")
    if data.get("date") != "2026-07-22":
        failures.append("Stage A date drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0351-preregister-official-lean-construct-matrix.md"
    ):
        failures.append("decision path drift")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("Lean/exporter pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")
    if data.get("retention_policy") != EXPECTED_RETENTION:
        failures.append("retention policy drift")
    if data.get("stage_b") is not None:
        failures.append("Stage A must not contain Stage B wire observations")
    if data.get("product_measurement") is not None:
        failures.append("Stage A must not contain product measurements")

    toolchain_path = ROOT / "lean-toolchain"
    if toolchain_path.read_text(encoding="utf-8").strip() != EXPECTED_PINS["lean"]["toolchain"]:
        failures.append("lean-toolchain does not match the registered pin")

    commands = data.get("commands")
    command_keys = {
        "working_directory",
        "resource_runner_argv",
        "lean_executable",
        "compile_positive_argv",
        "compile_negative_argv",
    }
    check_exact_keys(commands, command_keys, "commands", failures)
    if isinstance(commands, dict):
        expected_runner = [
            "systemd-run",
            "--user",
            "--scope",
            "--quiet",
            "-p",
            "MemoryHigh=3G",
            "-p",
            "MemoryMax=4G",
            "-p",
            "MemorySwapMax=512M",
        ]
        if commands.get("resource_runner_argv") != expected_runner:
            failures.append("resource runner argv drift")
        lean = commands.get("lean_executable")
        for key, output, source in (
            ("compile_positive_argv", "AxeyumConstructMatrix.olean", "AxeyumConstructMatrix.lean"),
            (
                "compile_negative_argv",
                "AxeyumConstructMatrixNegative.olean",
                "AxeyumConstructMatrixNegative.lean",
            ),
        ):
            expected = ["/usr/bin/time", "-v", lean, "-j1", "-o", output, source]
            if commands.get(key) != expected:
                failures.append(f"{key} drift")

    controls = data.get("historical_controls")
    if not isinstance(controls, list):
        failures.append("historical_controls must be an array")
    else:
        ids = [entry.get("id") for entry in controls if isinstance(entry, dict)]
        if ids != ["flat", "direct-recursive-control"]:
            failures.append("historical control order/population drift")
        for index, entry in enumerate(controls):
            check_exact_keys(
                entry,
                HISTORICAL_CONTROL_KEYS,
                f"historical_controls[{index}]",
                failures,
            )
            failures.extend(
                validate_file_hash(entry, "source_path", "source_sha256", f"historical_controls[{index}]")
            )
            failures.extend(
                validate_file_hash(entry, "stream_path", "stream_sha256", f"historical_controls[{index}]")
            )
            if isinstance(entry, dict):
                if entry.get("regenerated_runs") != 2 or entry.get("imported_runs") != 2:
                    failures.append(f"historical_controls[{index}] must record two reproductions and imports")
                report = entry.get("expected_report")
                check_exact_keys(
                    report,
                    REPORT_KEYS,
                    f"historical_controls[{index}].expected_report",
                    failures,
                )
                if report != EXPECTED_CONTROL_REPORTS.get(entry.get("id")):
                    failures.append(f"historical_controls[{index}] importer report drift")

    sources = data.get("sources")
    check_exact_keys(sources, {"positive", "negative"}, "sources", failures)
    if isinstance(sources, dict):
        positive = sources.get("positive")
        negative = sources.get("negative")
        check_exact_keys(
            positive,
            {"path", "sha256", "module", "official_source_outcome", "exit_status", "max_rss_kib"},
            "sources.positive",
            failures,
        )
        check_exact_keys(
            negative,
            {
                "path",
                "sha256",
                "module",
                "official_source_outcome",
                "exit_status",
                "diagnostic_substring",
                "max_rss_kib",
            },
            "sources.negative",
            failures,
        )
        failures.extend(validate_file_hash(positive, "path", "sha256", "sources.positive"))
        failures.extend(validate_file_hash(negative, "path", "sha256", "sources.negative"))
        if isinstance(positive, dict) and (
            positive.get("module") != "AxeyumConstructMatrix"
            or positive.get("official_source_outcome") != "accepted"
            or positive.get("exit_status") != 0
        ):
            failures.append("positive source compile outcome drift")
        if isinstance(positive, dict) and not (
            isinstance(positive.get("max_rss_kib"), int)
            and 0 < positive["max_rss_kib"] <= 4 * 1024 * 1024
        ):
            failures.append("positive source RSS must fit the 4 GiB cgroup")
        if isinstance(negative, dict) and (
            negative.get("module") != "AxeyumConstructMatrixNegative"
            or negative.get("official_source_outcome") != "rejected"
            or negative.get("exit_status") != 1
            or negative.get("diagnostic_substring")
            != "has a non positive occurrence of the datatypes being declared"
        ):
            failures.append("negative source rejection outcome drift")
        if isinstance(negative, dict) and not (
            isinstance(negative.get("max_rss_kib"), int)
            and 0 < negative["max_rss_kib"] <= 4 * 1024 * 1024
        ):
            failures.append("negative source RSS must fit the 4 GiB cgroup")

    cases = data.get("cases")
    if not isinstance(cases, list):
        failures.append("cases must be an array")
    else:
        if len(cases) != len(EXPECTED_CASES):
            failures.append(
                f"case population drift: expected {len(EXPECTED_CASES)}, got {len(cases)}"
            )
        ids = [case.get("id") for case in cases if isinstance(case, dict)]
        if len(ids) != len(set(ids)):
            failures.append("case IDs must be unique")
        for index, case in enumerate(cases):
            check_exact_keys(case, CASE_KEYS, f"cases[{index}]", failures)
            if not isinstance(case, dict):
                continue
            if case.get("stage_b_wire") is not None:
                failures.append(f"cases[{index}] contains premature Stage B wire data")
            if case.get("product_measurement") is not None:
                failures.append(f"cases[{index}] contains premature product data")
            if index < len(EXPECTED_CASES):
                actual = (
                    case.get("id"),
                    case.get("source_family"),
                    case.get("role"),
                    case.get("source_key"),
                    case.get("module"),
                    case.get("selected_root"),
                    case.get("computation_witness"),
                    case.get("expected_official_source"),
                )
                if actual != EXPECTED_CASES[index]:
                    failures.append(f"cases[{index}] source-freeze contract drift")

    return failures


def main() -> int:
    try:
        data = load_manifest()
    except (OSError, json.JSONDecodeError, ValueError) as error:
        print(f"lean construct matrix: unable to load manifest: {error}", file=sys.stderr)
        return 1
    failures = validate_manifest(data)
    if failures:
        for failure in failures:
            print(f"lean construct matrix: {failure}", file=sys.stderr)
        return 1
    print(
        "lean construct matrix Stage A valid: "
        f"{len(data['cases'])} cases, 2 source outcomes, "
        f"{len(data['historical_controls'])} reproduced controls, "
        "Stage B/product observations absent"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
