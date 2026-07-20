#!/usr/bin/env python3
"""Validate and recompute the retained ADR-0294 semantic census result."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
PRODUCER_SCRIPT = Path(__file__).with_name("census-glaurung-llvm-loop-semantics.py")
PRODUCER_SPEC = importlib.util.spec_from_file_location(
    "glaurung_loop_semantic_producer", PRODUCER_SCRIPT
)
if PRODUCER_SPEC is None or PRODUCER_SPEC.loader is None:
    raise RuntimeError(f"cannot load semantic census producer from {PRODUCER_SCRIPT}")
PRODUCER = importlib.util.module_from_spec(PRODUCER_SPEC)
sys.modules[PRODUCER_SPEC.name] = PRODUCER
PRODUCER_SPEC.loader.exec_module(PRODUCER)
BASE = PRODUCER.BASE

DEFAULT_MANIFEST = PRODUCER.DEFAULT_MANIFEST
DEFAULT_RESULT = PRODUCER.EXPECTED_FORMAL_OUTPUT


class ResultValidationError(RuntimeError):
    """The retained semantic census result is malformed or inconsistent."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ResultValidationError(message)


def require_object(value: Any, where: str) -> dict[str, Any]:
    require(isinstance(value, dict), f"{where}: expected object")
    return value


def require_list(value: Any, where: str) -> list[Any]:
    require(isinstance(value, list), f"{where}: expected array")
    return value


def require_exact_keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    require(
        actual == expected,
        f"{where}: fields differ: missing={sorted(expected - actual)} "
        f"unexpected={sorted(actual - expected)}",
    )


def load_json(path: Path, where: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ResultValidationError(f"cannot decode {where} {path}: {error}") from error
    return require_object(value, where)


def validate_result(
    result_path: Path, manifest_path: Path = DEFAULT_MANIFEST
) -> dict[str, Any]:
    manifest = PRODUCER.load_manifest(manifest_path)
    for file in manifest["producer_files"]:
        path = REPO / file["path"]
        require(path.is_file(), f"registered producer file is missing: {file['path']}")
        require(BASE.sha256_file(path) == file["sha256"], f"producer drift: {file['path']}")

    structural_manifest_path = REPO / manifest["structural_manifest"]["path"]
    structural_result_path = REPO / manifest["structural_result"]["path"]
    require(
        BASE.sha256_file(structural_manifest_path) == manifest["structural_manifest"]["sha256"],
        "structural manifest SHA-256 drift",
    )
    require(
        BASE.sha256_file(structural_result_path) == manifest["structural_result"]["sha256"],
        "structural result SHA-256 drift",
    )
    structural_manifest = BASE.load_manifest(structural_manifest_path)
    structural_result = BASE.load_result(
        structural_result_path, structural_manifest_path, structural_manifest
    )
    structural_sources = structural_result["sources"]

    result = load_json(result_path, "result")
    require_exact_keys(
        result,
        {
            "classifier_binary_sha256",
            "glaurung_revision",
            "manifest_sha256",
            "schema",
            "selection",
            "sources",
            "summary",
            "toolchain",
        },
        "result",
    )
    require(result["schema"] == PRODUCER.RESULT_SCHEMA, "result schema drift")
    require(
        result["glaurung_revision"] == structural_manifest["glaurung"]["revision"],
        "result Glaurung revision drift",
    )
    require(result["manifest_sha256"] == BASE.sha256_file(manifest_path), "manifest hash drift")
    require(
        isinstance(result["classifier_binary_sha256"], str)
        and bool(BASE.SHA256_RE.fullmatch(result["classifier_binary_sha256"])),
        "invalid classifier binary SHA-256",
    )

    tools = require_object(result["toolchain"], "result.toolchain")
    require_exact_keys(tools, {"cargo", "llvm_extract", "rustc"}, "result.toolchain")
    for name in ("cargo", "llvm_extract", "rustc"):
        tool = require_object(tools[name], f"result.toolchain.{name}")
        require_exact_keys(
            tool,
            {"realpath", "sha256", "version_first_line"},
            f"result.toolchain.{name}",
        )
        registered = manifest["toolchain"][name]
        for field in ("realpath", "sha256", "version_first_line"):
            require(tool[field] == registered[field], f"result tool drift: {name}.{field}")

    sources = require_list(result["sources"], "result.sources")
    require(len(sources) == len(structural_sources), "result source count drift")
    all_rows: list[dict[str, Any]] = []
    for source_index, (raw_source, structural_source) in enumerate(
        zip(sources, structural_sources)
    ):
        source = require_object(raw_source, f"result.source[{source_index}]")
        require_exact_keys(
            source,
            {"compile_stderr", "llvm_sha256", "loops", "path", "source_sha256"},
            f"result.source[{source_index}]",
        )
        for field in ("path", "source_sha256", "llvm_sha256", "compile_stderr"):
            require(
                source[field] == structural_source[field],
                f"result source[{source_index}] {field} drift",
            )
        rows = require_list(source["loops"], f"result.source[{source_index}].loops")
        structural_rows = structural_source["loops"]
        require(len(rows) == len(structural_rows), f"result source[{source_index}] loop loss")
        for row_index, (raw_row, structural_row) in enumerate(zip(rows, structural_rows)):
            row = require_object(raw_row, f"result.source[{source_index}].loop[{row_index}]")
            require_exact_keys(
                row,
                {
                    "diagnostic",
                    "function",
                    "iteration_paths",
                    "kind",
                    "moduleid_agnostic_extracted_llvm_sha256",
                    "source_path",
                    "stage",
                    "state_components",
                    "structural_profile",
                },
                f"result.source[{source_index}].loop[{row_index}]",
            )
            require(row["source_path"] == source["path"], "semantic source path drift")
            require(row["function"] == structural_row["function"], "semantic function drift")
            require(
                row["structural_profile"] == structural_row["profile"],
                "structural profile drift",
            )
            require(row["stage"] in PRODUCER.STAGES, "semantic stage drift")
            require(isinstance(row["kind"], str) and bool(row["kind"]), "empty semantic kind")
            require(
                isinstance(row["diagnostic"], str),
                "semantic diagnostic is not a string",
            )
            require(
                isinstance(row["moduleid_agnostic_extracted_llvm_sha256"], str)
                and bool(
                    BASE.SHA256_RE.fullmatch(
                        row["moduleid_agnostic_extracted_llvm_sha256"]
                    )
                ),
                "invalid extracted LLVM SHA-256",
            )
            for field in ("state_components", "iteration_paths"):
                require(
                    isinstance(row[field], int)
                    and not isinstance(row[field], bool)
                    and row[field] >= 0,
                    f"invalid semantic {field}",
                )
            if row["stage"] == "accepted":
                require(row["kind"] in {"self_loop", "single_latch"}, "accepted kind drift")
                require(
                    row["state_components"] > 0 and row["iteration_paths"] > 0,
                    "accepted metadata is empty",
                )
                require(not row["diagnostic"], "accepted row has a diagnostic")
            else:
                require(
                    row["state_components"] == 0 and row["iteration_paths"] == 0,
                    "rejected metadata is nonzero",
                )
                require(bool(row["diagnostic"]), "rejected row lacks a diagnostic")
            all_rows.append(row)

    stage_counts = Counter(row["stage"] for row in all_rows)
    outcome_counts = Counter(f"{row['stage']}:{row['kind']}" for row in all_rows)
    expected_summary = {
        "accepted": stage_counts["accepted"],
        "outcome_counts": dict(sorted(outcome_counts.items())),
        "rejected": len(all_rows) - stage_counts["accepted"],
        "rows": len(all_rows),
        "sources": len(sources),
        "stage_counts": {stage: stage_counts[stage] for stage in PRODUCER.STAGES},
    }
    require(result["summary"] == expected_summary, "semantic summary drift")
    expected_selection = PRODUCER.select_rejection(all_rows, manifest["selection"])
    require(result["selection"] == expected_selection, "semantic selection drift")
    require(len(all_rows) == structural_result["summary"]["loops"], "semantic row loss")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--result", type=Path, default=DEFAULT_RESULT)
    args = parser.parse_args(argv)
    try:
        result = validate_result(args.result, args.manifest)
        print(
            json.dumps(
                {
                    "result_sha256": BASE.sha256_file(args.result),
                    "schema": PRODUCER.RESULT_SCHEMA,
                    "selection": result["selection"],
                    "status": "valid-result",
                    **result["summary"],
                },
                sort_keys=True,
            )
        )
        return 0
    except (
        ResultValidationError,
        PRODUCER.SemanticCensusError,
        BASE.CensusError,
        OSError,
        UnicodeError,
    ) as error:
        print(f"semantic loop census result: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
