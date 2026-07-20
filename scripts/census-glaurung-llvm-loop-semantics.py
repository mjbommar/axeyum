#!/usr/bin/env python3
"""Produce the preregistered ADR-0294 Glaurung loop semantic census."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
BASE_SCRIPT = Path(__file__).with_name("census-glaurung-llvm-loops.py")
BASE_SPEC = importlib.util.spec_from_file_location("glaurung_loop_census_base", BASE_SCRIPT)
if BASE_SPEC is None or BASE_SPEC.loader is None:
    raise RuntimeError(f"cannot load structural census support from {BASE_SCRIPT}")
BASE = importlib.util.module_from_spec(BASE_SPEC)
sys.modules[BASE_SPEC.name] = BASE
BASE_SPEC.loader.exec_module(BASE)

SCHEMA = "axeyum.glaurung-llvm-loop-semantic-census.v1"
RESULT_SCHEMA = "axeyum.glaurung-llvm-loop-semantic-census-result.v1"
DEFAULT_MANIFEST = Path(
    "docs/consumer-track/verify/glaurung-llvm-loop-semantic-census-v1.json"
)
EXPECTED_STRUCTURAL_MANIFEST = Path(
    "docs/consumer-track/verify/glaurung-llvm-loop-census-v1.json"
)
EXPECTED_STRUCTURAL_RESULT = Path(
    "docs/consumer-track/verify/glaurung-llvm-loop-census-v1-result.json"
)
EXPECTED_FORMAL_OUTPUT = Path(
    "docs/consumer-track/verify/glaurung-llvm-loop-semantic-census-v1-result.json"
)
EXPECTED_CARGO_ARGS = [
    "build",
    "--locked",
    "--offline",
    "--quiet",
    "-p",
    "axeyum-verify",
    "--bin",
    "axeyum-llvm-loop-classify",
]
EXPECTED_SELECTION = {
    "minimum_functions": 2,
    "minimum_sources": 2,
    "require_strict_plurality": True,
}
CLASSIFIER_KEYS = {
    "function",
    "iteration_paths",
    "kind",
    "stage",
    "state_components",
}
STAGES = ["accepted", "function_syntax", "scalar_cfg", "loop_reflection"]


class SemanticCensusError(RuntimeError):
    """The semantic census cannot be validated or reproduced."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SemanticCensusError(message)


def require_object(value: Any, where: str) -> dict[str, Any]:
    require(isinstance(value, dict), f"{where}: expected object")
    return value


def require_list(value: Any, where: str) -> list[Any]:
    require(isinstance(value, list), f"{where}: expected array")
    return value


def require_string(value: Any, where: str) -> str:
    require(isinstance(value, str) and bool(value), f"{where}: expected nonempty string")
    return value


def require_exact_keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    require(
        actual == expected,
        f"{where}: fields differ: missing={sorted(expected - actual)} "
        f"unexpected={sorted(actual - expected)}",
    )


def safe_repo_path(raw: str, where: str) -> Path:
    path = Path(require_string(raw, where))
    require(not path.is_absolute() and ".." not in path.parts, f"{where}: unsafe path")
    return path


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise SemanticCensusError(f"cannot decode manifest {path}: {error}") from error
    manifest = require_object(value, "manifest")
    require_exact_keys(
        manifest,
        {
            "cargo_args",
            "formal_output",
            "producer_files",
            "result_state",
            "schema",
            "selection",
            "structural_manifest",
            "structural_result",
            "toolchain",
        },
        "manifest",
    )
    require(manifest["schema"] == SCHEMA, f"manifest.schema: expected {SCHEMA}")
    require(manifest["result_state"] == "zero-row", "manifest must remain zero-row")
    require(manifest["cargo_args"] == EXPECTED_CARGO_ARGS, "cargo argument drift")
    require(manifest["selection"] == EXPECTED_SELECTION, "selection rule drift")
    require(
        safe_repo_path(manifest["formal_output"], "manifest.formal_output")
        == EXPECTED_FORMAL_OUTPUT,
        "formal output path drift",
    )

    for field, expected_path in (
        ("structural_manifest", EXPECTED_STRUCTURAL_MANIFEST),
        ("structural_result", EXPECTED_STRUCTURAL_RESULT),
    ):
        reference = require_object(manifest[field], f"manifest.{field}")
        require_exact_keys(reference, {"path", "sha256"}, f"manifest.{field}")
        require(safe_repo_path(reference["path"], f"manifest.{field}.path") == expected_path,
                f"manifest.{field} path drift")
        require(
            bool(BASE.SHA256_RE.fullmatch(require_string(reference["sha256"], field))),
            f"manifest.{field} invalid SHA-256",
        )

    tools = require_object(manifest["toolchain"], "manifest.toolchain")
    require_exact_keys(tools, {"cargo", "llvm_extract", "rustc"}, "manifest.toolchain")
    for name in ("cargo", "llvm_extract", "rustc"):
        tool = require_object(tools[name], f"manifest.toolchain.{name}")
        require_exact_keys(
            tool,
            {"command", "realpath", "sha256", "version_first_line"},
            f"manifest.toolchain.{name}",
        )
        command = Path(require_string(tool["command"], f"toolchain.{name}.command"))
        realpath = Path(require_string(tool["realpath"], f"toolchain.{name}.realpath"))
        require(command.is_absolute(), f"toolchain.{name}.command must be absolute")
        require(realpath.is_absolute(), f"toolchain.{name}.realpath must be absolute")
        require(
            bool(BASE.SHA256_RE.fullmatch(require_string(tool["sha256"], name))),
            f"toolchain.{name} invalid SHA-256",
        )
        require_string(tool["version_first_line"], f"toolchain.{name}.version_first_line")

    files = require_list(manifest["producer_files"], "manifest.producer_files")
    require(bool(files), "producer file list must not be empty")
    paths: list[str] = []
    for index, raw_file in enumerate(files):
        file = require_object(raw_file, f"producer_file[{index}]")
        require_exact_keys(file, {"path", "sha256"}, f"producer_file[{index}]")
        file_path = safe_repo_path(file["path"], f"producer_file[{index}].path")
        digest = require_string(file["sha256"], f"producer_file[{index}].sha256")
        require(bool(BASE.SHA256_RE.fullmatch(digest)), f"producer_file[{index}] bad hash")
        paths.append(file_path.as_posix())
    require(paths == sorted(paths), "producer files must be sorted")
    require(len(paths) == len(set(paths)), "duplicate producer file")
    return manifest


def validate_registered_file(path: Path, expected_sha256: str, where: str) -> None:
    require(path.is_file(), f"{where}: missing file {path}")
    require(BASE.sha256_file(path) == expected_sha256, f"{where}: SHA-256 drift")


def validate_tool(spec: dict[str, Any], name: str) -> dict[str, str]:
    command = Path(spec["command"])
    require(command.is_file(), f"registered {name} is unavailable: {command}")
    realpath = str(command.resolve())
    require(realpath == spec["realpath"], f"{name}: realpath drift: {realpath}")
    digest = BASE.sha256_file(Path(realpath))
    require(digest == spec["sha256"], f"{name}: executable SHA-256 drift")
    completed = subprocess.run(
        [str(command), "--version"],
        check=False,
        capture_output=True,
        text=True,
        env=BASE.fixed_env(),
    )
    require(completed.returncode == 0, f"{name} --version failed")
    first_line = next((line for line in completed.stdout.splitlines() if line), "")
    require(first_line == spec["version_first_line"], f"{name}: version drift: {first_line}")
    return {"realpath": realpath, "sha256": digest, "version_first_line": first_line}


def load_registered_inputs(
    manifest: dict[str, Any], glaurung_root: Path | None
) -> tuple[dict[str, Any], dict[str, Any], dict[str, dict[str, str]]]:
    structural_manifest_path = REPO / manifest["structural_manifest"]["path"]
    structural_result_path = REPO / manifest["structural_result"]["path"]
    validate_registered_file(
        structural_manifest_path,
        manifest["structural_manifest"]["sha256"],
        "structural manifest",
    )
    validate_registered_file(
        structural_result_path,
        manifest["structural_result"]["sha256"],
        "structural result",
    )
    structural_manifest = BASE.load_manifest(structural_manifest_path)
    structural_result = BASE.load_result(
        structural_result_path, structural_manifest_path, structural_manifest
    )
    require(structural_result["summary"]["loops"] == 12, "expected 12 structural loops")
    require(
        structural_result["summary"]["functions_with_loops"] == 12,
        "expected 12 structural loop functions",
    )
    if glaurung_root is not None:
        BASE.validate_glaurung(glaurung_root, structural_manifest)
    for name in ("clang", "llvm_as"):
        BASE.tool_identity(structural_manifest["toolchain"][name])

    for file in manifest["producer_files"]:
        validate_registered_file(REPO / file["path"], file["sha256"], file["path"])
    tool_report = {
        name: validate_tool(manifest["toolchain"][name], name)
        for name in ("cargo", "llvm_extract", "rustc")
    }
    return structural_manifest, structural_result, tool_report


def run_checked(
    args: Sequence[str], *, cwd: Path, environment: dict[str, str] | None = None
) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        list(args),
        cwd=cwd,
        env=environment if environment is not None else BASE.fixed_env(),
        check=False,
        capture_output=True,
        text=True,
    )
    require(
        completed.returncode == 0,
        f"command failed ({completed.returncode}): {' '.join(args)}\n{completed.stderr}",
    )
    return completed


def parse_classifier_output(
    stdout: str, stderr: str, *, expected_function: str | None = None
) -> dict[str, Any]:
    values: dict[str, str] = {}
    for line in stdout.splitlines():
        require("=" in line, f"classifier emitted malformed line: {line}")
        key, value = line.split("=", 1)
        require(key not in values, f"classifier emitted duplicate key: {key}")
        values[key] = value
    require(set(values) == CLASSIFIER_KEYS, f"classifier fields drift: {sorted(values)}")
    require(values["stage"] in STAGES, f"classifier stage drift: {values['stage']}")
    require(bool(values["kind"]), "classifier kind is empty")
    function = values["function"]
    if not function:
        require(
            values["stage"] == "function_syntax" and bool(expected_function),
            "classifier function is empty outside an identified function-syntax rejection",
        )
        function = expected_function or ""
    for field in ("state_components", "iteration_paths"):
        require(values[field].isdigit(), f"classifier {field} is not an integer")
    state_components = int(values["state_components"])
    iteration_paths = int(values["iteration_paths"])
    if values["stage"] == "accepted":
        require(values["kind"] in {"self_loop", "single_latch"}, "accepted kind drift")
        require(state_components > 0 and iteration_paths > 0, "accepted metadata is empty")
        require(not stderr, "accepted classifier row emitted a diagnostic")
    else:
        require(state_components == 0 and iteration_paths == 0, "rejected metadata is nonzero")
        require(bool(stderr), "rejected classifier row lacks a precise diagnostic")
    return {
        "diagnostic": stderr,
        "function": function,
        "iteration_paths": iteration_paths,
        "kind": values["kind"],
        "stage": values["stage"],
        "state_components": state_components,
    }


def select_rejection(rows: list[dict[str, Any]], selection: dict[str, Any]) -> dict[str, Any] | None:
    buckets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["stage"] != "accepted":
            buckets[f"{row['stage']}:{row['kind']}"].append(row)
    if not buckets:
        return None
    ranked = sorted(buckets.items(), key=lambda item: (-len(item[1]), item[0]))
    bucket, selected_rows = ranked[0]
    second_count = len(ranked[1][1]) if len(ranked) > 1 else 0
    functions = {row["function"] for row in selected_rows}
    sources = {row["source_path"] for row in selected_rows}
    if selection["require_strict_plurality"] and len(selected_rows) <= second_count:
        return None
    if len(functions) < selection["minimum_functions"]:
        return None
    if len(sources) < selection["minimum_sources"]:
        return None
    return {
        "bucket": bucket,
        "functions": len(functions),
        "rows": len(selected_rows),
        "sources": len(sources),
    }


def run_census(
    manifest_path: Path, manifest: dict[str, Any], glaurung_root: Path
) -> dict[str, Any]:
    structural_manifest, structural_result, tool_report = load_registered_inputs(
        manifest, glaurung_root
    )
    cargo = manifest["toolchain"]["cargo"]["command"]
    rustc = manifest["toolchain"]["rustc"]["command"]
    llvm_extract = manifest["toolchain"]["llvm_extract"]["command"]
    clang = structural_manifest["toolchain"]["clang"]["command"]
    llvm_as = structural_manifest["toolchain"]["llvm_as"]["command"]
    structural_sources = {
        source["path"]: source for source in structural_result["sources"]
    }

    source_reports: list[dict[str, Any]] = []
    all_rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="axeyum-loop-semantics-") as temporary:
        temporary_root = Path(temporary)
        build_env = BASE.fixed_env()
        build_env.update({"CARGO_INCREMENTAL": "0", "RUSTC": rustc})
        run_checked([cargo, *manifest["cargo_args"]], cwd=REPO, environment=build_env)
        classifier = REPO / "target" / "debug" / "axeyum-llvm-loop-classify"
        require(classifier.is_file(), "classifier build produced no binary")

        for index, source in enumerate(structural_manifest["glaurung"]["sources"]):
            relative = source["path"]
            expected = structural_sources[relative]
            llvm_path = temporary_root / f"source-{index:02}.ll"
            compile_args = [clang, *structural_manifest["compile"]["args"]]
            compile_args.extend(
                f"-I{include}" for include in structural_manifest["compile"]["include_dirs"]
            )
            compile_args.extend([relative, "-o", str(llvm_path)])
            compiled = run_checked(compile_args, cwd=glaurung_root)
            run_checked([llvm_as, str(llvm_path), "-o", os.devnull], cwd=glaurung_root)
            normalized_stderr = compiled.stderr.replace(str(glaurung_root), "<glaurung>")
            require(
                BASE.sha256_file(llvm_path) == expected["llvm_sha256"],
                f"compiled LLVM drift: {relative}",
            )
            require(
                normalized_stderr == expected["compile_stderr"],
                f"compile diagnostic drift: {relative}",
            )
            loop_reports: list[dict[str, Any]] = []
            for loop_index, structural_loop in enumerate(expected["loops"]):
                function = structural_loop["function"]
                extracted = temporary_root / f"source-{index:02}-loop-{loop_index:02}.ll"
                run_checked(
                    [llvm_extract, f"--func={function}", "-S", str(llvm_path), "-o", str(extracted)],
                    cwd=glaurung_root,
                )
                run_checked([llvm_as, str(extracted), "-o", os.devnull], cwd=glaurung_root)
                classified = run_checked([str(classifier), str(extracted)], cwd=REPO)
                semantic = parse_classifier_output(
                    classified.stdout,
                    classified.stderr.removesuffix("\n"),
                    expected_function=function,
                )
                require(
                    semantic["function"] == function,
                    f"extracted function drift: expected {function}, got {semantic['function']}",
                )
                row = {
                    **semantic,
                    "extracted_llvm_sha256": BASE.sha256_file(extracted),
                    "source_path": relative,
                    "structural_profile": structural_loop["profile"],
                }
                loop_reports.append(row)
                all_rows.append(row)
            source_reports.append(
                {
                    "compile_stderr": normalized_stderr,
                    "llvm_sha256": expected["llvm_sha256"],
                    "loops": loop_reports,
                    "path": relative,
                    "source_sha256": source["sha256"],
                }
            )
        classifier_sha256 = BASE.sha256_file(classifier)

    stage_counts = Counter(row["stage"] for row in all_rows)
    outcome_counts = Counter(f"{row['stage']}:{row['kind']}" for row in all_rows)
    return {
        "classifier_binary_sha256": classifier_sha256,
        "glaurung_revision": structural_manifest["glaurung"]["revision"],
        "manifest_sha256": BASE.sha256_file(manifest_path),
        "schema": RESULT_SCHEMA,
        "selection": select_rejection(all_rows, manifest["selection"]),
        "sources": source_reports,
        "summary": {
            "accepted": stage_counts["accepted"],
            "outcome_counts": dict(sorted(outcome_counts.items())),
            "rejected": len(all_rows) - stage_counts["accepted"],
            "rows": len(all_rows),
            "sources": len(source_reports),
            "stage_counts": {stage: stage_counts[stage] for stage in STAGES},
        },
        "toolchain": tool_report,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--glaurung-root", type=Path)
    args = parser.parse_args(argv)
    try:
        require(args.validate != args.run, "select exactly one of --validate or --run")
        manifest = load_manifest(args.manifest)
        root = args.glaurung_root.resolve() if args.glaurung_root is not None else None
        if args.validate:
            load_registered_inputs(manifest, root)
            print(
                json.dumps(
                    {
                        "environment_verified": root is not None,
                        "manifest_sha256": BASE.sha256_file(args.manifest),
                        "schema": SCHEMA,
                        "status": "valid-zero-row",
                    },
                    sort_keys=True,
                )
            )
            return 0
        require(root is not None, "--run requires --glaurung-root")
        result = run_census(args.manifest, manifest, root)
        output = Path(manifest["formal_output"])
        state = BASE.retain_exact(output, BASE.canonical_json(result))
        print(json.dumps({"output": output.as_posix(), "state": state, **result["summary"]}, sort_keys=True))
        return 0
    except (SemanticCensusError, BASE.CensusError, OSError, UnicodeError) as error:
        print(f"semantic loop census: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
