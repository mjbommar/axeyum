#!/usr/bin/env python3
"""Produce the preregistered ADR-0293 Glaurung LLVM loop-shape census."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "axeyum.glaurung-llvm-loop-census.v1"
RESULT_SCHEMA = "axeyum.glaurung-llvm-loop-census-result.v1"
DEFAULT_MANIFEST = Path("docs/consumer-track/verify/glaurung-llvm-loop-census-v1.json")
EXPECTED_COMPILE_ARGS = [
    "--target=x86_64-pc-linux-gnu",
    "-O1",
    "-fno-unroll-loops",
    "-fno-vectorize",
    "-fno-slp-vectorize",
    "-fno-strict-aliasing",
    "-S",
    "-emit-llvm",
]
EXPECTED_OPT_ARGS = ["-passes=print<loops>", "-disable-output"]
PROFILES = [
    "adr0291_self_loop_shape",
    "adr0292_single_latch_shape",
    "single_latch_early_exit_shape",
    "single_latch_no_exit_shape",
    "multi_latch_shape",
    "nested_shape",
    "other_shape",
]
FUNCTION_RE = re.compile(r"^Loop info for function '([^']+)':$")
LOOP_RE = re.compile(r"^(?:Parallel )?Loop at depth (\d+) containing: (.+)$")
TAG_RE = re.compile(r"<([^>]+)>")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class CensusError(RuntimeError):
    """The registered census cannot be validated or reproduced."""


@dataclass(frozen=True)
class LoopBlock:
    """One block and the roles printed by LLVM LoopInfo."""

    name: str
    tags: tuple[str, ...]


@dataclass(frozen=True)
class LoopRow:
    """One LoopInfo row before profile classification."""

    function: str
    depth: int
    blocks: tuple[LoopBlock, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CensusError(message)


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


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def safe_relative_path(raw: str, where: str) -> Path:
    path = Path(require_string(raw, where))
    require(not path.is_absolute() and ".." not in path.parts, f"{where}: unsafe path")
    return path


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CensusError(f"cannot decode manifest {path}: {error}") from error
    manifest = require_object(value, "manifest")
    require_exact_keys(
        manifest,
        {
            "schema",
            "result_state",
            "glaurung",
            "toolchain",
            "compile",
            "loop_analysis",
            "formal_output",
        },
        "manifest",
    )
    require(manifest["schema"] == SCHEMA, f"manifest.schema: expected {SCHEMA}")
    require(manifest["result_state"] == "zero-row", "manifest must remain zero-row")

    glaurung = require_object(manifest["glaurung"], "manifest.glaurung")
    require_exact_keys(glaurung, {"revision", "sources"}, "manifest.glaurung")
    revision = require_string(glaurung["revision"], "manifest.glaurung.revision")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", revision)), "invalid Glaurung revision")
    sources = require_list(glaurung["sources"], "manifest.glaurung.sources")
    require(len(sources) == 12, "manifest must register exactly 12 C sources")
    source_paths: list[str] = []
    for index, raw_source in enumerate(sources):
        source = require_object(raw_source, f"source[{index}]")
        require_exact_keys(source, {"path", "sha256"}, f"source[{index}]")
        path_text = require_string(source["path"], f"source[{index}].path")
        safe_relative_path(path_text, f"source[{index}].path")
        digest = require_string(source["sha256"], f"source[{index}].sha256")
        require(bool(SHA256_RE.fullmatch(digest)), f"source[{index}]: invalid SHA-256")
        source_paths.append(path_text)
    require(source_paths == sorted(source_paths), "source paths must be sorted")
    require(len(set(source_paths)) == len(source_paths), "duplicate source path")

    toolchain = require_object(manifest["toolchain"], "manifest.toolchain")
    require_exact_keys(toolchain, {"clang", "llvm_as", "opt"}, "manifest.toolchain")
    for name in ("clang", "llvm_as", "opt"):
        tool = require_object(toolchain[name], f"manifest.toolchain.{name}")
        require_exact_keys(
            tool,
            {"command", "realpath", "sha256", "version_first_line"},
            f"manifest.toolchain.{name}",
        )
        require_string(tool["command"], f"toolchain.{name}.command")
        require(
            Path(
                require_string(tool["realpath"], f"toolchain.{name}.realpath")
            ).is_absolute(),
            f"toolchain.{name}.realpath must be absolute",
        )
        require(
            bool(
                SHA256_RE.fullmatch(
                    require_string(tool["sha256"], f"toolchain.{name}.sha256")
                )
            ),
            f"toolchain.{name}: invalid SHA-256",
        )
        require_string(tool["version_first_line"], f"toolchain.{name}.version_first_line")

    compile_spec = require_object(manifest["compile"], "manifest.compile")
    require_exact_keys(compile_spec, {"args", "include_dirs"}, "manifest.compile")
    require(compile_spec["args"] == EXPECTED_COMPILE_ARGS, "compile argument drift")
    require(compile_spec["include_dirs"] == ["samples/source/library"], "include drift")
    analysis = require_object(manifest["loop_analysis"], "manifest.loop_analysis")
    require_exact_keys(analysis, {"args", "profiles"}, "manifest.loop_analysis")
    require(analysis["args"] == EXPECTED_OPT_ARGS, "LoopInfo argument drift")
    require(analysis["profiles"] == PROFILES, "profile taxonomy drift")
    safe_relative_path(
        require_string(manifest["formal_output"], "manifest.formal_output"),
        "manifest.formal_output",
    )
    return manifest


def parse_blocks(raw: str) -> tuple[LoopBlock, ...]:
    blocks: list[LoopBlock] = []
    for index, piece in enumerate(raw.split(",")):
        piece = piece.strip()
        require(piece.startswith("%"), f"LoopInfo block[{index}] lacks `%`: {piece}")
        name = piece.split("<", 1)[0]
        require(bool(name), f"LoopInfo block[{index}] has no name")
        tags = tuple(TAG_RE.findall(piece))
        reconstructed = name + "".join(f"<{tag}>" for tag in tags)
        require(reconstructed == piece, f"unexpected LoopInfo block syntax: {piece}")
        blocks.append(LoopBlock(name=name, tags=tags))
    require(bool(blocks), "LoopInfo row has no blocks")
    return tuple(blocks)


def parse_loop_info(text: str) -> tuple[list[str], list[LoopRow]]:
    functions: list[str] = []
    rows: list[LoopRow] = []
    current_function: str | None = None
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        function_match = FUNCTION_RE.fullmatch(line)
        if function_match:
            current_function = function_match.group(1)
            require(current_function not in functions, f"duplicate function row: {current_function}")
            functions.append(current_function)
            continue
        loop_match = LOOP_RE.fullmatch(line)
        require(loop_match is not None, f"unrecognized opt LoopInfo output: {line}")
        require(current_function is not None, "LoopInfo row precedes its function")
        rows.append(
            LoopRow(
                function=current_function,
                depth=int(loop_match.group(1)),
                blocks=parse_blocks(loop_match.group(2)),
            )
        )
    return functions, rows


def classify_loop(row: LoopRow, *, function_has_nested_loop: bool) -> str:
    if function_has_nested_loop:
        return "nested_shape"
    headers = [block for block in row.blocks if "header" in block.tags]
    latches = [block for block in row.blocks if "latch" in block.tags]
    exiting = [block for block in row.blocks if "exiting" in block.tags]
    if len(headers) != 1:
        return "other_shape"
    header = headers[0]
    if len(row.blocks) == 1 and len(latches) == 1 and latches[0] == header:
        return "adr0291_self_loop_shape" if exiting == [header] else "other_shape"
    if len(latches) > 1:
        return "multi_latch_shape"
    if len(latches) != 1:
        return "other_shape"
    latch = latches[0]
    if not exiting:
        return "single_latch_no_exit_shape"
    if exiting == [latch]:
        return "adr0292_single_latch_shape"
    return "single_latch_early_exit_shape"


def tool_identity(spec: dict[str, Any]) -> tuple[str, dict[str, str]]:
    command = require_string(spec["command"], "tool.command")
    discovered = shutil.which(command)
    require(discovered is not None, f"registered tool is unavailable: {command}")
    realpath = str(Path(discovered).resolve())
    require(realpath == spec["realpath"], f"{command}: realpath drift: {realpath}")
    digest = sha256_file(Path(realpath))
    require(digest == spec["sha256"], f"{command}: executable SHA-256 drift")
    completed = subprocess.run(
        [command, "--version"], check=False, capture_output=True, text=True, env=fixed_env()
    )
    require(completed.returncode == 0, f"{command} --version failed")
    first_line = next((line for line in completed.stdout.splitlines() if line), "")
    require(first_line == spec["version_first_line"], f"{command}: version drift: {first_line}")
    return command, {
        "realpath": realpath,
        "sha256": digest,
        "version_first_line": first_line,
    }


def fixed_env() -> dict[str, str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C", "TZ": "UTC", "SOURCE_DATE_EPOCH": "0"})
    return environment


def run_checked(args: Sequence[str], *, cwd: Path) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        list(args), cwd=cwd, env=fixed_env(), check=False, capture_output=True, text=True
    )
    require(
        completed.returncode == 0,
        f"command failed ({completed.returncode}): {' '.join(args)}\n{completed.stderr}",
    )
    return completed


def validate_glaurung(root: Path, manifest: dict[str, Any]) -> None:
    require(root.is_dir(), f"Glaurung root is not a directory: {root}")
    revision = run_checked(["git", "rev-parse", "HEAD"], cwd=root).stdout.strip()
    require(revision == manifest["glaurung"]["revision"], f"Glaurung revision drift: {revision}")
    paths = [source["path"] for source in manifest["glaurung"]["sources"]]
    status = run_checked(
        ["git", "status", "--porcelain", "--untracked-files=all", "--", *paths], cwd=root
    ).stdout
    require(not status.strip(), f"registered Glaurung sources are dirty:\n{status}")
    for source in manifest["glaurung"]["sources"]:
        path = root / safe_relative_path(source["path"], "source.path")
        require(path.is_file(), f"registered source is missing: {source['path']}")
        require(sha256_file(path) == source["sha256"], f"source SHA-256 drift: {source['path']}")


def validate_registered_environment(root: Path, manifest: dict[str, Any]) -> None:
    """Validate the pinned sources and tools without observing LoopInfo rows."""

    validate_glaurung(root, manifest)
    for name in ("clang", "llvm_as", "opt"):
        tool_identity(manifest["toolchain"][name])


def loop_json(row: LoopRow, profile: str) -> dict[str, Any]:
    return {
        "blocks": [{"name": block.name, "tags": list(block.tags)} for block in row.blocks],
        "depth": row.depth,
        "function": row.function,
        "profile": profile,
    }


def run_census(manifest_path: Path, manifest: dict[str, Any], root: Path) -> dict[str, Any]:
    validate_glaurung(root, manifest)
    tools: dict[str, str] = {}
    tool_report: dict[str, dict[str, str]] = {}
    for name in ("clang", "llvm_as", "opt"):
        command, identity = tool_identity(manifest["toolchain"][name])
        tools[name] = command
        tool_report[name] = identity

    sources_report: list[dict[str, Any]] = []
    profile_counts: Counter[str] = Counter()
    functions_with_loops = 0
    with tempfile.TemporaryDirectory(prefix="axeyum-loop-census-") as temporary:
        temporary_root = Path(temporary)
        for index, source in enumerate(manifest["glaurung"]["sources"]):
            relative = source["path"]
            llvm_path = temporary_root / f"source-{index:02}.ll"
            compile_args = [tools["clang"], *manifest["compile"]["args"]]
            compile_args.extend(f"-I{include}" for include in manifest["compile"]["include_dirs"])
            compile_args.extend([relative, "-o", str(llvm_path)])
            compiled = run_checked(compile_args, cwd=root)
            run_checked([tools["llvm_as"], str(llvm_path), "-o", os.devnull], cwd=root)
            analyzed = run_checked(
                [tools["opt"], *manifest["loop_analysis"]["args"], str(llvm_path)], cwd=root
            )
            functions, rows = parse_loop_info(analyzed.stderr)
            nested_functions = {
                row.function for row in rows if row.depth > 1
            }
            classified = [
                (row, classify_loop(row, function_has_nested_loop=row.function in nested_functions))
                for row in rows
            ]
            profile_counts.update(profile for _, profile in classified)
            functions_with_loops += len({row.function for row, _ in classified})
            normalized_stderr = compiled.stderr.replace(str(root), "<glaurung>")
            sources_report.append(
                {
                    "compile_stderr": normalized_stderr,
                    "functions_seen": functions,
                    "llvm_sha256": sha256_file(llvm_path),
                    "loops": [loop_json(row, profile) for row, profile in classified],
                    "opt_stderr_sha256": sha256_bytes(analyzed.stderr.encode("utf-8")),
                    "path": relative,
                    "source_sha256": source["sha256"],
                }
            )

    return {
        "compile": manifest["compile"],
        "glaurung_revision": manifest["glaurung"]["revision"],
        "loop_analysis": manifest["loop_analysis"],
        "manifest_sha256": sha256_file(manifest_path),
        "schema": RESULT_SCHEMA,
        "sources": sources_report,
        "summary": {
            "functions_with_loops": functions_with_loops,
            "loops": sum(profile_counts.values()),
            "profile_counts": {profile: profile_counts[profile] for profile in PROFILES},
            "sources": len(sources_report),
        },
        "toolchain": tool_report,
    }


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def retain_exact(path: Path, payload: bytes) -> str:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        require(path.read_bytes() == payload, f"existing result is not byte-identical: {path}")
        return "reproduced"
    with tempfile.NamedTemporaryFile(dir=path.parent, prefix=f".{path.name}.", delete=False) as tmp:
        temporary = Path(tmp.name)
        tmp.write(payload)
        tmp.flush()
        os.fsync(tmp.fileno())
    temporary.replace(path)
    return "created"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--validate", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--glaurung-root", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)
    try:
        require(args.validate != args.run, "select exactly one of --validate or --run")
        manifest = load_manifest(args.manifest)
        if args.validate:
            if args.glaurung_root is not None:
                validate_registered_environment(args.glaurung_root.resolve(), manifest)
            print(
                json.dumps(
                    {
                        "environment_verified": args.glaurung_root is not None,
                        "manifest_sha256": sha256_file(args.manifest),
                        "schema": SCHEMA,
                        "sources": len(manifest["glaurung"]["sources"]),
                        "status": "valid-zero-row",
                    },
                    sort_keys=True,
                )
            )
            return 0
        require(args.glaurung_root is not None, "--run requires --glaurung-root")
        registered_out = Path(manifest["formal_output"])
        out = args.out if args.out is not None else registered_out
        require(out == registered_out, f"formal output path drift: {out}")
        result = run_census(args.manifest, manifest, args.glaurung_root.resolve())
        state = retain_exact(out, canonical_json(result))
        print(
            json.dumps(
                {"output": out.as_posix(), "state": state, **result["summary"]}, sort_keys=True
            )
        )
        return 0
    except (CensusError, OSError, UnicodeError) as error:
        print(f"loop census: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
