#!/usr/bin/env python3
"""Validate and optionally reproduce the ADR-0295 Glaurung call fixture."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = Path(
    "docs/consumer-track/verify/glaurung-llvm-direct-call-v1.json"
)
SCHEMA = "axeyum.glaurung-llvm-direct-call.v1"
SHA256_RE = re.compile(r"[0-9a-f]{64}")
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
EXPECTED_FUNCTIONS = ["compute", "leaf", "main"]


class ValidationError(ValueError):
    """The registered fixture or live reproduction is inconsistent."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def require_object(value: Any, where: str) -> dict[str, Any]:
    require(isinstance(value, dict), f"{where}: expected object")
    return value


def require_list(value: Any, where: str) -> list[Any]:
    require(isinstance(value, list), f"{where}: expected array")
    return value


def require_string(value: Any, where: str) -> str:
    require(isinstance(value, str) and bool(value), f"{where}: expected nonempty string")
    return value


def require_keys(value: dict[str, Any], keys: set[str], where: str) -> None:
    actual = set(value)
    require(
        actual == keys,
        f"{where}: fields differ: missing={sorted(keys - actual)} "
        f"unexpected={sorted(actual - keys)}",
    )


def safe_relative(raw: str, where: str) -> Path:
    path = Path(require_string(raw, where))
    require(not path.is_absolute() and ".." not in path.parts, f"{where}: unsafe path")
    return path


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_file(path: Path) -> str:
    return digest_bytes(path.read_bytes())


def validate_file(root: Path, spec: dict[str, Any], where: str) -> Path:
    require_keys(spec, {"path", "sha256"}, where)
    path = root / safe_relative(spec["path"], f"{where}.path")
    expected = require_string(spec["sha256"], f"{where}.sha256")
    require(bool(SHA256_RE.fullmatch(expected)), f"{where}: invalid SHA-256")
    require(path.is_file(), f"{where}: missing file {path}")
    require(digest_file(path) == expected, f"{where}: SHA-256 drift")
    return path


def extract_function(module: bytes, name: str) -> bytes:
    marker = f"@{name}(".encode()
    marker_start = module.find(marker)
    require(marker_start >= 0, f"module: missing function `{name}`")
    start = module.rfind(b"define ", 0, marker_start)
    require(start >= 0, f"module: missing definition start for `{name}`")
    relative_end = module.find(b"\n}\n", marker_start)
    require(relative_end >= 0, f"module: missing definition end for `{name}`")
    return module[start : relative_end + 3]


def load_and_validate(manifest_path: Path, repo: Path = REPO) -> dict[str, Any]:
    try:
        value = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot decode manifest {manifest_path}: {error}") from error
    manifest = require_object(value, "manifest")
    require_keys(
        manifest,
        {"compile", "fixture", "glaurung", "schema", "toolchain"},
        "manifest",
    )
    require(manifest["schema"] == SCHEMA, f"manifest.schema: expected {SCHEMA}")

    compile_spec = require_object(manifest["compile"], "manifest.compile")
    require_keys(compile_spec, {"args", "include_dirs"}, "manifest.compile")
    require(compile_spec["args"] == EXPECTED_COMPILE_ARGS, "compile argument drift")
    require(
        compile_spec["include_dirs"] == ["samples/source/library"],
        "compile include-directory drift",
    )

    glaurung = require_object(manifest["glaurung"], "manifest.glaurung")
    require_keys(glaurung, {"revision", "source"}, "manifest.glaurung")
    revision = require_string(glaurung["revision"], "manifest.glaurung.revision")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", revision)), "invalid Glaurung revision")
    source_spec = require_object(glaurung["source"], "manifest.glaurung.source")
    require_keys(source_spec, {"path", "sha256"}, "manifest.glaurung.source")
    safe_relative(source_spec["path"], "manifest.glaurung.source.path")
    require(
        bool(SHA256_RE.fullmatch(require_string(source_spec["sha256"], "source hash"))),
        "invalid Glaurung source SHA-256",
    )

    fixture = require_object(manifest["fixture"], "manifest.fixture")
    require_keys(fixture, {"functions", "module", "source"}, "manifest.fixture")
    fixture_source = validate_file(
        repo, require_object(fixture["source"], "fixture.source"), "fixture.source"
    )
    module_path = validate_file(
        repo, require_object(fixture["module"], "fixture.module"), "fixture.module"
    )
    require(
        digest_file(fixture_source) == source_spec["sha256"],
        "fixture and Glaurung source hashes differ",
    )
    module = module_path.read_bytes()
    functions = require_list(fixture["functions"], "fixture.functions")
    names: list[str] = []
    for index, raw in enumerate(functions):
        function = require_object(raw, f"fixture.functions[{index}]")
        require_keys(function, {"name", "sha256"}, f"fixture.functions[{index}]")
        name = require_string(function["name"], f"fixture.functions[{index}].name")
        expected = require_string(function["sha256"], f"fixture.functions[{index}].sha256")
        require(bool(SHA256_RE.fullmatch(expected)), f"function `{name}` invalid SHA-256")
        require(digest_bytes(extract_function(module, name)) == expected,
                f"function `{name}` SHA-256 drift")
        names.append(name)
    require(names == EXPECTED_FUNCTIONS, f"function inventory drift: {names}")

    toolchain = require_object(manifest["toolchain"], "manifest.toolchain")
    require_keys(toolchain, {"clang"}, "manifest.toolchain")
    clang = require_object(toolchain["clang"], "manifest.toolchain.clang")
    require_keys(
        clang,
        {"command", "realpath", "sha256", "version_first_line"},
        "manifest.toolchain.clang",
    )
    for field in ("command", "realpath", "version_first_line"):
        require_string(clang[field], f"manifest.toolchain.clang.{field}")
    require(Path(clang["command"]).is_absolute(), "clang command must be absolute")
    require(Path(clang["realpath"]).is_absolute(), "clang realpath must be absolute")
    require(bool(SHA256_RE.fullmatch(require_string(clang["sha256"], "clang hash"))),
            "invalid clang SHA-256")
    return manifest


def fixed_env() -> dict[str, str]:
    env = os.environ.copy()
    env.update({"LC_ALL": "C", "LANG": "C", "TZ": "UTC", "SOURCE_DATE_EPOCH": "0"})
    return env


def reproduce(manifest: dict[str, Any], glaurung_root: Path, repo: Path = REPO) -> None:
    root = glaurung_root.resolve()
    require((root / ".git").exists(), f"not a Glaurung git checkout: {root}")
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    require(revision == manifest["glaurung"]["revision"],
            f"Glaurung revision drift: {revision}")
    source_spec = manifest["glaurung"]["source"]
    source = root / safe_relative(source_spec["path"], "glaurung.source.path")
    require(source.is_file(), f"missing Glaurung source: {source}")
    require(digest_file(source) == source_spec["sha256"], "live Glaurung source SHA-256 drift")
    fixture_source = repo / manifest["fixture"]["source"]["path"]
    require(source.read_bytes() == fixture_source.read_bytes(),
            "live and committed Glaurung sources differ")

    clang_spec = manifest["toolchain"]["clang"]
    clang = Path(clang_spec["command"])
    require(clang.is_file(), f"registered clang is unavailable: {clang}")
    require(str(clang.resolve()) == clang_spec["realpath"], "clang realpath drift")
    require(digest_file(clang.resolve()) == clang_spec["sha256"], "clang SHA-256 drift")
    version = subprocess.run(
        [str(clang), "--version"],
        check=True,
        capture_output=True,
        text=True,
        env=fixed_env(),
    ).stdout.splitlines()[0]
    require(version == clang_spec["version_first_line"], f"clang version drift: {version}")

    with tempfile.TemporaryDirectory(prefix="axeyum-direct-call-") as temporary:
        output = Path(temporary) / "pac.ll"
        command = [str(clang), *manifest["compile"]["args"]]
        command.extend(f"-I{path}" for path in manifest["compile"]["include_dirs"])
        command.extend([source_spec["path"], "-o", str(output)])
        completed = subprocess.run(
            command,
            cwd=root,
            check=False,
            capture_output=True,
            env=fixed_env(),
        )
        require(completed.returncode == 0,
                f"registered clang command failed: {completed.stderr.decode(errors='replace')}")
        expected_module = repo / manifest["fixture"]["module"]["path"]
        require(output.read_bytes() == expected_module.read_bytes(),
                "live clang output differs from the committed module")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--glaurung-root", type=Path)
    args = parser.parse_args(argv)
    manifest_path = args.manifest if args.manifest.is_absolute() else REPO / args.manifest
    try:
        manifest = load_and_validate(manifest_path)
        if args.glaurung_root is not None:
            reproduce(manifest, args.glaurung_root)
    except (OSError, subprocess.SubprocessError, ValidationError) as error:
        print(f"glaurung LLVM direct-call fixture: {error}", file=os.sys.stderr)
        return 1
    print(
        json.dumps(
            {
                "functions": EXPECTED_FUNCTIONS,
                "live_reproduced": args.glaurung_root is not None,
                "schema": SCHEMA,
                "status": "pass",
            },
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
