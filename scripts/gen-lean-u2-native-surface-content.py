#!/usr/bin/env python3
"""Derive TL0.6.4 M1's non-crediting pinned-content U2 surface census."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tomllib
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
from types import ModuleType
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

MANIFEST = ROOT / "docs/plan/lean-u2-native-surface-content-v1.json"
OUT_JSON = ROOT / "docs/plan/generated/lean-u2-native-surface-content.json"
OUT_MD = ROOT / "docs/plan/generated/lean-u2-native-surface-content.md"
U2_PATH = ROOT / "docs/plan/lean-u2-test-authority-v1.json"
U2_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-test-authority.py"
M0_PATH = ROOT / "docs/plan/lean-u2-native-surface-classification-v1.json"
M0_VALIDATOR_PATH = ROOT / "scripts/gen-lean-u2-native-surface-classification.py"
GENERATOR_PATH = ROOT / "scripts/gen-lean-u2-native-surface-content.py"
TEST_PATH = ROOT / "scripts/tests/test_lean_u2_native_surface_content.py"

SCHEMA = "axeyum-lean-u2-native-surface-content-v1"
REPORT_SCHEMA = "axeyum-lean-u2-native-surface-content-report-v1"
AS_OF = "2026-07-23"
TARGET_COMMIT = "d024af099ca4bf2c86f649261ebf59565dc8c622"
SOURCE_HASHES = {
    "docs/plan/lean-u2-test-authority-v1.json": (
        "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e"
    ),
    "docs/plan/lean-u2-native-surface-classification-v1.json": (
        "89b29bc6820d1d948d5cd4defdd28eb59ddb55a5924a3cf770c0b21282959959"
    ),
}
VALIDATOR_HASHES = {
    "scripts/gen-lean-u2-test-authority.py": (
        "2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba"
    ),
    "scripts/gen-lean-u2-native-surface-classification.py": (
        "4827fc4ed27e729b36f2c0451059e4a4c7e4186ac8650eb54e8e98b1d740ccf6"
    ),
}
EXPECTED_CONTENT_FILES_SHA256 = (
    "f2c8b9c9276ac85dfef7d8e4fc32abe2350a3ae9e659a9a5795cba7f0390631f"
)
EXPECTED_CASES_SHA256 = (
    "37050cfb25f0ecfa2256ccb9516124092fc611af5d7be94cce1e9e0745745cd3"
)
EXPECTED_M0_CASE_ROWS_SHA256 = (
    "f0c4d2cded9c0fb7a681438d6fe0e7b696e118cdafc5a2281bd13af51d9d1cdd"
)

SIGNAL_DOMAIN = "axeyum-lean-u2-native-content-signal-v1"
FILE_DOMAIN = "axeyum-lean-u2-native-content-file-v1"
SCOPE_DOMAIN = "axeyum-lean-u2-native-content-scope-v1"
CASE_DOMAIN = "axeyum-lean-u2-native-content-case-v1"

ROLE_ORDER = (
    "primary",
    "sidecar",
    "case-hook",
    "case-local-support",
    "family-runner",
    "registration-wrapper-template",
    "shared-support",
    "unreferenced-content",
)


def _signal(
    signal_id: str,
    description: str,
    media: list[str],
    matcher_kind: str,
    matcher: str,
    confidence: str,
    disposition: str,
    surfaces: list[str],
) -> dict[str, Any]:
    return {
        "id": signal_id,
        "version": 1,
        "description": description,
        "media_classes": media,
        "matcher_kind": matcher_kind,
        "matcher": matcher,
        "confidence": confidence,
        "disposition": disposition,
        "surface_effect": surfaces,
    }


SIGNALS: tuple[dict[str, Any], ...] = (
    _signal(
        "lean.syntax-declaration",
        "active syntax, macro, or macro_rules declaration token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:syntax|macro|macro_rules)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["parser-macro"],
    ),
    _signal(
        "lean.syntax-quotation",
        "active Lean syntax quotation opener",
        ["lean"],
        "lean-quotation",
        r"`[ \t]*\(",
        "exact-token",
        "promote",
        ["parser-macro"],
    ),
    _signal(
        "lean.elaborator-extension",
        "active elaborator extension declaration or API token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:elab|elab_rules|term_elab|command_elab|builtin_term_elab|builtin_command_elab)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["elaborator"],
    ),
    _signal(
        "lean.declaration",
        "active declaration-form token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:def|theorem|opaque|axiom|structure|class|inductive|instance)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["elaborator"],
    ),
    _signal(
        "lean.recursion-control",
        "active mutual, partial, termination_by, or decreasing_by token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:mutual|partial|termination_by|decreasing_by)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["elaborator"],
    ),
    _signal(
        "lean.tactic-block",
        "active by tactic-block token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])by(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["tactic-meta"],
    ),
    _signal(
        "lean.meta-api",
        "active Lean.Meta or Lean.Elab.Tactic API reference",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])Lean\.(?:Meta|Elab\.Tactic)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["tactic-meta"],
    ),
    _signal(
        "lean.import-command",
        "active line-leading import or prelude command",
        ["lean"],
        "lean-active-regex",
        r"(?m)^[ \t]*(?:public[ \t]+)?(?:import|prelude)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["kernel-import"],
    ),
    _signal(
        "lean.evaluation-command",
        "active #eval, #reduce, or run_tac command",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:#eval|#reduce|run_tac)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["compiler-runtime"],
    ),
    _signal(
        "lean.ffi-declaration",
        "active extern or implemented_by declaration token",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:extern|implemented_by)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["ffi"],
    ),
    _signal(
        "lean.server-api",
        "active Lean.Server, Lean.Widget, RequestM, or Rpc API reference",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])(?:Lean\.(?:Server|Widget)|RequestM|Rpc)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["editor-rpc"],
    ),
    _signal(
        "lean.compiler-api",
        "active Lean.Compiler, Lean.IR, or Lean.LCNF API reference",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])Lean\.(?:Compiler|IR|LCNF)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["compiler-runtime"],
    ),
    _signal(
        "lean.lake-api",
        "active Lake API namespace reference",
        ["lean"],
        "lean-active-regex",
        r"(?<![A-Za-z0-9_])Lake\.(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["modules-lake"],
    ),
    _signal(
        "toml.project-field",
        "parsed project/package/build field in TOML",
        ["toml"],
        "toml-key",
        "package|lean_lib|lean_exe|require|name|version",
        "structured-field",
        "promote",
        ["modules-lake"],
    ),
    _signal(
        "toml.native-link-field",
        "parsed native-library or linker field in TOML",
        ["toml"],
        "toml-key",
        "extern_lib|more_link_args|linkArgs|weakLinkArgs",
        "structured-field",
        "promote",
        ["ffi"],
    ),
    _signal(
        "json.rpc-method",
        "parsed JSON object with a string-valued method field",
        ["json"],
        "json-field",
        "method",
        "structured-field",
        "promote",
        ["editor-rpc"],
    ),
    _signal(
        "json.document-version",
        "parsed JSON document/version/edit/cancel field",
        ["json"],
        "json-field",
        "version|textDocument|contentChanges|cancel",
        "structured-field",
        "promote",
        ["editor-rpc"],
    ),
    _signal(
        "c.abi-declaration",
        "active C-family extern, dlopen, or Lean ABI token",
        ["c-family"],
        "c-active-regex",
        r"(?<![A-Za-z0-9_])(?:extern|dlopen|lean_object|LEAN_EXPORT)(?![A-Za-z0-9_])",
        "exact-token",
        "promote",
        ["ffi"],
    ),
    _signal(
        "shell.tool-command",
        "unquoted shell occurrence of lean, leanc, lake, cmake, ninja, or make",
        ["shell", "python", "text"],
        "text-active-regex",
        r"(?<![A-Za-z0-9_])(?:lean|leanc|lake|cmake|ninja|make)(?![A-Za-z0-9_])",
        "candidate",
        "candidate-only",
        ["toolchain-cli"],
    ),
    _signal(
        "shell.native-link-candidate",
        "unquoted shell/CMake occurrence of compiler, linker, plugin, or shared library token",
        ["shell", "python", "text"],
        "text-active-regex",
        r"(?<![A-Za-z0-9_])(?:cc|gcc|clang|leanc|dlopen|plugin|shared_library)(?![A-Za-z0-9_])",
        "candidate",
        "candidate-only",
        ["ffi"],
    ),
    _signal(
        "text.rpc-candidate",
        "textual RPC/LSP method or request marker requiring structured review",
        ["expected", "text", "shell", "python"],
        "text-active-regex",
        r"(?:textDocument/|\$/lean/|jsonrpc|RequestM)",
        "candidate",
        "candidate-only",
        ["editor-rpc"],
    ),
)

PINNED_POSITIVE_CONTROLS = {
    "tests/elab_bench/big_beq.lean": ["lean.syntax-declaration"],
    "tests/server_interactive/catHover.lean": ["lean.syntax-declaration"],
    "doc/examples/Certora2022/ex1.lean": ["lean.evaluation-command"],
    "tests/elab_bench/cbv_decide.lean": ["lean.meta-api"],
    "tests/misc_dir/server_project/run_test.lean": ["lean.server-api"],
    "tests/elab/toLCNFCacheBug.lean": ["lean.compiler-api"],
    "doc/examples/widgets.lean": ["lean.import-command"],
    "tests/elab_fail/test_extern.lean": ["lean.ffi-declaration"],
}

CLAIMS = {
    "all_tracked_u2_content_files_inspected": True,
    "all_registration_cases_content_projected": True,
    "content_signal_census_complete": True,
    "generated_wrappers_materialized": False,
    "module_dependency_closure_complete": False,
    "native_execution_observed": False,
    "matched_pair_formed": False,
    "performance_measured": False,
    "tl0_6_4_complete": False,
    "u2_complete": False,
    "lean_parity_established": False,
}
ZERO_CREDITS = {
    "official_outcomes": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}
RESIDUAL = [
    "Generated tests/with_stage1_test_env.sh references are inventoried but not materialized; M2 owns configured-wrapper closure.",
    "M2 must derive exact module, generated-artifact, runtime, library, FFI, request, and project dependency closures.",
    "M3 must review every provisional case row and resolve all candidate and no-signal-observed fields.",
    "TL0.6.5 may form native pairs only after accepted TL0.6.4 and matching complete official/native evidence.",
]


class ContentError(RuntimeError):
    """A fail-closed M1 content derivation or validation failure."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def seal(record: dict[str, Any], domain: str) -> dict[str, Any]:
    result = copy.deepcopy(record)
    result["record_sha256"] = domain_digest(
        domain, {key: value for key, value in result.items() if key != "record_sha256"}
    )
    return result


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ContentError(f"cannot read canonical JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ContentError(f"top-level JSON must be an object: {path}")
    return value


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ContentError(f"cannot import validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_frozen_inputs() -> tuple[dict[str, Any], dict[str, Any], ModuleType]:
    for relative, expected in SOURCE_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ContentError(f"frozen source authority drift: {relative}")
    for relative, expected in VALIDATOR_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ContentError(f"frozen validator source drift: {relative}")
    u2 = load_json(U2_PATH)
    u2_validator = load_script("lean_u2_content_parent_validator", U2_VALIDATOR_PATH)
    failures = u2_validator.validate_manifest(u2)
    if failures:
        raise ContentError("invalid frozen U2 authority: " + "; ".join(failures))
    m0 = load_json(M0_PATH)
    m0_validator = load_script("lean_u2_content_m0_validator", M0_VALIDATOR_PATH)
    failures = m0_validator.validate_authority(m0)
    if failures:
        raise ContentError("invalid frozen M0 authority: " + "; ".join(failures))
    if u2.get("content_files_sha256") != EXPECTED_CONTENT_FILES_SHA256:
        raise ContentError("frozen U2 content-list seal drift")
    if u2.get("cases_sha256") != EXPECTED_CASES_SHA256:
        raise ContentError("frozen U2 case-list seal drift")
    if m0.get("case_rows_sha256") != EXPECTED_M0_CASE_ROWS_SHA256:
        raise ContentError("frozen M0 case-row seal drift")
    return u2, m0, m0_validator


def safe_relative(path: str) -> bool:
    pure = PurePosixPath(path)
    return bool(path) and not pure.is_absolute() and ".." not in pure.parts and pure.as_posix() == path


def git_output(source_root: Path, *args: str) -> bytes:
    try:
        return subprocess.run(
            ["git", "-C", str(source_root), *args],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        detail = getattr(error, "stderr", b"").decode("utf-8", "replace").strip()
        raise ContentError(f"git {' '.join(args)} failed: {detail or error}") from error


def verify_source_root(source_root: Path, u2: dict[str, Any]) -> dict[str, bytes]:
    root = source_root.resolve()
    head = git_output(root, "rev-parse", "HEAD").decode("ascii").strip()
    if head != TARGET_COMMIT:
        raise ContentError(f"source HEAD drift: {head} != {TARGET_COMMIT}")
    entries: dict[str, tuple[str, str]] = {}
    raw = git_output(root, "ls-files", "-s", "-z")
    for item in raw.split(b"\0"):
        if not item:
            continue
        try:
            meta, path_bytes = item.split(b"\t", 1)
            mode, blob, stage = meta.decode("ascii").split()
            path = path_bytes.decode("utf-8")
        except (ValueError, UnicodeError) as error:
            raise ContentError("malformed git ls-files record") from error
        if stage != "0":
            raise ContentError(f"non-stage-zero source entry: {path}")
        entries[path] = (mode, blob)

    blobs: dict[str, bytes] = {}
    for expected in u2["content_files"]:
        path = expected["path"]
        if not safe_relative(path):
            raise ContentError(f"unsafe parent content path: {path}")
        observed = entries.get(path)
        if observed != (expected["mode"], expected["git_blob"]):
            raise ContentError(f"source Git identity drift: {path}")
        fs_path = root / path
        try:
            if expected["mode"] == "120000":
                if not fs_path.is_symlink():
                    raise ContentError(f"expected source symlink: {path}")
                data = os.readlink(fs_path).encode("utf-8")
            else:
                if not fs_path.is_file() or fs_path.is_symlink():
                    raise ContentError(f"expected regular source file: {path}")
                data = fs_path.read_bytes()
        except OSError as error:
            raise ContentError(f"cannot read source file {path}: {error}") from error
        if len(data) != expected["bytes"] or sha256_bytes(data) != expected["sha256"]:
            raise ContentError(f"source byte identity drift: {path}")
        blobs[path] = data
    if len(blobs) != len(u2["content_files"]):
        raise ContentError("source content coverage drift")
    return blobs


def media_class(path: str, mode: str, data: bytes) -> str:
    if mode == "120000":
        return "symlink"
    name = PurePosixPath(path).name.lower()
    suffix = PurePosixPath(path).suffix.lower()
    if b"\0" in data:
        return "binary"
    if suffix == ".lean":
        return "lean"
    if name.endswith(".expected"):
        return "expected"
    if suffix == ".toml":
        return "toml"
    if suffix == ".json":
        return "json"
    if suffix in {".c", ".cc", ".cpp", ".cxx", ".h", ".hpp"}:
        return "c-family"
    if suffix in {".sh", ".bash"} or name in {"test", "run_test"}:
        return "shell"
    if suffix == ".py":
        return "python"
    if suffix in {".txt", ".md", ".in", ".cmake", ".yaml", ".yml", ".nix"} or name == "cmakelists.txt":
        return "text"
    try:
        data.decode("utf-8")
    except UnicodeDecodeError:
        return "binary"
    return "text"


def mask_span(mask: bytearray, start: int, end: int) -> None:
    mask[start:end] = b"\0" * max(0, end - start)


def lean_active_mask(data: bytes) -> tuple[bytearray, list[tuple[int, int]]]:
    """Return active Lean bytes and balanced syntax-quotation spans."""
    mask = bytearray(b"\1" * len(data))
    quotations: list[tuple[int, int]] = []
    i = 0
    while i < len(data):
        if data.startswith(b"--", i):
            end = data.find(b"\n", i + 2)
            end = len(data) if end < 0 else end
            mask_span(mask, i, end)
            i = end
        elif data.startswith(b"/-", i):
            start = i
            depth = 1
            i += 2
            while i < len(data) and depth:
                if data.startswith(b"/-", i):
                    depth += 1
                    i += 2
                elif data.startswith(b"-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask_span(mask, start, i)
        elif data[i : i + 1] == b'"':
            start = i
            i += 1
            while i < len(data):
                if data[i : i + 1] == b"\\":
                    i += 2
                elif data[i : i + 1] == b'"':
                    i += 1
                    break
                else:
                    i += 1
            mask_span(mask, start, min(i, len(data)))
        elif data[i : i + 1] == b"`":
            probe = i + 1
            while probe < len(data) and data[probe : probe + 1] in b" \t":
                probe += 1
            if probe < len(data) and data[probe : probe + 1] == b"(":
                start = i
                depth = 0
                i = probe
                while i < len(data):
                    if data[i : i + 1] == b"(":
                        depth += 1
                    elif data[i : i + 1] == b")":
                        depth -= 1
                        if depth == 0:
                            i += 1
                            break
                    elif data[i : i + 1] == b'"':
                        i += 1
                        while i < len(data):
                            if data[i : i + 1] == b"\\":
                                i += 2
                            elif data[i : i + 1] == b'"':
                                break
                            else:
                                i += 1
                    i += 1
                quotations.append((start, min(i, len(data))))
                mask_span(mask, start, min(i, len(data)))
            else:
                i += 1
        else:
            i += 1
    return mask, quotations


def c_active_mask(data: bytes) -> bytearray:
    mask = bytearray(b"\1" * len(data))
    i = 0
    while i < len(data):
        if data.startswith(b"//", i) or data.startswith(b"#", i):
            end = data.find(b"\n", i + 1)
            end = len(data) if end < 0 else end
            mask_span(mask, i, end)
            i = end
        elif data.startswith(b"/*", i):
            end = data.find(b"*/", i + 2)
            end = len(data) if end < 0 else end + 2
            mask_span(mask, i, end)
            i = end
        elif data[i : i + 1] in {b'"', b"'"}:
            quote = data[i : i + 1]
            start = i
            i += 1
            while i < len(data):
                if data[i : i + 1] == b"\\":
                    i += 2
                elif data[i : i + 1] == quote:
                    i += 1
                    break
                else:
                    i += 1
            mask_span(mask, start, min(i, len(data)))
        else:
            i += 1
    return mask


def text_active_mask(data: bytes) -> bytearray:
    mask = bytearray(b"\1" * len(data))
    i = 0
    while i < len(data):
        if data[i : i + 1] == b"#":
            end = data.find(b"\n", i + 1)
            end = len(data) if end < 0 else end
            mask_span(mask, i, end)
            i = end
        elif data[i : i + 1] in {b'"', b"'"}:
            quote = data[i : i + 1]
            start = i
            i += 1
            while i < len(data):
                if data[i : i + 1] == b"\\":
                    i += 2
                elif data[i : i + 1] == quote:
                    i += 1
                    break
                else:
                    i += 1
            mask_span(mask, start, min(i, len(data)))
        else:
            i += 1
    return mask


def line_column(data: bytes, offset: int) -> tuple[int, int]:
    line = data.count(b"\n", 0, offset) + 1
    last = data.rfind(b"\n", 0, offset)
    column = offset + 1 if last < 0 else offset - last
    return line, column


def hit_record(
    data: bytes,
    signal: dict[str, Any],
    start: int,
    end: int,
    matcher_route: str,
) -> dict[str, Any]:
    line, column = line_column(data, start)
    context = data[max(0, start - 32) : min(len(data), end + 32)]
    return {
        "signal_id": signal["id"],
        "signal_version": signal["version"],
        "confidence": signal["confidence"],
        "disposition": signal["disposition"],
        "surface_effect": signal["surface_effect"],
        "byte_start": start,
        "byte_end": end,
        "line": line,
        "column": column,
        "matched_bytes": end - start,
        "matched_sha256": sha256_bytes(data[start:end]),
        "context_sha256": sha256_bytes(context),
        "matcher_route": matcher_route,
    }


def active_regex_hits(
    data: bytes,
    signal: dict[str, Any],
    mask: bytearray,
) -> list[dict[str, Any]]:
    pattern = re.compile(signal["matcher"].encode("ascii"), re.MULTILINE)
    hits = []
    for match in pattern.finditer(data):
        if match.end() > match.start() and all(mask[match.start() : match.end()]):
            hits.append(hit_record(data, signal, match.start(), match.end(), signal["matcher_kind"]))
    return hits


def structured_key_hits(
    data: bytes,
    signal: dict[str, Any],
    present_keys: set[str],
    toml: bool,
) -> list[dict[str, Any]]:
    allowed = signal["matcher"].split("|")
    keys = [key for key in allowed if key in present_keys]
    hits: list[dict[str, Any]] = []
    for key in keys:
        if toml:
            pattern = re.compile(rb"(?m)^[ \t]*" + re.escape(key.encode()) + rb"[ \t]*=")
        else:
            pattern = re.compile(rb'"' + re.escape(key.encode()) + rb'"[ \t]*:')
        for match in pattern.finditer(data):
            key_start = match.start() + match.group(0).find(key.encode())
            hits.append(hit_record(data, signal, key_start, key_start + len(key), signal["matcher_kind"]))
    return hits


def nested_keys(value: Any) -> Iterable[tuple[str, Any]]:
    if isinstance(value, dict):
        for key, child in value.items():
            yield str(key), child
            yield from nested_keys(child)
    elif isinstance(value, list):
        for child in value:
            yield from nested_keys(child)


def scan_content(path: str, mode: str, data: bytes) -> tuple[str, str, list[dict[str, Any]]]:
    media = media_class(path, mode, data)
    if media in {"binary", "symlink"}:
        return media, "inspected-no-decoder", []
    hits: list[dict[str, Any]] = []
    decoder_state = "decoded"
    lean_mask: bytearray | None = None
    quotations: list[tuple[int, int]] = []
    c_mask: bytearray | None = None
    text_mask: bytearray | None = None
    parsed_toml: Any = None
    parsed_json: Any = None
    if media == "lean":
        lean_mask, quotations = lean_active_mask(data)
    elif media == "c-family":
        c_mask = c_active_mask(data)
    elif media in {"shell", "python", "text"}:
        text_mask = text_active_mask(data)
    elif media == "toml":
        try:
            parsed_toml = tomllib.loads(data.decode("utf-8"))
        except (UnicodeDecodeError, tomllib.TOMLDecodeError):
            decoder_state = "malformed-structured"
    elif media == "json":
        try:
            parsed_json = json.loads(data.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError):
            decoder_state = "malformed-structured"

    for signal in SIGNALS:
        if media not in signal["media_classes"]:
            continue
        kind = signal["matcher_kind"]
        if kind == "lean-active-regex" and lean_mask is not None:
            hits.extend(active_regex_hits(data, signal, lean_mask))
        elif kind == "lean-quotation" and lean_mask is not None:
            for start, end in quotations:
                opener_end = data.find(b"(", start, end) + 1
                hits.append(hit_record(data, signal, start, opener_end, kind))
        elif kind == "c-active-regex" and c_mask is not None:
            hits.extend(active_regex_hits(data, signal, c_mask))
        elif kind == "text-active-regex" and text_mask is not None:
            hits.extend(active_regex_hits(data, signal, text_mask))
        elif kind == "toml-key" and parsed_toml is not None:
            hits.extend(structured_key_hits(data, signal, {key for key, _ in nested_keys(parsed_toml)}, True))
        elif kind == "json-field" and parsed_json is not None:
            pairs = list(nested_keys(parsed_json))
            if signal["id"] == "json.rpc-method":
                present = {key for key, value in pairs if key == "method" and isinstance(value, str)}
            else:
                present = {key for key, _ in pairs}
            hits.extend(structured_key_hits(data, signal, present, False))
    hits.sort(key=lambda row: (row["byte_start"], row["byte_end"], row["signal_id"]))
    return media, decoder_state, hits


def extract_registration_refs(case: dict[str, Any], content_paths: set[str]) -> tuple[list[str], list[str]]:
    tracked: set[str] = set()
    generated: set[str] = set()
    for argument in case["registration"]["command"]:
        for match in re.finditer(r"\$LEAN_ROOT/([A-Za-z0-9_./-]+)", argument):
            path = match.group(1).rstrip(".,;:)]}")
            if path in content_paths:
                tracked.add(path)
            elif re.fullmatch(r"tests/with_stage[0-9]+_(?:test|bench)_env\.sh", path):
                generated.add(path)
    source = case["source_path"]
    if PurePosixPath(source).name in {"run_test.sh", "test.sh"}:
        tracked.add(source)
    return sorted(tracked), sorted(generated)


def within_scope(path: str, scope: str) -> bool:
    return path == scope or path.startswith(scope + "/")


def derive_case_files(
    case: dict[str, Any], content_paths: list[str]
) -> dict[str, Any]:
    content_set = set(content_paths)
    primary = [case["source_path"]]
    sidecars = list(case["sidecars"])
    hooks = [
        case["source_path"] + suffix
        for suffix in (".init.sh", ".before.sh", ".after.sh")
        if case["source_path"] + suffix in content_set
    ]
    tracked_refs, generated_refs = extract_registration_refs(case, content_set)
    runners = [path for path in tracked_refs if PurePosixPath(path).name in {"run_test.sh", "test.sh"}]
    wrappers = [path for path in tracked_refs if path not in runners]
    if case["kind"] in {"directory", "lake-directory"}:
        case_local = [path for path in content_paths if within_scope(path, case["support_scope"])]
        shared = []
    else:
        case_local = []
        explicit = set(primary + sidecars + hooks + tracked_refs)
        shared = [
            path
            for path in content_paths
            if within_scope(path, case["support_scope"]) and path not in explicit
        ]
    return {
        "primary": primary,
        "sidecars": sidecars,
        "hooks": hooks,
        "case_local": case_local,
        "runners": runners,
        "wrappers": wrappers,
        "generated_references": generated_refs,
        "shared": shared,
    }


def derive_roles(
    u2: dict[str, Any], content_paths: list[str]
) -> tuple[dict[str, list[str]], list[dict[str, Any]]]:
    roles: dict[str, set[str]] = defaultdict(set)
    projections: list[dict[str, Any]] = []
    for case in u2["cases"]:
        projection = derive_case_files(case, content_paths)
        projections.append(projection)
        for path in projection["primary"]:
            roles[path].add("primary")
        for path in projection["sidecars"]:
            roles[path].add("sidecar")
        for path in projection["hooks"]:
            roles[path].add("case-hook")
        for path in projection["case_local"]:
            roles[path].add("case-local-support")
        for path in projection["runners"]:
            roles[path].add("family-runner")
        for path in projection["shared"]:
            roles[path].add("shared-support")
        if projection["generated_references"]:
            for path in ("tests/CMakeLists.txt", "tests/with_env.sh.in", "tests/env.sh.in"):
                if path in set(content_paths):
                    roles[path].add("registration-wrapper-template")
    result: dict[str, list[str]] = {}
    for path in content_paths:
        observed = roles.get(path, set()) or {"unreferenced-content"}
        result[path] = [role for role in ROLE_ORDER if role in observed]
    return result, projections


def build_file_rows(
    u2: dict[str, Any], blobs: dict[str, bytes], roles: dict[str, list[str]]
) -> list[dict[str, Any]]:
    rows = []
    for source in u2["content_files"]:
        path = source["path"]
        media, state, hits = scan_content(path, source["mode"], blobs[path])
        rows.append(
            seal(
                {
                    "path": path,
                    "mode": source["mode"],
                    "git_blob": source["git_blob"],
                    "bytes": source["bytes"],
                    "sha256": source["sha256"],
                    "media_class": media,
                    "decoder_state": state,
                    "roles": roles[path],
                    "signal_hits_sha256": domain_digest(
                        "axeyum-lean-u2-native-content-file-hits-v1", hits
                    ),
                    "signal_hits": hits,
                },
                FILE_DOMAIN,
            )
        )
    return rows


def build_scope_rows(
    u2: dict[str, Any], file_rows: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    by_path = {row["path"]: row for row in file_rows}
    scopes = sorted({case["support_scope"] for case in u2["cases"]})
    rows = []
    for scope in scopes:
        files = [row for row in file_rows if within_scope(row["path"], scope)]
        signal_counts: Counter[str] = Counter()
        for row in files:
            signal_counts.update(hit["signal_id"] for hit in row["signal_hits"])
        rows.append(
            seal(
                {
                    "support_scope": scope,
                    "file_count": len(files),
                    "file_records_sha256": domain_digest(
                        "axeyum-lean-u2-native-content-scope-files-v1",
                        [by_path[row["path"]]["record_sha256"] for row in files],
                    ),
                    "media_counts": dict(sorted(Counter(row["media_class"] for row in files).items())),
                    "signal_hit_counts": dict(sorted(signal_counts.items())),
                },
                SCOPE_DOMAIN,
            )
        )
    return rows


def ordered_surfaces(values: Iterable[str], m0: dict[str, Any]) -> list[str]:
    present = set(values)
    return [row["id"] for row in m0["surface_registry"] if row["id"] in present]


def build_case_rows(
    u2: dict[str, Any],
    m0: dict[str, Any],
    m0_validator: ModuleType,
    file_rows: list[dict[str, Any]],
    scope_rows: list[dict[str, Any]],
    projections: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    by_path = {row["path"]: row for row in file_rows}
    scope_by_name = {row["support_scope"]: row for row in scope_rows}
    rows = []
    for case, m0_row, projection in zip(u2["cases"], m0["case_rows"], projections, strict=True):
        promotable_paths = set(projection["primary"] + projection["hooks"] + projection["case_local"])
        evidence = []
        evidenced_path_signals: set[tuple[str, str]] = set()
        candidate_hits = 0
        exact_signal_ids: set[str] = set()
        applicable_signal_ids: set[str] = set()
        for path in sorted(promotable_paths):
            file_row = by_path[path]
            applicable_signal_ids.update(
                signal["id"] for signal in SIGNALS if file_row["media_class"] in signal["media_classes"]
            )
            for hit_index, hit in enumerate(file_row["signal_hits"]):
                if hit["disposition"] == "promote":
                    exact_signal_ids.add(hit["signal_id"])
                    evidence_key = (path, hit["signal_id"])
                    if evidence_key not in evidenced_path_signals:
                        evidenced_path_signals.add(evidence_key)
                        evidence.append(
                            {
                                "path": path,
                                "file_sha256": file_row["sha256"],
                                "signal_id": hit["signal_id"],
                                "hit_index": hit_index,
                                "surface_effect": hit["surface_effect"],
                            }
                        )
                else:
                    candidate_hits += 1
        evidence.sort(key=lambda row: (row["path"], row["signal_id"], row["hit_index"]))
        observed_surfaces = ordered_surfaces(
            (surface for item in evidence for surface in item["surface_effect"]), m0
        )
        direct = ordered_surfaces(m0_row["direct_surfaces"] + observed_surfaces, m0)
        closure = m0_validator.surface_closure(
            direct,
            [
                {key: value for key, value in item.items() if key != "record_sha256"}
                for item in m0["surface_registry"]
            ],
        )
        generated_residuals = (
            ["generated-wrapper-not-materialized"]
            if projection["generated_references"]
            else []
        )
        scope = scope_by_name[case["support_scope"]]
        rows.append(
            seal(
                {
                    "case_id": case["id"],
                    "source_case_sha256": case["sha256"],
                    "m0_case_sha256": m0_row["record_sha256"],
                    "family": case["family"],
                    "kind": case["kind"],
                    "profiles": case["profiles"],
                    "support_scope": case["support_scope"],
                    "files": {
                        "primary": projection["primary"],
                        "sidecars": projection["sidecars"],
                        "hooks": projection["hooks"],
                        "case_local": projection["case_local"],
                        "tracked_runners": projection["runners"],
                        "tracked_wrappers": projection["wrappers"],
                        "generated_references": projection["generated_references"],
                        "shared_scope_file_count": len(projection["shared"]),
                        "shared_scope_record_sha256": scope["record_sha256"],
                    },
                    "m0_direct_surfaces": m0_row["direct_surfaces"],
                    "m0_surface_closure": m0_row["surface_closure"],
                    "content_observed_surfaces": observed_surfaces,
                    "direct_surfaces": direct,
                    "surface_closure": closure,
                    "exact_signal_ids": sorted(exact_signal_ids),
                    "signal_evidence_sha256": domain_digest(
                        "axeyum-lean-u2-native-content-case-evidence-v1", evidence
                    ),
                    "signal_evidence": evidence,
                    "candidate_hit_count": candidate_hits,
                    "no_signal_observed": sorted(applicable_signal_ids - exact_signal_ids),
                    "generated_residuals": generated_residuals,
                    "classification_state": "content-census-provisional",
                    "content_refinement": "complete-census",
                    "module_dependency_closure": "not-run",
                    "native_outcome": "not-run",
                    "execution_credit": 0,
                    "pairing_credit": 0,
                },
                CASE_DOMAIN,
            )
        )
    return rows


def validate_pinned_controls(file_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_path = {row["path"]: row for row in file_rows}
    results = []
    for path, expected in PINNED_POSITIVE_CONTROLS.items():
        observed = sorted({hit["signal_id"] for hit in by_path[path]["signal_hits"]})
        missing = sorted(set(expected) - set(observed))
        if missing:
            raise ContentError(f"pinned positive control missed {path}: {', '.join(missing)}")
        results.append({"path": path, "expected_signal_ids": expected, "observed": True})
    return results


def build_authority(source_root: Path) -> dict[str, Any]:
    u2, m0, m0_validator = validate_frozen_inputs()
    blobs = verify_source_root(source_root, u2)
    content_paths = [row["path"] for row in u2["content_files"]]
    roles, projections = derive_roles(u2, content_paths)
    file_rows = build_file_rows(u2, blobs, roles)
    scope_rows = build_scope_rows(u2, file_rows)
    case_rows = build_case_rows(u2, m0, m0_validator, file_rows, scope_rows, projections)
    signal_registry = [seal(item, SIGNAL_DOMAIN) for item in SIGNALS]
    controls = validate_pinned_controls(file_rows)
    authority: dict[str, Any] = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "complete-tracked-content-census-dependency-closure-not-run",
        "scope": "full-u2-pinned-content-surface-refinement-not-support-or-parity",
        "target": u2["target"],
        "policy": {
            "tracked_content_files_required": 7004,
            "registration_cases_required": 3723,
            "shared_scope_non_promoting": True,
            "candidate_signal_non_promoting": True,
            "m0_floor_removal_forbidden": True,
            "generated_wrapper_materialized": False,
            "module_dependencies_derived": False,
            "native_execution_observed": False,
            "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
            "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
        },
        "source_authorities": [
            {"path": relative, "physical_sha256": digest}
            for relative, digest in SOURCE_HASHES.items()
        ],
        "validator_sources": [
            {"path": relative, "sha256": digest}
            for relative, digest in VALIDATOR_HASHES.items()
        ],
        "implementation_sources": [
            {
                "path": GENERATOR_PATH.relative_to(ROOT).as_posix(),
                "sha256": sha256_file(GENERATOR_PATH),
            },
            {
                "path": TEST_PATH.relative_to(ROOT).as_posix(),
                "sha256": sha256_file(TEST_PATH),
            },
        ],
        "parent_logical_seals": {
            "content_files_sha256": u2["content_files_sha256"],
            "cases_sha256": u2["cases_sha256"],
            "m0_case_rows_sha256": m0["case_rows_sha256"],
            "m0_surface_registry_sha256": m0["surface_registry_sha256"],
        },
        "signal_registry_sha256": domain_digest(
            "axeyum-lean-u2-native-content-signal-registry-v1", signal_registry
        ),
        "signal_registry": signal_registry,
        "pinned_positive_controls": controls,
        "file_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-content-files-v1", file_rows
        ),
        "file_rows": file_rows,
        "scope_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-content-scopes-v1", scope_rows
        ),
        "scope_rows": scope_rows,
        "case_rows_sha256": domain_digest(
            "axeyum-lean-u2-native-content-cases-v1", case_rows
        ),
        "case_rows": case_rows,
        "summary": authority_summary(file_rows, scope_rows, case_rows),
        "claims": CLAIMS,
        "credits": ZERO_CREDITS,
        "residual": RESIDUAL,
        "record_sha256": "",
    }
    authority["record_sha256"] = domain_digest(
        SCHEMA, {key: value for key, value in authority.items() if key != "record_sha256"}
    )
    return authority


def _list_counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for row in rows:
        counts.update(row[field])
    return dict(sorted(counts.items()))


def authority_summary(
    file_rows: list[dict[str, Any]],
    scope_rows: list[dict[str, Any]],
    case_rows: list[dict[str, Any]],
) -> dict[str, Any]:
    hit_counts: Counter[str] = Counter()
    for row in file_rows:
        hit_counts.update(hit["signal_id"] for hit in row["signal_hits"])
    return {
        "tracked_content_files": len(file_rows),
        "registration_cases": len(case_rows),
        "support_scopes": len(scope_rows),
        "media_counts": dict(sorted(Counter(row["media_class"] for row in file_rows).items())),
        "decoder_state_counts": dict(sorted(Counter(row["decoder_state"] for row in file_rows).items())),
        "role_file_counts": {
            role: sum(role in row["roles"] for row in file_rows) for role in ROLE_ORDER
        },
        "signal_hit_counts": dict(sorted(hit_counts.items())),
        "signal_hits": sum(hit_counts.values()),
        "cases_with_content_added_surface": sum(bool(row["content_observed_surfaces"]) for row in case_rows),
        "cases_with_generated_wrapper_residual": sum(bool(row["generated_residuals"]) for row in case_rows),
        "classification_state_counts": dict(sorted(Counter(row["classification_state"] for row in case_rows).items())),
        "content_refinement_counts": dict(sorted(Counter(row["content_refinement"] for row in case_rows).items())),
        "module_dependency_closure_counts": dict(sorted(Counter(row["module_dependency_closure"] for row in case_rows).items())),
        "native_outcome_counts": dict(sorted(Counter(row["native_outcome"] for row in case_rows).items())),
        "direct_surface_counts": _list_counts(case_rows, "direct_surfaces"),
        "closure_surface_counts": _list_counts(case_rows, "surface_closure"),
    }


def validate_record_seal(record: Any, domain: str, label: str, failures: list[str]) -> None:
    if not isinstance(record, dict):
        failures.append(f"{label} must be an object")
        return
    expected = domain_digest(domain, {key: value for key, value in record.items() if key != "record_sha256"})
    if record.get("record_sha256") != expected:
        failures.append(f"{label} record seal drift")


def validate_authority(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    try:
        u2, m0, m0_validator = validate_frozen_inputs()
    except ContentError as error:
        return [str(error)]
    expected_registry = [seal(item, SIGNAL_DOMAIN) for item in SIGNALS]
    fixed = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "complete-tracked-content-census-dependency-closure-not-run",
        "scope": "full-u2-pinned-content-surface-refinement-not-support-or-parity",
        "target": u2["target"],
        "claims": CLAIMS,
        "credits": ZERO_CREDITS,
        "residual": RESIDUAL,
    }
    for key, expected in fixed.items():
        if data.get(key) != expected:
            failures.append(f"{key} drift")
    expected_policy = {
        "tracked_content_files_required": 7004,
        "registration_cases_required": 3723,
        "shared_scope_non_promoting": True,
        "candidate_signal_non_promoting": True,
        "m0_floor_removal_forbidden": True,
        "generated_wrapper_materialized": False,
        "module_dependencies_derived": False,
        "native_execution_observed": False,
        "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
        "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
    }
    if data.get("policy") != expected_policy:
        failures.append("policy drift")
    expected_sources = [
        {"path": relative, "physical_sha256": digest}
        for relative, digest in SOURCE_HASHES.items()
    ]
    expected_validators = [
        {"path": relative, "sha256": digest}
        for relative, digest in VALIDATOR_HASHES.items()
    ]
    if data.get("source_authorities") != expected_sources:
        failures.append("source authorities drift")
    if data.get("validator_sources") != expected_validators:
        failures.append("validator sources drift")
    expected_implementation_sources = [
        {
            "path": path.relative_to(ROOT).as_posix(),
            "sha256": sha256_file(path),
        }
        for path in (GENERATOR_PATH, TEST_PATH)
    ]
    if data.get("implementation_sources") != expected_implementation_sources:
        failures.append("implementation sources drift")
    expected_parent_seals = {
        "content_files_sha256": u2["content_files_sha256"],
        "cases_sha256": u2["cases_sha256"],
        "m0_case_rows_sha256": m0["case_rows_sha256"],
        "m0_surface_registry_sha256": m0["surface_registry_sha256"],
    }
    if data.get("parent_logical_seals") != expected_parent_seals:
        failures.append("parent logical seals drift")
    if data.get("signal_registry") != expected_registry:
        failures.append("signal registry semantic or order drift")
    if data.get("signal_registry_sha256") != domain_digest(
        "axeyum-lean-u2-native-content-signal-registry-v1", data.get("signal_registry")
    ):
        failures.append("signal registry list seal drift")
    if data.get("pinned_positive_controls") != [
        {"path": path, "expected_signal_ids": expected, "observed": True}
        for path, expected in PINNED_POSITIVE_CONTROLS.items()
    ]:
        failures.append("pinned positive controls drift")

    parent_files = u2["content_files"]
    file_rows = data.get("file_rows")
    if not isinstance(file_rows, list):
        failures.append("file rows must be a list")
        file_rows = []
    if len(file_rows) != len(parent_files):
        failures.append(f"file row count drift: {len(file_rows)} != {len(parent_files)}")
    signal_by_id = {row["id"]: row for row in SIGNALS}
    hits_by_path: dict[str, list[dict[str, Any]]] = {}
    for index, (row, parent) in enumerate(zip(file_rows, parent_files, strict=False)):
        label = f"file row {index} ({parent['path']})"
        if not isinstance(row, dict):
            failures.append(f"{label} must be an object")
            continue
        for field in ("path", "mode", "git_blob", "bytes", "sha256"):
            if row.get(field) != parent[field]:
                failures.append(f"{label} parent identity drift")
                break
        if row.get("roles") != [role for role in ROLE_ORDER if role in set(row.get("roles", []))]:
            failures.append(f"{label} role order or identity drift")
        hits = row.get("signal_hits")
        if not isinstance(hits, list):
            failures.append(f"{label} signal hits must be a list")
            hits = []
        previous: tuple[int, int, str] | None = None
        for hit_index, hit in enumerate(hits):
            hit_label = f"{label} hit {hit_index}"
            if not isinstance(hit, dict):
                failures.append(f"{hit_label} must be an object")
                continue
            signal = signal_by_id.get(hit.get("signal_id"))
            if signal is None:
                failures.append(f"{hit_label} unknown signal")
                continue
            for field in ("signal_version", "confidence", "disposition", "surface_effect"):
                expected = signal["version"] if field == "signal_version" else signal[field]
                if hit.get(field) != expected:
                    failures.append(f"{hit_label} signal semantic drift")
            start, end = hit.get("byte_start"), hit.get("byte_end")
            if not isinstance(start, int) or not isinstance(end, int) or not (0 <= start < end <= parent["bytes"]):
                failures.append(f"{hit_label} byte interval invalid")
            order = (start if isinstance(start, int) else -1, end if isinstance(end, int) else -1, str(hit.get("signal_id")))
            if previous is not None and order < previous:
                failures.append(f"{label} hit order drift")
            previous = order
            if "record_sha256" in hit:
                failures.append(f"{hit_label} redundant per-hit seal present")
        if row.get("signal_hits_sha256") != domain_digest(
            "axeyum-lean-u2-native-content-file-hits-v1", hits
        ):
            failures.append(f"{label} hit list seal drift")
        validate_record_seal(row, FILE_DOMAIN, label, failures)
        hits_by_path[parent["path"]] = hits
    if data.get("file_rows_sha256") != domain_digest(
        "axeyum-lean-u2-native-content-files-v1", file_rows
    ):
        failures.append("file row list seal drift")

    content_paths = [row["path"] for row in parent_files]
    expected_roles, projections = derive_roles(u2, content_paths)
    file_by_path = {item.get("path"): item for item in file_rows if isinstance(item, dict)}
    for row in file_rows:
        if isinstance(row, dict) and row.get("path") in expected_roles and row.get("roles") != expected_roles[row["path"]]:
            failures.append(f"file {row.get('path')}: role projection drift")

    scope_rows = data.get("scope_rows")
    if not isinstance(scope_rows, list):
        failures.append("scope rows must be a list")
        scope_rows = []
    for index, row in enumerate(scope_rows):
        validate_record_seal(row, SCOPE_DOMAIN, f"scope row {index}", failures)
    if data.get("scope_rows_sha256") != domain_digest(
        "axeyum-lean-u2-native-content-scopes-v1", scope_rows
    ):
        failures.append("scope row list seal drift")
    expected_scope_rows = build_scope_rows(u2, file_rows)
    if scope_rows != expected_scope_rows:
        failures.append("support scope semantic or aggregate drift")
    expected_scopes = sorted({case["support_scope"] for case in u2["cases"]})
    if [row.get("support_scope") for row in scope_rows if isinstance(row, dict)] != expected_scopes:
        failures.append("support scope population or order drift")
    scope_by_name = {row.get("support_scope"): row for row in scope_rows if isinstance(row, dict)}

    case_rows = data.get("case_rows")
    if not isinstance(case_rows, list):
        failures.append("case rows must be a list")
        case_rows = []
    if len(case_rows) != len(m0["case_rows"]):
        failures.append(f"case row count drift: {len(case_rows)} != {len(m0['case_rows'])}")
    for index, (row, case, m0_row, projection) in enumerate(
        zip(case_rows, u2["cases"], m0["case_rows"], projections, strict=False)
    ):
        label = f"case row {index} ({case['id']})"
        if not isinstance(row, dict):
            failures.append(f"{label} must be an object")
            continue
        identities = {
            "case_id": case["id"],
            "source_case_sha256": case["sha256"],
            "m0_case_sha256": m0_row["record_sha256"],
            "family": case["family"],
            "kind": case["kind"],
            "profiles": case["profiles"],
            "support_scope": case["support_scope"],
        }
        if any(row.get(key) != value for key, value in identities.items()):
            failures.append(f"{label} parent identity drift")
        expected_files = {
            "primary": projection["primary"],
            "sidecars": projection["sidecars"],
            "hooks": projection["hooks"],
            "case_local": projection["case_local"],
            "tracked_runners": projection["runners"],
            "tracked_wrappers": projection["wrappers"],
            "generated_references": projection["generated_references"],
            "shared_scope_file_count": len(projection["shared"]),
            "shared_scope_record_sha256": scope_by_name.get(case["support_scope"], {}).get("record_sha256"),
        }
        if row.get("files") != expected_files:
            failures.append(f"{label} file-role projection drift")
        evidence = row.get("signal_evidence")
        if not isinstance(evidence, list):
            failures.append(f"{label} evidence must be a list")
            evidence = []
        evidence_surfaces: list[str] = []
        exact_signal_ids: set[str] = set()
        promotable_paths = set(projection["primary"] + projection["hooks"] + projection["case_local"])
        for evidence_row in evidence:
            if not isinstance(evidence_row, dict):
                failures.append(f"{label} evidence row must be an object")
                continue
            path = evidence_row.get("path")
            if path not in promotable_paths:
                failures.append(f"{label} shared/sidecar/runner evidence promoted")
            hit_index = evidence_row.get("hit_index")
            path_hits = hits_by_path.get(path, [])
            hit = (
                path_hits[hit_index]
                if isinstance(hit_index, int) and 0 <= hit_index < len(path_hits)
                else None
            )
            if hit is None or hit.get("disposition") != "promote":
                failures.append(f"{label} out-of-range, unresolved, or non-promoting evidence index")
                continue
            if evidence_row.get("signal_id") != hit["signal_id"] or evidence_row.get("surface_effect") != hit["surface_effect"]:
                failures.append(f"{label} evidence semantic drift")
            file_row = file_by_path.get(path)
            if file_row is None or evidence_row.get("file_sha256") != file_row.get("sha256"):
                failures.append(f"{label} evidence file identity drift")
            exact_signal_ids.add(hit["signal_id"])
            evidence_surfaces.extend(hit["surface_effect"])
        if row.get("signal_evidence_sha256") != domain_digest(
            "axeyum-lean-u2-native-content-case-evidence-v1", evidence
        ):
            failures.append(f"{label} evidence list seal drift")
        observed = ordered_surfaces(evidence_surfaces, m0)
        if row.get("content_observed_surfaces") != observed:
            failures.append(f"{label} content-observed surface drift")
        if row.get("exact_signal_ids") != sorted(exact_signal_ids):
            failures.append(f"{label} exact signal set drift")
        applicable_signal_ids: set[str] = set()
        candidate_hit_count = 0
        for path in promotable_paths:
            file_row = file_by_path.get(path)
            if file_row is None:
                continue
            applicable_signal_ids.update(
                signal["id"]
                for signal in SIGNALS
                if file_row.get("media_class") in signal["media_classes"]
            )
            candidate_hit_count += sum(
                hit.get("disposition") == "candidate-only"
                for hit in file_row.get("signal_hits", [])
            )
        if row.get("candidate_hit_count") != candidate_hit_count:
            failures.append(f"{label} candidate hit count drift")
        if row.get("no_signal_observed") != sorted(applicable_signal_ids - exact_signal_ids):
            failures.append(f"{label} no-signal accounting drift")
        direct = ordered_surfaces(m0_row["direct_surfaces"] + observed, m0)
        if row.get("m0_direct_surfaces") != m0_row["direct_surfaces"] or row.get("direct_surfaces") != direct:
            failures.append(f"{label} M0 floor or direct surface drift")
        expected_closure = m0_validator.surface_closure(
            direct,
            [{key: value for key, value in item.items() if key != "record_sha256"} for item in m0["surface_registry"]],
        )
        if row.get("m0_surface_closure") != m0_row["surface_closure"] or row.get("surface_closure") != expected_closure:
            failures.append(f"{label} surface closure drift")
        expected_generated = ["generated-wrapper-not-materialized"] if projection["generated_references"] else []
        if row.get("generated_residuals") != expected_generated:
            failures.append(f"{label} generated-wrapper residual drift")
        noncredit = {
            "classification_state": "content-census-provisional",
            "content_refinement": "complete-census",
            "module_dependency_closure": "not-run",
            "native_outcome": "not-run",
            "execution_credit": 0,
            "pairing_credit": 0,
        }
        if any(row.get(key) != value for key, value in noncredit.items()):
            failures.append(f"{label} non-crediting state drift")
        validate_record_seal(row, CASE_DOMAIN, label, failures)
    if data.get("case_rows_sha256") != domain_digest(
        "axeyum-lean-u2-native-content-cases-v1", case_rows
    ):
        failures.append("case row list seal drift")

    if data.get("summary") != authority_summary(file_rows, scope_rows, case_rows):
        failures.append("summary drift")

    if data.get("record_sha256") != domain_digest(
        SCHEMA, {key: value for key, value in data.items() if key != "record_sha256"}
    ):
        failures.append("top-level record seal drift")
    return failures


def summarize(data: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "as_of": data["as_of"],
        "target": data["target"],
        "verdict": "all tracked U2 content has a provisional signal census; TL0.6.4 and Lean parity remain incomplete",
        "summary": data["summary"],
        "claims": data["claims"],
        "credits": data["credits"],
        "residual": data["residual"],
        "authority_record_sha256": data["record_sha256"],
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Generated Lean U2 native-surface content census",
        "",
        "> Generated by `scripts/gen-lean-u2-native-surface-content.py`; do not edit by hand.",
        "",
        f"- Verdict: **{report['verdict']}**.",
        f"- Tracked files inspected: **{summary['tracked_content_files']:,}**.",
        f"- Registered cases projected: **{summary['registration_cases']:,}**.",
        f"- Exact/candidate signal hits: **{summary['signal_hits']:,}**.",
        f"- Cases with a content-observed surface: **{summary['cases_with_content_added_surface']:,}**.",
        f"- Cases retaining the generated-wrapper residual: **{summary['cases_with_generated_wrapper_residual']:,}**.",
        "- Native outcomes and paired cells: **0 / 0**.",
        "",
        "## Media denominator",
        "",
        "| Media class | Files |",
        "|---|---:|",
    ]
    for name, count in summary["media_counts"].items():
        lines.append(f"| `{name}` | {count:,} |")
    lines.extend(["", "## Signal denominator", "", "| Signal | Hits |", "|---|---:|"])
    for name, count in summary["signal_hit_counts"].items():
        lines.append(f"| `{name}` | {count:,} |")
    lines.extend(["", "## Refined surface denominator", "", "| Surface | Direct cases | Closure cases |", "|---|---:|---:|"])
    surfaces = sorted(set(summary["direct_surface_counts"]) | set(summary["closure_surface_counts"]))
    for surface in surfaces:
        lines.append(
            f"| `{surface}` | {summary['direct_surface_counts'].get(surface, 0):,} | {summary['closure_surface_counts'].get(surface, 0):,} |"
        )
    lines.extend(
        [
            "",
            "## Non-crediting boundary",
            "",
            "Every case remains `content-census-provisional`; exact module/generated/runtime/FFI/request/project dependency closure and every native outcome remain `not-run`. Lexical or structured content evidence is not native support, execution, or semantic agreement.",
            "",
            "## Required continuation",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["residual"])
    return "\n".join(lines) + "\n"


def write_outputs(authority: dict[str, Any]) -> None:
    MANIFEST.write_bytes(canonical_bytes(authority) + b"\n")
    # Reload the canonical sorted-key representation so generated report order
    # is identical during derivation and offline --check.
    report = summarize(load_json(MANIFEST))
    OUT_JSON.write_text(json_text(report), encoding="utf-8")
    OUT_MD.write_text(render_markdown(report), encoding="utf-8")


def check_outputs(source_root: Path | None) -> None:
    if not MANIFEST.is_file():
        raise ContentError(f"missing committed authority: {MANIFEST.relative_to(ROOT)}")
    data = load_json(MANIFEST)
    failures = validate_authority(data)
    if failures:
        raise ContentError("invalid committed M1 authority: " + "; ".join(failures))
    if source_root is not None:
        reproduced = build_authority(source_root)
        if reproduced != data:
            raise ContentError("pinned-source reproduction differs from committed authority")
    report = summarize(data)
    expected_json = json_text(report)
    expected_md = render_markdown(report)
    if not OUT_JSON.is_file() or OUT_JSON.read_text(encoding="utf-8") != expected_json:
        raise ContentError(f"stale generated report: {OUT_JSON.relative_to(ROOT)}")
    if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != expected_md:
        raise ContentError(f"stale generated report: {OUT_MD.relative_to(ROOT)}")
    print(
        "LEAN_U2_NATIVE_CONTENT|"
        f"files={data['summary']['tracked_content_files']}|"
        f"cases={data['summary']['registration_cases']}|"
        f"hits={data['summary']['signal_hits']}|"
        f"generated_residual={data['summary']['cases_with_generated_wrapper_residual']}|"
        "dependency_closed=0|native_outcomes=0|paired=0|parity=0"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, help="exact pinned Lean checkout for derivation/reproduction")
    parser.add_argument("--check", action="store_true", help="validate committed authority and generated reports")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        if args.check:
            check_outputs(args.source_root)
        else:
            if args.source_root is None:
                raise ContentError("derivation requires --source-root")
            authority = build_authority(args.source_root)
            write_outputs(authority)
            print(
                f"lean-u2-native-content: wrote {authority['summary']['tracked_content_files']} files / "
                f"{authority['summary']['registration_cases']} cases; dependency/native/pair/parity credit zero"
            )
    except ContentError as error:
        print(f"lean-u2-native-content: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
