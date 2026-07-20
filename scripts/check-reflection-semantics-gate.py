#!/usr/bin/env python3
"""Validate the source-owned reflection semantics evidence manifest."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


SCHEMA = "axeyum.reflection-semantics-gate.v1"
REPORT_SCHEMA = "axeyum.reflection-semantics-gate-validation.v1"
DEFAULT_MANIFEST = Path("docs/consumer-track/verify/reflection-semantics-gate.json")
EXPECTED_TEST_BINARIES = [
    "reflection_semantics_gate",
    "cross_ir_equivalence",
    "cross_ir_refutation",
    "llvm_checked_cfg",
    "llvm_checked_memory",
    "mir_checked_memory",
    "checked_bounds",
    "llvm_checked_loop",
    "llvm_direct_calls",
]
CHECKER_TEST_MODULE = "scripts/tests/test_check_reflection_semantics_gate.py"
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


class GateError(ValueError):
    """A stable validation failure."""


def require_object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise GateError(f"{where}: expected object")
    return value


def require_list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise GateError(f"{where}: expected array")
    return value


def require_string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise GateError(f"{where}: expected nonempty string")
    return value


def require_exact_keys(value: dict[str, Any], expected: set[str], where: str) -> None:
    actual = set(value)
    if actual != expected:
        raise GateError(
            f"{where}: fields differ: missing={sorted(expected - actual)} "
            f"unexpected={sorted(actual - expected)}"
        )


def safe_path(root: Path, raw: str, where: str) -> Path:
    relative = Path(require_string(raw, where))
    if relative.is_absolute() or ".." in relative.parts:
        raise GateError(f"{where}: path must be repository-relative without `..`")
    resolved = (root / relative).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise GateError(f"{where}: path escapes repository root") from error
    if not resolved.is_file():
        raise GateError(f"{where}: file does not exist: {relative.as_posix()}")
    return resolved


def skip_line_comment(text: str, index: int) -> int:
    newline = text.find("\n", index + 2)
    return len(text) if newline < 0 else newline + 1


def skip_block_comment(text: str, index: int) -> int:
    depth = 1
    cursor = index + 2
    while cursor < len(text) and depth:
        if text.startswith("/*", cursor):
            depth += 1
            cursor += 2
        elif text.startswith("*/", cursor):
            depth -= 1
            cursor += 2
        else:
            cursor += 1
    if depth:
        raise GateError("unterminated Rust block comment while reading enum")
    return cursor


def skip_quoted(text: str, index: int, quote: str) -> int:
    cursor = index + 1
    while cursor < len(text):
        if text[cursor] == "\\":
            cursor += 2
        elif text[cursor] == quote:
            return cursor + 1
        else:
            cursor += 1
    raise GateError("unterminated Rust literal while reading enum")


def skip_space_and_comments(text: str, index: int) -> int:
    cursor = index
    while cursor < len(text):
        if text[cursor].isspace():
            cursor += 1
        elif text.startswith("//", cursor):
            cursor = skip_line_comment(text, cursor)
        elif text.startswith("/*", cursor):
            cursor = skip_block_comment(text, cursor)
        else:
            break
    return cursor


def find_opening_brace(text: str, index: int) -> int:
    cursor = index
    while cursor < len(text):
        if text.startswith("//", cursor):
            cursor = skip_line_comment(text, cursor)
        elif text.startswith("/*", cursor):
            cursor = skip_block_comment(text, cursor)
        elif text[cursor] in {'"', "'"}:
            cursor = skip_quoted(text, cursor, text[cursor])
        elif text[cursor] == "{":
            return cursor
        elif text[cursor] == ";":
            break
        else:
            cursor += 1
    raise GateError("enum declaration has no body")


def skip_attribute(text: str, index: int) -> int:
    if not text.startswith("#[", index):
        return index
    depth = 1
    cursor = index + 2
    while cursor < len(text) and depth:
        if text.startswith("//", cursor):
            cursor = skip_line_comment(text, cursor)
        elif text.startswith("/*", cursor):
            cursor = skip_block_comment(text, cursor)
        elif text[cursor] in {'"', "'"}:
            cursor = skip_quoted(text, cursor, text[cursor])
        elif text[cursor] == "[":
            depth += 1
            cursor += 1
        elif text[cursor] == "]":
            depth -= 1
            cursor += 1
        else:
            cursor += 1
    if depth:
        raise GateError("unterminated Rust attribute while reading enum")
    return cursor


def enum_variants(source: str, enum_name: str, where: str) -> list[str]:
    declaration = re.compile(rf"\benum\s+{re.escape(enum_name)}\b").search(source)
    if declaration is None:
        raise GateError(f"{where}: enum `{enum_name}` not found")
    cursor = find_opening_brace(source, declaration.end()) + 1
    variants: list[str] = []
    closing = {"(": ")", "[": "]", "{": "}", "<": ">"}

    while True:
        cursor = skip_space_and_comments(source, cursor)
        while source.startswith("#[", cursor):
            cursor = skip_space_and_comments(source, skip_attribute(source, cursor))
        if cursor >= len(source):
            raise GateError(f"{where}: enum `{enum_name}` has no closing brace")
        if source[cursor] == "}":
            break
        match = IDENTIFIER.match(source, cursor)
        if match is None:
            raise GateError(
                f"{where}: expected named variant in `{enum_name}` at byte {cursor}"
            )
        variant = match.group(0)
        if variant in variants:
            raise GateError(f"{where}: duplicate variant `{variant}` in `{enum_name}`")
        variants.append(variant)
        cursor = match.end()
        stack: list[str] = []
        while cursor < len(source):
            if source.startswith("//", cursor):
                cursor = skip_line_comment(source, cursor)
            elif source.startswith("/*", cursor):
                cursor = skip_block_comment(source, cursor)
            elif source[cursor] in {'"', "'"}:
                cursor = skip_quoted(source, cursor, source[cursor])
            elif source[cursor] in closing:
                stack.append(closing[source[cursor]])
                cursor += 1
            elif stack and source[cursor] == stack[-1]:
                stack.pop()
                cursor += 1
            elif not stack and source[cursor] == ",":
                cursor += 1
                break
            elif not stack and source[cursor] == "}":
                break
            else:
                cursor += 1
        else:
            raise GateError(f"{where}: enum `{enum_name}` has no closing brace")
    if not variants:
        raise GateError(f"{where}: enum `{enum_name}` has no variants")
    return variants


def require_string_list(value: Any, where: str, *, nonempty: bool = True) -> list[str]:
    rows = require_list(value, where)
    result = [require_string(row, f"{where}[{index}]") for index, row in enumerate(rows)]
    if nonempty and not result:
        raise GateError(f"{where}: must not be empty")
    if len(set(result)) != len(result):
        raise GateError(f"{where}: duplicate values")
    return result


def validate_test_reference(root: Path, reference: str, where: str) -> None:
    path_text, separator, test_name = reference.rpartition("::")
    if not separator or not IDENTIFIER.fullmatch(test_name):
        raise GateError(f"{where}: expected `relative/path.rs::test_name`")
    path = safe_path(root, path_text, where)
    source = path.read_text(encoding="utf-8")
    pattern = re.compile(
        rf"(?m)^[ \t]*#\[[ \t]*test[ \t]*\][ \t]*\r?\n"
        rf"(?:[ \t]*#\[(?![ \t]*ignore\b)[^\]\n]+\][ \t]*\r?\n)*"
        rf"[ \t]*fn[ \t]+{re.escape(test_name)}[ \t]*\("
    )
    if pattern.search(source) is None:
        raise GateError(f"{where}: active `#[test] fn {test_name}` not found in {path_text}")


def validate(root: Path, manifest_path: Path) -> dict[str, Any]:
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise GateError(f"manifest: cannot decode JSON: {error}") from error
    manifest = require_object(manifest, "manifest")
    require_exact_keys(
        manifest,
        {"schema", "surfaces", "evidence_groups", "test_binaries"},
        "manifest",
    )
    if manifest["schema"] != SCHEMA:
        raise GateError(f"manifest.schema: expected `{SCHEMA}`")

    surfaces = require_list(manifest["surfaces"], "manifest.surfaces")
    if not surfaces:
        raise GateError("manifest.surfaces: must not be empty")
    derived: set[str] = set()
    surface_ids: set[str] = set()
    for index, raw_surface in enumerate(surfaces):
        where = f"manifest.surfaces[{index}]"
        surface = require_object(raw_surface, where)
        require_exact_keys(surface, {"id", "source", "enum"}, where)
        surface_id = require_string(surface["id"], f"{where}.id")
        if surface_id in surface_ids:
            raise GateError(f"{where}.id: duplicate surface `{surface_id}`")
        surface_ids.add(surface_id)
        enum_name = require_string(surface["enum"], f"{where}.enum")
        source_path = safe_path(root, surface["source"], f"{where}.source")
        source_text = source_path.read_text(encoding="utf-8")
        for variant in enum_variants(source_text, enum_name, where):
            key = f"{surface_id}::{variant}"
            if key in derived:
                raise GateError(f"{where}: duplicate derived semantic key `{key}`")
            derived.add(key)

    groups = require_list(manifest["evidence_groups"], "manifest.evidence_groups")
    if not groups:
        raise GateError("manifest.evidence_groups: must not be empty")
    ownership: dict[str, str] = {}
    group_ids: set[str] = set()
    proof_tests: set[str] = set()
    fuzz_tests: set[str] = set()
    refutation_tests: set[str] = set()
    for index, raw_group in enumerate(groups):
        where = f"manifest.evidence_groups[{index}]"
        group = require_object(raw_group, where)
        allowed = {"id", "members", "proof_tests", "fuzz_tests", "refutation_tests"}
        actual = set(group)
        if not {"id", "members", "proof_tests", "fuzz_tests"}.issubset(actual) or not actual.issubset(allowed):
            raise GateError(f"{where}: fields differ from evidence-group schema")
        group_id = require_string(group["id"], f"{where}.id")
        if group_id in group_ids:
            raise GateError(f"{where}.id: duplicate evidence group `{group_id}`")
        group_ids.add(group_id)
        members = require_string_list(group["members"], f"{where}.members")
        for member in members:
            if member not in derived:
                raise GateError(f"{where}.members: orphan semantic key `{member}`")
            if member in ownership:
                raise GateError(
                    f"{where}.members: `{member}` already owned by `{ownership[member]}`"
                )
            ownership[member] = group_id
        for field, destination in [
            ("proof_tests", proof_tests),
            ("fuzz_tests", fuzz_tests),
            ("refutation_tests", refutation_tests),
        ]:
            references = require_string_list(
                group.get(field, []), f"{where}.{field}", nonempty=field != "refutation_tests"
            )
            for test_index, reference in enumerate(references):
                validate_test_reference(root, reference, f"{where}.{field}[{test_index}]")
                destination.add(reference)

    missing = sorted(derived - set(ownership))
    if missing:
        raise GateError(f"manifest.evidence_groups: uncovered semantic keys: {missing}")

    binaries = require_string_list(manifest["test_binaries"], "manifest.test_binaries")
    if binaries != EXPECTED_TEST_BINARIES:
        raise GateError(
            "manifest.test_binaries: command-list drift; expected "
            f"{EXPECTED_TEST_BINARIES}, got {binaries}"
        )

    return {
        "schema": REPORT_SCHEMA,
        "surfaces": len(surfaces),
        "variants": len(derived),
        "evidence_groups": len(groups),
        "proof_tests": len(proof_tests),
        "fuzz_tests": len(fuzz_tests),
        "refutation_tests": len(refutation_tests),
        "test_binaries": binaries,
        "status": "pass",
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (default: script parent)",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="manifest path relative to --root",
    )
    parser.add_argument(
        "--run",
        action="store_true",
        help="after validation, run the exact registered Cargo test binaries",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    try:
        manifest_path = safe_path(root, args.manifest.as_posix(), "--manifest")
        report = validate(root, manifest_path)
    except GateError as error:
        print(f"reflection semantics gate: {error}", file=sys.stderr)
        return 1
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    if args.run:
        checker_tests = [sys.executable, "-m", "unittest", CHECKER_TEST_MODULE]
        print("reflection semantics checker tests: " + " ".join(checker_tests), flush=True)
        checker_result = subprocess.run(checker_tests, cwd=root, check=False)
        if checker_result.returncode != 0:
            return checker_result.returncode
        command = ["cargo", "test", "-p", "axeyum-verify"]
        for binary in report["test_binaries"]:
            command.extend(["--test", binary])
        print("reflection semantics gate command: " + " ".join(command), flush=True)
        return subprocess.run(command, cwd=root, check=False).returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
