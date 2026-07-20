#!/usr/bin/env python3
"""Validate and reproducibly regenerate the registered axeyum-verify MIR fixture."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import NoReturn


SCHEMA = "axeyum.verify-mir-capture.v1"
REPO_ROOT = Path(__file__).resolve().parents[1]
CANONICAL_ROOT = (
    REPO_ROOT / "crates" / "axeyum-verify" / "tests" / "fixtures" / "mir"
)
TARGET_TMP_ROOT = REPO_ROOT / "target" / "axeyum-mir-capture"
SOURCE_NAME = "source.rs"
OUTPUT_NAME = "rustc197-debug.mir"
PROVENANCE_NAME = "provenance.json"
CHECKSUM_NAME = "SHA256SUMS"
EXPECTED_FILES = {SOURCE_NAME, OUTPUT_NAME, PROVENANCE_NAME, CHECKSUM_NAME}
HASHED_FILES = (SOURCE_NAME, OUTPUT_NAME, PROVENANCE_NAME)

REGISTERED_ARGV = [
    "--crate-name",
    "axeyum_verify_mir_capture",
    "--crate-type",
    "lib",
    "--edition",
    "2024",
    "-C",
    "opt-level=0",
    "-C",
    "overflow-checks=yes",
    "-Zunpretty=mir",
    SOURCE_NAME,
]
REGISTERED_ENVIRONMENT = {"LC_ALL": "C", "SOURCE_DATE_EPOCH": "0"}
REGISTERED_COMPILER = {
    "release": "1.97.0-nightly",
    "commit_hash": "f53b654a8882fd5fc036c4ca7a4ff41ce32497a6",
    "commit_date": "2026-04-30",
    "host": "x86_64-unknown-linux-gnu",
    "llvm_version": "22.1.4",
    "verbose_version": [
        "rustc 1.97.0-nightly (f53b654a8 2026-04-30)",
        "binary: rustc",
        "commit-hash: f53b654a8882fd5fc036c4ca7a4ff41ce32497a6",
        "commit-date: 2026-04-30",
        "host: x86_64-unknown-linux-gnu",
        "release: 1.97.0-nightly",
        "LLVM version: 22.1.4",
    ],
}
EXPECTED_TOP_LEVEL_KEYS = {
    "argv",
    "capture",
    "checksums",
    "compiler",
    "environment",
    "output",
    "schema",
    "source",
}
EXPECTED_COMPILER_KEYS = {
    "commit_date",
    "commit_hash",
    "host",
    "llvm_version",
    "release",
    "verbose_version",
}
EXPECTED_FUNCTIONS = (
    "scalar_pick",
    "checked_read",
    "clamped_read",
    "store_then_load",
)


class FixtureError(Exception):
    """A stable, externally visible fixture-check failure."""

    def __init__(self, error_class: str, message: str):
        super().__init__(message)
        self.error_class = error_class


def fail(error_class: str, message: str) -> NoReturn:
    raise FixtureError(error_class, message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def validate_relative_name(value: object, expected: str, field: str) -> str:
    if not isinstance(value, str):
        fail("manifest_type", f"{field} must be a string")
    path = Path(value)
    if path.is_absolute() or value != expected or any(part == ".." for part in path.parts):
        fail("unsafe_path", f"{field} must be exactly {expected!r}")
    return value


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            fail("duplicate_manifest_key", f"duplicate JSON object key {key!r}")
        result[key] = value
    return result


def load_manifest(root: Path) -> dict[str, object]:
    path = root / PROVENANCE_NAME
    try:
        raw = path.read_bytes()
    except OSError as exc:
        fail("missing_file", f"cannot read {PROVENANCE_NAME}: {exc}")
    try:
        value = json.loads(raw, object_pairs_hook=unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        fail("malformed_manifest", f"cannot parse {PROVENANCE_NAME}: {exc}")
    if not isinstance(value, dict):
        fail("manifest_type", "provenance root must be an object")
    if set(value) != EXPECTED_TOP_LEVEL_KEYS:
        fail("manifest_keys", "provenance top-level keys differ from the registered schema")
    if value.get("schema") != SCHEMA:
        fail("manifest_schema", f"unsupported provenance schema {value.get('schema')!r}")
    validate_relative_name(value.get("source"), SOURCE_NAME, "source")
    validate_relative_name(value.get("output"), OUTPUT_NAME, "output")
    validate_relative_name(value.get("checksums"), CHECKSUM_NAME, "checksums")
    if value.get("argv") != REGISTERED_ARGV:
        fail("unsafe_argv", "compiler argv differs from the registered non-executable template")
    if value.get("environment") != REGISTERED_ENVIRONMENT:
        fail("unsafe_environment", "capture environment differs from the registered template")
    if value.get("capture") != {
        "stderr": "diagnostic-only",
        "stdout": "raw-byte-for-byte",
    }:
        fail("capture_rule", "capture stream rules differ from the registered policy")
    compiler = value.get("compiler")
    if not isinstance(compiler, dict) or set(compiler) != EXPECTED_COMPILER_KEYS:
        fail("compiler_manifest", "compiler identity fields differ from the registered schema")
    if compiler != REGISTERED_COMPILER:
        fail("compiler_manifest", "compiler identity differs from the registered compiler")
    return value


def validate_capture_surface(raw: bytes) -> None:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        fail("capture_encoding", f"raw compiler stdout is not UTF-8: {exc}")
    functions = tuple(re.findall(r"(?m)^fn ([A-Za-z_][A-Za-z0-9_]*)\(", text))
    if functions != EXPECTED_FUNCTIONS:
        fail("capture_surface", f"captured function order differs: {functions!r}")
    write = text.find("        _1[_2] = copy _3;")
    read = text.find("        _0 = copy _1[_2];", write + 1)
    if write < 0 or read < 0:
        fail("capture_surface", "store_then_load write/read shape is absent or reordered")


def directory_names(root: Path) -> set[str]:
    try:
        entries = list(root.iterdir())
    except OSError as exc:
        fail("fixture_root", f"cannot read fixture root: {exc}")
    if any(not entry.is_file() for entry in entries):
        fail("unexpected_file", "fixture root must contain only ordinary registered files")
    return {entry.name for entry in entries}


def load_checksums(root: Path) -> dict[str, str]:
    try:
        text = (root / CHECKSUM_NAME).read_text(encoding="ascii")
    except (OSError, UnicodeDecodeError) as exc:
        fail("missing_file", f"cannot read {CHECKSUM_NAME}: {exc}")
    result: dict[str, str] = {}
    for line_number, line in enumerate(text.splitlines(), start=1):
        parts = line.split("  ")
        if len(parts) != 2:
            fail("malformed_checksums", f"{CHECKSUM_NAME}:{line_number}: expected two fields")
        digest, name = parts
        if (
            len(digest) != 64
            or digest.lower() != digest
            or any(ch not in "0123456789abcdef" for ch in digest)
        ):
            fail("invalid_sha256", f"{CHECKSUM_NAME}:{line_number}: invalid SHA-256")
        validate_relative_name(name, name, f"checksum path at line {line_number}")
        if name not in HASHED_FILES:
            fail("unexpected_checksum", f"{CHECKSUM_NAME}:{line_number}: unexpected file {name!r}")
        if name in result:
            fail("duplicate_checksum", f"{CHECKSUM_NAME}:{line_number}: duplicate file {name!r}")
        result[name] = digest
    if tuple(result) != HASHED_FILES:
        fail("checksum_set", "checksum file list or order differs from the registered set")
    return result


def verify_content(root: Path) -> dict[str, object]:
    names = directory_names(root)
    if names != EXPECTED_FILES:
        missing = sorted(EXPECTED_FILES - names)
        extra = sorted(names - EXPECTED_FILES)
        fail("unexpected_file", f"fixture files differ: missing={missing}, extra={extra}")
    checksums = load_checksums(root)
    for name in HASHED_FILES:
        try:
            actual = sha256_bytes((root / name).read_bytes())
        except OSError as exc:
            fail("missing_file", f"cannot read {name}: {exc}")
        if actual != checksums[name]:
            fail("checksum_mismatch", f"SHA-256 mismatch for {name}")
    validate_capture_surface((root / OUTPUT_NAME).read_bytes())
    return load_manifest(root)


def compiler_vv(rustc: str) -> tuple[str | None, str | None]:
    env = os.environ.copy()
    env.update(REGISTERED_ENVIRONMENT)
    try:
        run = subprocess.run(
            [rustc, "-vV"],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
    except OSError as exc:
        return None, f"compiler unavailable: {exc}"
    if run.returncode != 0:
        detail = run.stderr.decode("utf-8", errors="replace").strip()
        return None, f"compiler -vV failed with {run.returncode}: {detail}"
    try:
        return run.stdout.decode("utf-8"), None
    except UnicodeDecodeError as exc:
        return None, f"compiler -vV was not UTF-8: {exc}"


def expected_compiler_vv() -> str:
    return "\n".join(REGISTERED_COMPILER["verbose_version"]) + "\n"


def capture_once(root: Path, rustc: str) -> bytes:
    TARGET_TMP_ROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="capture-", dir=TARGET_TMP_ROOT) as tmp_name:
        tmp = Path(tmp_name)
        shutil.copyfile(root / SOURCE_NAME, tmp / SOURCE_NAME)
        env = os.environ.copy()
        env.update(REGISTERED_ENVIRONMENT)
        try:
            run = subprocess.run(
                [rustc, *REGISTERED_ARGV],
                cwd=tmp,
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                env=env,
            )
        except OSError as exc:
            fail("compiler_execution", f"cannot execute compiler: {exc}")
        if run.returncode != 0:
            detail = run.stderr.decode("utf-8", errors="replace").strip()
            fail("compiler_execution", f"compiler capture failed with {run.returncode}: {detail}")
        return run.stdout


def compiler_matches(rustc: str) -> tuple[bool, str | None]:
    actual, unavailable = compiler_vv(rustc)
    if actual is None:
        return False, unavailable
    if actual != expected_compiler_vv():
        return False, "compiler identity does not match the registered rustc -vV"
    return True, None


def render_checksums(root: Path, output: bytes) -> bytes:
    material = {
        SOURCE_NAME: (root / SOURCE_NAME).read_bytes(),
        OUTPUT_NAME: output,
        PROVENANCE_NAME: (root / PROVENANCE_NAME).read_bytes(),
    }
    return "".join(
        f"{sha256_bytes(material[name])}  {name}\n" for name in HASHED_FILES
    ).encode("ascii")


def atomic_write(path: Path, data: bytes) -> None:
    fd, tmp_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp_name, path)
    except BaseException:
        try:
            os.unlink(tmp_name)
        except FileNotFoundError:
            pass
        raise


def regenerate_fixture(root: Path, rustc: str, *, require_canonical: bool) -> None:
    if require_canonical and root.resolve() != CANONICAL_ROOT.resolve():
        fail("noncanonical_regenerate", "CLI regeneration is restricted to the canonical fixture root")
    names = directory_names(root)
    allowed_before = EXPECTED_FILES
    if not {SOURCE_NAME, PROVENANCE_NAME}.issubset(names) or not names.issubset(allowed_before):
        fail("unexpected_file", "regeneration requires only the registered fixture files")
    load_manifest(root)
    matches, reason = compiler_matches(rustc)
    if not matches:
        fail("compiler_identity_mismatch", reason or "compiler identity mismatch")
    first = capture_once(root, rustc)
    second = capture_once(root, rustc)
    if first != second:
        fail("nondeterministic_output", "two compiler captures differ byte-for-byte")
    checksums = render_checksums(root, first)
    atomic_write(root / OUTPUT_NAME, first)
    atomic_write(root / CHECKSUM_NAME, checksums)


def verify_fixture(root: Path, rustc: str, *, require_replay: bool) -> dict[str, object]:
    verify_content(root)
    matches, reason = compiler_matches(rustc)
    if not matches:
        if require_replay:
            fail("compiler_identity_mismatch", reason or "compiler identity mismatch")
        return {
            "compiler_replay": "unavailable",
            "compiler_replay_reason": reason,
            "content_valid": True,
            "schema": SCHEMA,
        }
    fresh = capture_once(root, rustc)
    committed = (root / OUTPUT_NAME).read_bytes()
    if fresh != committed:
        fail("compiler_replay_mismatch", "fresh compiler stdout differs from the committed MIR")
    return {
        "compiler_replay": "exact",
        "content_valid": True,
        "schema": SCHEMA,
    }


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--verify", action="store_true")
    modes.add_argument("--require-replay", action="store_true")
    modes.add_argument("--regenerate", action="store_true")
    parser.add_argument(
        "--fixture-root",
        type=Path,
        default=CANONICAL_ROOT,
        help="alternate read-only fixture root for verification tests",
    )
    parser.add_argument(
        "--rustc",
        default=os.environ.get("AXEYUM_MIR_RUSTC", "rustc"),
        help="compiler executable (or set AXEYUM_MIR_RUSTC)",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    root = args.fixture_root.resolve()
    try:
        if args.regenerate:
            regenerate_fixture(root, args.rustc, require_canonical=True)
            result = verify_fixture(root, args.rustc, require_replay=True)
            result["regenerated"] = True
        else:
            result = verify_fixture(root, args.rustc, require_replay=args.require_replay)
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
        return 0
    except FixtureError as exc:
        print(
            json.dumps(
                {"error_class": exc.error_class, "message": str(exc)},
                sort_keys=True,
                separators=(",", ":"),
            ),
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
