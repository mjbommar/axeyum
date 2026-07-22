"""Fail-closed helpers for the ADR-0356 pinned official producer."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import tomllib
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping

from scripts.smtcomp_repro.official_selection import canonical_json_bytes


CHUNK = 1024 * 1024
RUNTIME_ROOTS = ("email-validator", "polars", "pydantic", "rich")
EXPECTED_RUNTIME_PACKAGES = 14


class OfficialProducerError(ValueError):
    """An input or output violates the pinned official-producer contract."""


def hash_file(path: Path) -> tuple[int, str]:
    """Return byte count and SHA-256 for one regular non-symlink file."""
    if path.is_symlink() or not path.is_file():
        raise OfficialProducerError(f"not a regular file: {path}")
    size = 0
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while data := source.read(CHUNK):
            size += len(data)
            digest.update(data)
    return size, digest.hexdigest()


def _safe_relative_path(value: object) -> PurePosixPath:
    if not isinstance(value, str):
        raise OfficialProducerError(f"authority path is not a string: {value!r}")
    path = PurePosixPath(value)
    if (
        "\\" in value
        or path.as_posix() != value
        or path.is_absolute()
        or not path.parts
        or any(part in {"", ".", ".."} for part in path.parts)
    ):
        raise OfficialProducerError(f"unsafe authority path: {value!r}")
    return path


def authority_bundle_entries(authority: Mapping[str, Any]) -> list[dict[str, object]]:
    """Return the exact source/data/submission files required by the producer."""
    raw_entries: list[Mapping[str, Any]] = []
    organizer = authority.get("organizer")
    if not isinstance(organizer, Mapping) or not isinstance(organizer.get("source_files"), list):
        raise OfficialProducerError("authority organizer source list is missing")
    raw_entries.extend(organizer["source_files"])
    benchmark = authority.get("benchmark_metadata")
    if not isinstance(benchmark, Mapping):
        raise OfficialProducerError("authority benchmark metadata is missing")
    raw_entries.append(benchmark)
    historical = authority.get("historical_results")
    submissions = authority.get("submissions")
    if not isinstance(historical, list) or not isinstance(submissions, list):
        raise OfficialProducerError("authority data or submission list is missing")
    raw_entries.extend(historical)
    raw_entries.extend(submissions)

    entries: list[dict[str, object]] = []
    seen: set[str] = set()
    for raw in raw_entries:
        if not isinstance(raw, Mapping):
            raise OfficialProducerError("authority bundle entry is not an object")
        path = _safe_relative_path(raw.get("path"))
        name = path.as_posix()
        byte_count = raw.get("bytes")
        sha256 = raw.get("sha256")
        if (
            name in seen
            or isinstance(byte_count, bool)
            or not isinstance(byte_count, int)
            or byte_count < 0
            or not isinstance(sha256, str)
            or len(sha256) != 64
        ):
            raise OfficialProducerError(f"invalid or duplicate authority bundle entry: {name}")
        seen.add(name)
        entries.append({"bytes": byte_count, "path": name, "sha256": sha256})
    entries.sort(key=lambda row: str(row["path"]))
    return entries


def verify_bundle(root: Path, entries: Iterable[Mapping[str, object]], exact: bool = True) -> list[dict[str, object]]:
    """Verify a materialized producer bundle and optionally reject extra files."""
    expected: set[str] = set()
    verified: list[dict[str, object]] = []
    if root.is_symlink() or not root.is_dir():
        raise OfficialProducerError(f"bundle root is not a regular directory: {root}")
    for entry in entries:
        relative = _safe_relative_path(entry.get("path"))
        name = relative.as_posix()
        if name in expected:
            raise OfficialProducerError(f"duplicate expected bundle path: {name}")
        expected.add(name)
        path = root.joinpath(*relative.parts)
        size, sha256 = hash_file(path)
        if size != entry.get("bytes") or sha256 != entry.get("sha256"):
            raise OfficialProducerError(f"bundle file identity differs: {name}")
        verified.append({"bytes": size, "path": name, "sha256": sha256})
    if exact:
        actual = set()
        for directory, names, filenames in os.walk(root, followlinks=False):
            base = Path(directory)
            for name in names:
                child = base / name
                if child.is_symlink() or not child.is_dir():
                    raise OfficialProducerError(f"non-directory in bundle tree: {child}")
            for name in filenames:
                child = base / name
                if child.is_symlink() or not child.is_file():
                    raise OfficialProducerError(f"non-regular bundle entry: {child}")
                actual.add(child.relative_to(root).as_posix())
        if actual != expected:
            raise OfficialProducerError(
                f"bundle file set differs: missing={sorted(expected - actual)!r} extra={sorted(actual - expected)!r}"
            )
    return verified


def materialize_bundle(source: Path, destination: Path, entries: list[Mapping[str, object]]) -> list[dict[str, object]]:
    """Copy an already verified bundle without Git history or unregistered files."""
    if destination.exists():
        raise OfficialProducerError(f"bundle destination already exists: {destination}")
    verify_bundle(source, entries, exact=False)
    destination.mkdir(parents=True)
    for entry in entries:
        relative = _safe_relative_path(entry.get("path"))
        src = source.joinpath(*relative.parts)
        dst = destination.joinpath(*relative.parts)
        dst.parent.mkdir(parents=True, exist_ok=True)
        with src.open("rb") as input_file, dst.open("xb") as output_file:
            shutil.copyfileobj(input_file, output_file, length=CHUNK)
    return verify_bundle(destination, entries, exact=True)


def _dependency_name(value: str) -> str:
    return value.lower().replace("_", "-")


def locked_runtime_requirements(lock_bytes: bytes) -> tuple[bytes, list[dict[str, object]]]:
    """Derive a hash-locked minimal runtime closure from the pinned Poetry lock."""
    try:
        lock = tomllib.loads(lock_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise OfficialProducerError("poetry.lock is not valid UTF-8 TOML") from error
    packages = lock.get("package")
    metadata = lock.get("metadata")
    if not isinstance(packages, list) or not isinstance(metadata, dict):
        raise OfficialProducerError("poetry.lock package or metadata section is missing")
    if metadata.get("lock-version") != "2.1" or metadata.get("python-versions") != ">=3.11,<4.0":
        raise OfficialProducerError("poetry.lock metadata differs")
    by_name: dict[str, dict[str, Any]] = {}
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get("name"), str):
            raise OfficialProducerError("invalid poetry.lock package")
        name = _dependency_name(package["name"])
        if name in by_name:
            raise OfficialProducerError(f"duplicate locked package: {name}")
        by_name[name] = package

    pending = list(RUNTIME_ROOTS)
    selected: set[str] = set()
    while pending:
        name = _dependency_name(pending.pop())
        if name in selected:
            continue
        package = by_name.get(name)
        if package is None:
            raise OfficialProducerError(f"runtime dependency is absent from poetry.lock: {name}")
        if "main" not in package.get("groups", []):
            raise OfficialProducerError(f"runtime dependency is not in the main lock group: {name}")
        selected.add(name)
        dependencies = package.get("dependencies", {})
        if not isinstance(dependencies, dict):
            raise OfficialProducerError(f"invalid locked dependencies: {name}")
        pending.extend(dependencies)

    manifest: list[dict[str, object]] = []
    requirement_blocks: list[str] = []
    for name in sorted(selected):
        package = by_name[name]
        version = package.get("version")
        files = package.get("files")
        if not isinstance(version, str) or not isinstance(files, list) or not files:
            raise OfficialProducerError(f"locked package identity is incomplete: {name}")
        hashes = sorted(
            entry.get("hash")
            for entry in files
            if isinstance(entry, dict)
            and isinstance(entry.get("hash"), str)
            and entry["hash"].startswith("sha256:")
        )
        if len(hashes) != len(files):
            raise OfficialProducerError(f"locked package has a non-SHA-256 artifact: {name}")
        markers = package.get("markers")
        if isinstance(markers, dict):
            marker = markers.get("main")
        else:
            marker = markers
        if marker is not None and not isinstance(marker, str):
            raise OfficialProducerError(f"invalid main-group marker: {name}")
        header = f"{name}=={version}" + (f" ; {marker}" if marker else "")
        block = header + " " + " ".join(f"--hash={value}" for value in hashes)
        requirement_blocks.append(block)
        manifest.append({"hashes": hashes, "marker": marker, "name": name, "version": version})
    return ("\n".join(requirement_blocks) + "\n").encode(), manifest


def validate_selected_output(selected: bytes, expected_count: int | None = None) -> list[str]:
    """Require a normalized, LF-terminated, strict path-sorted selected list."""
    try:
        text = selected.decode("utf-8")
    except UnicodeDecodeError as error:
        raise OfficialProducerError("official selected output is not UTF-8") from error
    if not text.endswith("\n") or "\r" in text:
        raise OfficialProducerError("official selected output is not LF-terminated")
    paths = text.splitlines()
    if expected_count is not None and len(paths) != expected_count:
        raise OfficialProducerError(f"official selected count differs: {len(paths)}/{expected_count}")
    previous: str | None = None
    for value in paths:
        path = _safe_relative_path(value)
        if len(path.parts) < 4 or path.parts[0] != "non-incremental":
            raise OfficialProducerError(f"invalid selected benchmark path: {value!r}")
        if previous is not None and value <= previous:
            raise OfficialProducerError("official selected output is not strictly path-sorted")
        previous = value
    return paths


def validate_repetition(first: Path, second: Path) -> dict[str, str]:
    """Require exact normalized selection and per-logic equality across runs."""
    first_selected = (first / "official-selected.txt").read_bytes()
    second_selected = (second / "official-selected.txt").read_bytes()
    first_paths = validate_selected_output(first_selected)
    second_paths = validate_selected_output(second_selected)
    if first_selected != second_selected or first_paths != second_paths:
        raise OfficialProducerError("official selected bytes differ across fresh environments")
    first_logic = (first / "per-logic.json").read_bytes()
    second_logic = (second / "per-logic.json").read_bytes()
    try:
        first_value = json.loads(first_logic)
        second_value = json.loads(second_logic)
    except json.JSONDecodeError as error:
        raise OfficialProducerError("per-logic output is not JSON") from error
    if (
        first_logic != canonical_json_bytes(first_value)
        or second_logic != canonical_json_bytes(second_value)
        or first_logic != second_logic
    ):
        raise OfficialProducerError("per-logic output differs across fresh environments")
    return {
        "official_selected_sha256": hashlib.sha256(first_selected).hexdigest(),
        "per_logic_sha256": hashlib.sha256(first_logic).hexdigest(),
    }
