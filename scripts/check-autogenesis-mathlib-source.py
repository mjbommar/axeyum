#!/usr/bin/env python3
"""Check the pinned statement-only Mathlib source and its external artifact."""

from __future__ import annotations

import hashlib
import json
import pathlib
import re
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-statement-source-v1.json"
EXPECTED_KEYS = {"level_params", "module", "name", "type", "type_repr"}


class SourceError(RuntimeError):
    """The source identity or statement-only boundary is invalid."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SourceError(f"{path} is not a JSON object")
    return value


def verify_manifest(manifest: dict[str, Any], root: pathlib.Path = ROOT) -> None:
    unsigned = dict(manifest)
    claimed = unsigned.pop("manifest_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise SourceError("manifest digest is missing or invalid")
    if manifest.get("schema_version") != 1 or manifest.get("kind") != "axeyum-autogenesis-external-statement-source":
        raise SourceError("manifest schema identity is invalid")
    source = manifest.get("source")
    if not isinstance(source, dict) or source.get("commit") != "c5ea00351c28e24afc9f0f84379aa41082b1188f" or source.get("tag") != "v4.30.0":
        raise SourceError("Mathlib source identity changed")
    extractor = manifest.get("extractor")
    if not isinstance(extractor, dict):
        raise SourceError("extractor identity is absent")
    path = root / str(extractor.get("path"))
    if not path.is_file() or sha256_file(path) != extractor.get("sha256"):
        raise SourceError("extractor bytes do not match the manifest")
    text = path.read_text()
    if re.search(r"theoremInfo\s*\.\s*value", text):
        raise SourceError("extractor reads a theorem proof value")
    for marker in ("theoremInfo.type", '"type_repr"', '"type"'):
        if marker not in text:
            raise SourceError(f"extractor no longer emits statement marker {marker!r}")
    artifact = manifest.get("external_artifact")
    if not isinstance(artifact, dict) or artifact.get("content") != "statement-only-ndjson":
        raise SourceError("external statement artifact contract is invalid")
    policy = manifest.get("integration_policy")
    if not isinstance(policy, dict) or "must not read" not in str(policy.get("proof_isolation")):
        raise SourceError("proof-isolation policy is absent")


def verify_rows(path: pathlib.Path, artifact: dict[str, Any]) -> None:
    if path.stat().st_size != artifact.get("bytes"):
        raise SourceError("external statement artifact byte count changed")
    if sha256_file(path) != artifact.get("sha256"):
        raise SourceError("external statement artifact digest changed")
    count = 0
    previous = ""
    seen: set[str] = set()
    with path.open() as source:
        for count, line in enumerate(source, start=1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise SourceError(f"external row {count} is malformed: {error}") from error
            if not isinstance(row, dict) or set(row) != EXPECTED_KEYS:
                raise SourceError(f"external row {count} has the wrong statement-only fields")
            name = row.get("name")
            if not isinstance(name, str) or not (name.startswith("Nat.") or name.startswith("Int.")):
                raise SourceError(f"external row {count} is outside the Nat/Int scope")
            if name in seen or (previous and name < previous):
                raise SourceError(f"external row {count} is duplicate or out of order")
            seen.add(name)
            previous = name
            if not isinstance(row.get("module"), str) or not row["module"]:
                raise SourceError(f"external row {count} lacks a defining module")
            if not isinstance(row.get("level_params"), list) or not all(isinstance(value, str) for value in row["level_params"]):
                raise SourceError(f"external row {count} has malformed level parameters")
            if not isinstance(row.get("type"), str) or not row["type"]:
                raise SourceError(f"external row {count} lacks a readable theorem type")
            if not isinstance(row.get("type_repr"), str) or "Lean.Expr" not in row["type_repr"]:
                raise SourceError(f"external row {count} lacks a structural theorem type")
    if count != artifact.get("records"):
        raise SourceError("external statement artifact record count changed")


def check(manifest: dict[str, Any], root: pathlib.Path = ROOT) -> str:
    verify_manifest(manifest, root)
    artifact = manifest["external_artifact"]
    storage = pathlib.Path(artifact["storage_root"])
    path = storage / artifact["file"]
    if not storage.exists():
        return "unavailable"
    if not path.is_file():
        raise SourceError("external storage is mounted but the statement artifact is absent")
    verify_rows(path, artifact)
    return "verified"


def main() -> int:
    try:
        manifest = load_object(MANIFEST)
        external = check(manifest)
        print(
            "AUTOGENESIS_MATHLIB_SOURCE_OK|"
            f"{manifest['manifest_sha256']}|external={external}|"
            f"records={manifest['external_artifact']['records']}"
        )
    except (OSError, json.JSONDecodeError, SourceError) as error:
        print(f"autogenesis-mathlib-source: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
