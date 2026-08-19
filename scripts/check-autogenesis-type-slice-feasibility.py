#!/usr/bin/env python3
"""Verify the sealed proof-free type-slice feasibility observation."""

from __future__ import annotations

from collections import Counter
import hashlib
import importlib.util
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-type-slice-feasibility-v1.json"


class TypeSliceResultError(RuntimeError):
    """The diagnostic result is unavailable, stale, malformed, or overclaimed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise TypeSliceResultError(f"{path} is not an object")
    return value


def load_analyzer(path: pathlib.Path):
    spec = importlib.util.spec_from_file_location("type_slice_analyzer_for_result", path)
    if spec is None or spec.loader is None:
        raise TypeSliceResultError(f"cannot load analyzer {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def validate_observation(
    manifest: dict[str, Any],
    observation: dict[str, Any],
    prior_observation: dict[str, Any],
) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise TypeSliceResultError("inner observation identity changed")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind") != "axeyum-autogenesis-type-slice-feasibility"
        or observation.get("state") != "syntactic-diagnostic-no-proof-or-ledger-credit"
        or observation.get("authority")
        != {
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_executed": False,
            "targets": 138,
        }
        or claimed != manifest["observation_archive"]["observation_sha256"]
    ):
        raise TypeSliceResultError("observation contract changed")
    rows = observation.get("rows")
    prior_rows = prior_observation.get("rows")
    if not isinstance(rows, list) or not isinstance(prior_rows, list) or len(rows) != 138:
        raise TypeSliceResultError("diagnostic population changed")
    by_artifact = {
        row.get("artifact_file"): row for row in prior_rows if isinstance(row, dict)
    }
    if len(by_artifact) != 138:
        raise TypeSliceResultError("prior coverage population changed")
    implementation_contaminated = 0
    type_clean = 0
    prior_rejections_clean = 0
    aggregates = Counter()
    seen = set()
    for row in rows:
        if not isinstance(row, dict):
            raise TypeSliceResultError("type-slice row is not an object")
        artifact = row.get("artifact_file")
        if artifact in seen or artifact not in by_artifact:
            raise TypeSliceResultError("type-slice row identity changed")
        seen.add(artifact)
        prior = by_artifact[artifact]
        if any(
            row.get(field) != prior.get(field)
            for field in ("artifact_file", "fact_id", "family", "partition", "target_definition")
        ):
            raise TypeSliceResultError(f"row mapping changed: {artifact}")
        if row.get("partition") not in {"train", "development"}:
            raise TypeSliceResultError("held-out row entered the observation")
        implementation_trusted = row.get("implementation_trusted")
        type_trusted = row.get("type_trusted")
        boundary = row.get("abstractable_type_boundary")
        if not all(isinstance(value, list) for value in (implementation_trusted, type_trusted, boundary)):
            raise TypeSliceResultError("dependency lists are malformed")
        implementation_contaminated += bool(implementation_trusted)
        type_clean += not type_trusted
        if prior.get("outcome") == "adapter-rejection" and not type_trusted:
            prior_rejections_clean += 1
        for field in ("declarations", "implementation_declarations", "type_declarations"):
            value = row.get(field)
            if not isinstance(value, int) or value < 0:
                raise TypeSliceResultError(f"invalid declaration count: {field}")
            aggregates[field] += value
        aggregates["abstractable"] += len(boundary)
    expected_coverage = manifest["coverage"]
    actual_coverage = {
        "implementation_closure_has_trusted": implementation_contaminated,
        "type_closure_has_no_trusted": type_clean,
        "type_closure_has_trusted": 138 - type_clean,
        "prior_adapter_rejections_with_clean_type_closure": prior_rejections_clean,
    }
    if observation.get("coverage") != {
        key: actual_coverage[key]
        for key in (
            "implementation_closure_has_trusted",
            "type_closure_has_no_trusted",
            "type_closure_has_trusted",
        )
    } or actual_coverage != expected_coverage:
        raise TypeSliceResultError("coverage totals changed")
    expected_aggregates = manifest["aggregate_declarations"]
    if (
        aggregates["declarations"] != expected_aggregates["exported"]
        or aggregates["implementation_declarations"]
        != expected_aggregates["implementation_closure"]
        or aggregates["type_declarations"] != expected_aggregates["type_closure"]
        or aggregates["abstractable"]
        != expected_aggregates["abstractable_type_boundary_occurrences"]
    ):
        raise TypeSliceResultError("aggregate declaration counts changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-type-slice-feasibility"
        or manifest.get("state") != "syntactic-diagnostic-no-proof-or-ledger-credit"
        or manifest.get("population", {}).get("held_out_inspected") is not False
        or manifest.get("population", {}).get("ledger_writes") != 0
    ):
        raise TypeSliceResultError("manifest contract changed")
    analyzer_path = ROOT / manifest["analyzer"]["path"]
    if sha256(analyzer_path) != manifest["analyzer"]["sha256"]:
        raise TypeSliceResultError("analyzer identity changed")
    source_root = pathlib.Path(manifest["source_archive"]["root"])
    observation_root = pathlib.Path(manifest["observation_archive"]["root"])
    observation_path = observation_root / manifest["observation_archive"]["file"]
    if not source_root.is_dir() or not observation_root.is_dir():
        raise TypeSliceResultError("external archive is unavailable")
    if (
        sha256(source_root / "mapping.json")
        != manifest["source_archive"]["mapping_sha256"]
        or sha256(source_root / "observation.json")
        != manifest["source_archive"]["coverage_observation_sha256"]
        or sha256(observation_path)
        != manifest["observation_archive"]["file_sha256"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
    ):
        raise TypeSliceResultError("external evidence changed or is mutable")
    mapping = load(source_root / "mapping.json")
    observation = load(observation_path)
    prior_observation = load(source_root / "observation.json")
    validate_observation(manifest, observation, prior_observation)
    analyzer = load_analyzer(analyzer_path)
    reproduced = analyzer.analyze_archive(source_root, mapping)
    if reproduced != observation:
        raise TypeSliceResultError("analysis does not reproduce byte-semantic output")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_TYPE_SLICE_FEASIBILITY_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "rows=138|prior_rejections_clean=114|type_trusted=0|"
            "held_out=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        TypeSliceResultError,
    ) as error:
        print(f"autogenesis-type-slice-feasibility: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
