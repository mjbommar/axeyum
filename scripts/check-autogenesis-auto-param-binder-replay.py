#!/usr/bin/env python3
"""Verify the checked Mathlib replay with bounded autoParam binder transport."""

from __future__ import annotations

from collections import Counter
import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-auto-param-binder-replay-v1.json"
BASE_SCRIPT = ROOT / "scripts/check-autogenesis-checked-type-slice-replay.py"
SPEC = importlib.util.spec_from_file_location("checked_type_slice_base", BASE_SCRIPT)
assert SPEC is not None and SPEC.loader is not None
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
SPEC.loader.exec_module(BASE)

POLICY_VERSION = "contaminated-definition-boundary-auto-param-binders-v3"
V1_SCHEMA = "axeyum-proof-free-type-slice-receipt-v1"
V2_SCHEMA = "axeyum-proof-free-type-slice-receipt-v2"
NORMALIZATION_KIND = "checked-auto-param-type-only-v1"
AUTO_PARAM_SHA256 = "b689f75f537fda7c41491b554675d2bcbf6c52733d66ae6cb7885215a73f2a6a"
NORMALIZED_ARTIFACTS = {
    "r014.ndjson",
    "r057.ndjson",
    "r058.ndjson",
    "r064.ndjson",
    "r065.ndjson",
    "r081.ndjson",
    "r088.ndjson",
    "r090.ndjson",
    "r124.ndjson",
    "r128.ndjson",
}
EXPECTED_DECLARATIONS = Counter(
    {
        "AddMonoid.mk": 6,
        "AddMonoid.rec": 6,
        "Monoid.mk": 7,
        "Monoid.rec": 7,
        "Preorder.mk": 3,
        "Preorder.rec": 3,
        "Semiring.mk": 6,
        "Semiring.rec": 6,
    }
)


class BinderReplayError(RuntimeError):
    """The replay evidence is absent, mutable, stale, or overclaimed."""


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    return sha256_bytes(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BinderReplayError(f"{path} is not an object")
    return value


def require_hash(value: Any, context: str) -> None:
    try:
        BASE.require_hash(value, context)
    except BASE.CheckedSliceError as error:
        raise BinderReplayError(str(error)) from error


def git_blob(commit: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise BinderReplayError(f"tooling blob is unavailable: {commit}:{path}")
    return result.stdout


def validate_mapping(mapping: dict[str, Any]) -> list[dict[str, Any]]:
    try:
        return BASE.validate_mapping(mapping)
    except BASE.CheckedSliceError as error:
        raise BinderReplayError(str(error)) from error


def validate_receipt(receipt: Any, row: dict[str, Any]) -> tuple[int, Counter[str], int]:
    if not isinstance(receipt, dict):
        raise BinderReplayError("accepted row lacks a receipt")
    unsigned = dict(receipt)
    claimed = unsigned.pop("receipt_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise BinderReplayError("receipt digest changed")
    schema = receipt.get("schema_version")
    normalization = receipt.get("transport_normalization")
    if (
        schema not in {V1_SCHEMA, V2_SCHEMA}
        or receipt.get("policy_version") != POLICY_VERSION
        or receipt.get("specialization_verified") is not True
        or (schema == V1_SCHEMA) != (normalization is None)
    ):
        raise BinderReplayError("receipt transport contract changed")
    for field in BASE.HASH_FIELDS:
        require_hash(receipt.get(field), f"receipt {field}")
    source = receipt.get("source")
    if not isinstance(source, dict):
        raise BinderReplayError("receipt source identity is absent")
    if source.get("stream_sha256") != row.get("stream_sha256") or source.get("target") != row.get("target_definition"):
        raise BinderReplayError("receipt source identity changed")
    for field in BASE.SOURCE_HASH_FIELDS:
        require_hash(source.get(field), f"receipt source {field}")
    retained = receipt.get("retained")
    abstractions = receipt.get("abstractions")
    if not isinstance(retained, list) or not isinstance(abstractions, list):
        raise BinderReplayError("receipt inventories are malformed")
    retained_by_name: dict[str, dict[str, Any]] = {}
    for item in retained:
        if not isinstance(item, dict) or item.get("kind") in BASE.TRUSTED_KINDS:
            raise BinderReplayError("receipt retains a trusted declaration")
        name = item.get("name")
        if not isinstance(name, str) or not name or name in retained_by_name:
            raise BinderReplayError("receipt retained inventory is malformed")
        require_hash(item.get("content_sha256"), "retained content")
        require_hash(item.get("dependency_sha256"), "retained dependencies")
        retained_by_name[name] = item
    for position, item in enumerate(abstractions):
        if not isinstance(item, dict) or item.get("binder_position") != position:
            raise BinderReplayError("receipt binder order changed")
        if not isinstance(item.get("source_name"), str) or not item["source_name"]:
            raise BinderReplayError("receipt abstraction name is malformed")
        if not isinstance(item.get("source_occurrences"), int) or item["source_occurrences"] < 1:
            raise BinderReplayError("receipt abstraction occurrence count is malformed")
        require_hash(item.get("instantiated_type_sha256"), "abstraction type")
        require_hash(item.get("source_content_sha256"), "abstraction source")
        levels = item.get("universe_sha256")
        if not isinstance(levels, list):
            raise BinderReplayError("receipt universe identity is malformed")
        for level in levels:
            require_hash(level, "abstraction universe")
    changed: Counter[str] = Counter()
    rewrites = 0
    if schema == V2_SCHEMA:
        if not isinstance(normalization, dict):
            raise BinderReplayError("normalized receipt lacks transport evidence")
        declarations = normalization.get("declarations")
        rewrites = normalization.get("rewritten_occurrences")
        if (
            normalization.get("kind") != NORMALIZATION_KIND
            or normalization.get("auto_param_source_content_sha256") != AUTO_PARAM_SHA256
            or not isinstance(rewrites, int)
            or rewrites < 1
            or not isinstance(declarations, list)
            or not declarations
        ):
            raise BinderReplayError("autoParam normalization contract changed")
        names = [item.get("name") for item in declarations if isinstance(item, dict)]
        if len(names) != len(declarations) or names != sorted(set(names)):
            raise BinderReplayError("normalized declarations are not sorted and unique")
        for item in declarations:
            name = item["name"]
            retained_item = retained_by_name.get(name)
            for field in (
                "source_content_sha256",
                "normalized_content_sha256",
                "normalized_dependency_sha256",
            ):
                require_hash(item.get(field), f"normalized declaration {field}")
            if item["source_content_sha256"] == item["normalized_content_sha256"]:
                raise BinderReplayError("normalization did not change declaration content")
            if retained_item is None or (
                retained_item["content_sha256"] != item["normalized_content_sha256"]
                or retained_item["dependency_sha256"] != item["normalized_dependency_sha256"]
            ):
                raise BinderReplayError("normalized declaration is not the retained identity")
            changed[name] += 1
    return len(abstractions), changed, rewrites


def validate_observation(
    manifest: dict[str, Any],
    observation: dict[str, Any],
    mapping: dict[str, Any],
    source_root: pathlib.Path | None,
) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise BinderReplayError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["development", "train"],
        "held_out_inspected": False,
        "proof_producers_executed": False,
        "proof_bodies_requested": False,
        "ledger_writes": 0,
        "targets": 138,
    }
    if (
        observation.get("schema_version") != 1
        or observation.get("kind") != "axeyum-autogenesis-checked-type-slice-replay"
        or observation.get("state") != "checked-slice-replay-no-proof-or-ledger-credit"
        or observation.get("policy_version") != POLICY_VERSION
        or observation.get("authority") != expected_authority
        or observation.get("mapping_sha256") != manifest["source_archive"]["mapping_sha256"]
        or claimed != manifest["observation_archive"]["observation_sha256"]
    ):
        raise BinderReplayError("observation contract changed")
    mapping_rows = validate_mapping(mapping)
    rows = observation.get("rows")
    if not isinstance(rows, list) or len(rows) != 138:
        raise BinderReplayError("observation population changed")
    by_artifact = {row["artifact_file"]: row for row in mapping_rows}
    seen: set[str] = set()
    schemas: Counter[str] = Counter()
    changed: Counter[str] = Counter()
    normalized_artifacts: set[str] = set()
    abstraction_total = 0
    rewrite_total = 0
    for row in rows:
        if not isinstance(row, dict):
            raise BinderReplayError("observation row is malformed")
        artifact = row.get("artifact_file")
        if artifact in seen or artifact not in by_artifact:
            raise BinderReplayError("observation row identity changed")
        seen.add(artifact)
        mapped = by_artifact[artifact]
        for field in ("artifact_file", "fact_id", "family", "partition", "target_definition"):
            if row.get(field) != mapped.get(field):
                raise BinderReplayError(f"observation mapping changed: {artifact}")
        require_hash(row.get("stream_sha256"), "source stream")
        if source_root is not None and sha256(source_root / "streams" / artifact) != row["stream_sha256"]:
            raise BinderReplayError(f"source stream changed: {artifact}")
        if row.get("outcome") != "accepted-receipt" or "decline" in row:
            raise BinderReplayError("replay no longer accepts every row")
        receipt = row.get("receipt")
        count, row_changed, rewrites = validate_receipt(receipt, row)
        schemas[receipt["schema_version"]] += 1
        abstraction_total += count
        rewrite_total += rewrites
        changed.update(row_changed)
        if row_changed:
            normalized_artifacts.add(artifact)
    coverage = manifest["coverage"]
    expected_coverage = {
        "accepted_receipts": 138,
        "declined_selection": 0,
        "exact_v1_receipts": 128,
        "normalized_v2_receipts": 10,
        "abstractions": 152,
        "rewritten_occurrences": 164,
        "normalized_artifacts": sorted(NORMALIZED_ARTIFACTS),
    }
    if (
        observation.get("coverage") != {"accepted-receipt": 138}
        or coverage != expected_coverage
        or schemas != Counter({V1_SCHEMA: 128, V2_SCHEMA: 10})
        or abstraction_total != 152
        or rewrite_total != 164
        or changed != EXPECTED_DECLARATIONS
        or normalized_artifacts != NORMALIZED_ARTIFACTS
    ):
        raise BinderReplayError("binder replay coverage changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-auto-param-binder-replay"
        or manifest.get("state") != "checked-slice-replay-no-proof-or-ledger-credit"
        or manifest.get("population") != {
            "train_development": 138,
            "held_out_inspected": False,
            "proof_producers_executed": False,
            "proof_bodies_requested": False,
            "ledger_writes": 0,
        }
    ):
        raise BinderReplayError("manifest contract changed")
    commit = manifest.get("tooling_commit")
    if not isinstance(commit, str) or len(commit) != 40:
        raise BinderReplayError("tooling commit is malformed")
    tooling_files = manifest.get("tooling_files")
    if not isinstance(tooling_files, list) or len(tooling_files) != 4:
        raise BinderReplayError("tooling inventory changed")
    for item in tooling_files:
        path = item.get("path")
        if not isinstance(path, str) or sha256_bytes(git_blob(commit, path)) != item.get("sha256"):
            raise BinderReplayError(f"tooling identity changed: {path}")
    source_root = pathlib.Path(manifest["source_archive"]["root"])
    observation_root = pathlib.Path(manifest["observation_archive"]["root"])
    observation_path = observation_root / manifest["observation_archive"]["file"]
    if not source_root.is_dir() or not observation_root.is_dir():
        raise BinderReplayError("external replay archive is unavailable")
    if (
        sha256(source_root / "mapping.json") != manifest["source_archive"]["mapping_sha256"]
        or sha256(observation_path) != manifest["observation_archive"]["file_sha256"]
        or observation_path.stat().st_size != manifest["observation_archive"]["bytes"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_root.stat().st_mode) != 0o555
    ):
        raise BinderReplayError("external replay evidence changed or is mutable")
    validate_observation(
        manifest,
        load(observation_path),
        load(source_root / "mapping.json"),
        source_root,
    )
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_AUTO_PARAM_BINDER_REPLAY_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "accepted=138|normalized=10|rewrites=164|held_out=0|proofs=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BinderReplayError) as error:
        print(f"autogenesis-auto-param-binder-replay: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
