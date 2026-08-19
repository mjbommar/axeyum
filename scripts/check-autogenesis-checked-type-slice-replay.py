#!/usr/bin/env python3
"""Verify the proof-free checked Mathlib type-slice replay."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-checked-type-slice-replay-v1.json"
TRUSTED_KINDS = {"axiom", "theorem", "opaque", "quotient"}
POLICY_VERSION = "contaminated-definition-boundary-v1"
HASH_FIELDS = {
    "fresh_target_content_sha256",
    "sliced_goal_sha256",
}
SOURCE_HASH_FIELDS = {
    "goal_sha256",
    "stream_sha256",
    "target_content_sha256",
}


class CheckedSliceError(RuntimeError):
    """The checked replay is absent, stale, malformed, or overclaimed."""


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return sha256_bytes(encoded)


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CheckedSliceError(f"{path} is not an object")
    return value


def require_hash(value: Any, context: str) -> None:
    if not isinstance(value, str) or len(value) != 64:
        raise CheckedSliceError(f"{context} is not a SHA-256 digest")
    try:
        int(value, 16)
    except ValueError as error:
        raise CheckedSliceError(f"{context} is not a SHA-256 digest") from error


def git_blob(commit: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise CheckedSliceError(f"tooling blob is unavailable: {commit}:{path}")
    return result.stdout


def validate_mapping(mapping: dict[str, Any]) -> list[dict[str, Any]]:
    if (
        mapping.get("kind") != "axeyum-autogenesis-reflexivity-coverage-input"
        or mapping.get("state") != "proof-free-source-input"
        or mapping.get("authority")
        != {
            "nursery_sha256": "f23d76470e29719f5f4303d3e6d34fcd23bf2018692d6fe73fd9f17b85aa497b",
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_accessed": False,
            "target_outcomes_accessed": False,
            "facts_opened": 138,
        }
    ):
        raise CheckedSliceError("mapping authority changed or crossed the sealed boundary")
    rows = mapping.get("rows")
    if not isinstance(rows, list) or len(rows) != 138 or not all(isinstance(row, dict) for row in rows):
        raise CheckedSliceError("mapping population changed")
    identities = [set(), set(), set()]
    for row in rows:
        values = [row.get("artifact_file"), row.get("fact_id"), row.get("target_definition")]
        if not all(isinstance(value, str) and value for value in values):
            raise CheckedSliceError("mapping identity is malformed")
        artifact = values[0]
        if pathlib.Path(artifact).name != artifact or row.get("partition") not in {"train", "development"}:
            raise CheckedSliceError("mapping contains an unsafe path or held-out row")
        for seen, value in zip(identities, values, strict=True):
            if value in seen:
                raise CheckedSliceError("mapping repeats an artifact, fact, or target identity")
            seen.add(value)
    return rows


def validate_receipt(receipt: Any, row: dict[str, Any]) -> int:
    if not isinstance(receipt, dict):
        raise CheckedSliceError("accepted row lacks a receipt")
    unsigned = dict(receipt)
    claimed = unsigned.pop("receipt_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise CheckedSliceError("receipt digest changed")
    if (
        receipt.get("schema_version") != "axeyum-proof-free-type-slice-receipt-v1"
        or receipt.get("policy_version") != POLICY_VERSION
        or receipt.get("specialization_verified") is not True
    ):
        raise CheckedSliceError("receipt contract changed")
    for field in HASH_FIELDS:
        require_hash(receipt.get(field), f"receipt {field}")
    source = receipt.get("source")
    if not isinstance(source, dict):
        raise CheckedSliceError("receipt source identity is absent")
    if source.get("stream_sha256") != row.get("stream_sha256") or source.get("target") != row.get("target_definition"):
        raise CheckedSliceError("receipt source identity changed")
    for field in SOURCE_HASH_FIELDS:
        require_hash(source.get(field), f"receipt source {field}")
    retained = receipt.get("retained")
    abstractions = receipt.get("abstractions")
    if not isinstance(retained, list) or not isinstance(abstractions, list):
        raise CheckedSliceError("receipt inventories are malformed")
    retained_names = set()
    for item in retained:
        if not isinstance(item, dict) or item.get("kind") in TRUSTED_KINDS:
            raise CheckedSliceError("receipt retains a trusted declaration")
        name = item.get("name")
        if not isinstance(name, str) or not name or name in retained_names:
            raise CheckedSliceError("receipt retained inventory is malformed")
        retained_names.add(name)
        require_hash(item.get("content_sha256"), "retained content")
        require_hash(item.get("dependency_sha256"), "retained dependencies")
    for position, item in enumerate(abstractions):
        if not isinstance(item, dict) or item.get("binder_position") != position:
            raise CheckedSliceError("receipt binder order changed")
        if not isinstance(item.get("source_name"), str) or not item["source_name"]:
            raise CheckedSliceError("receipt abstraction name is malformed")
        if not isinstance(item.get("source_occurrences"), int) or item["source_occurrences"] < 1:
            raise CheckedSliceError("receipt abstraction occurrence count is malformed")
        require_hash(item.get("instantiated_type_sha256"), "abstraction type")
        require_hash(item.get("source_content_sha256"), "abstraction source")
        levels = item.get("universe_sha256")
        if not isinstance(levels, list):
            raise CheckedSliceError("receipt universe identity is malformed")
        for level in levels:
            require_hash(level, "abstraction universe")
    return len(abstractions)


def validate_observation(
    manifest: dict[str, Any],
    observation: dict[str, Any],
    mapping: dict[str, Any],
    source_root: pathlib.Path | None,
) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise CheckedSliceError("inner observation identity changed")
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
        raise CheckedSliceError("observation contract changed")
    mapping_rows = validate_mapping(mapping)
    rows = observation.get("rows")
    if not isinstance(rows, list) or len(rows) != 138:
        raise CheckedSliceError("observation population changed")
    by_artifact = {row["artifact_file"]: row for row in mapping_rows}
    seen = set()
    coverage: Counter[str] = Counter()
    abstraction_total = 0
    nonempty = 0
    max_abstractions = 0
    declined_artifacts = []
    for row in rows:
        if not isinstance(row, dict):
            raise CheckedSliceError("observation row is malformed")
        artifact = row.get("artifact_file")
        if artifact in seen or artifact not in by_artifact:
            raise CheckedSliceError("observation row identity changed")
        seen.add(artifact)
        mapped = by_artifact[artifact]
        if any(row.get(field) != mapped.get(field) for field in ("artifact_file", "fact_id", "family", "partition", "target_definition")):
            raise CheckedSliceError(f"observation mapping changed: {artifact}")
        stream_hash = row.get("stream_sha256")
        require_hash(stream_hash, "source stream")
        if source_root is not None and sha256(source_root / "streams" / artifact) != stream_hash:
            raise CheckedSliceError(f"source stream changed: {artifact}")
        outcome = row.get("outcome")
        coverage[outcome] += 1
        if outcome == "accepted-receipt":
            count = validate_receipt(row.get("receipt"), row)
            abstraction_total += count
            nonempty += count > 0
            max_abstractions = max(max_abstractions, count)
            if "decline" in row:
                raise CheckedSliceError("accepted row also carries a decline")
        elif outcome == "decline:selection":
            declined_artifacts.append(artifact)
            decline = row.get("decline")
            if (
                not isinstance(decline, dict)
                or decline.get("stage") != "selection"
                or "TrustedRetainedClosure" not in str(decline.get("reason"))
                or "receipt" in row
            ):
                raise CheckedSliceError("selection decline contract changed")
        else:
            raise CheckedSliceError(f"unexpected replay outcome: {outcome}")
    expected_coverage = manifest["coverage"]
    if (
        dict(coverage) != observation.get("coverage")
        or coverage != Counter({"accepted-receipt": 128, "decline:selection": 10})
        or expected_coverage["accepted_receipts"] != 128
        or expected_coverage["declined_selection"] != 10
        or abstraction_total != expected_coverage["abstractions"]
        or nonempty != expected_coverage["accepted_with_abstractions"]
        or 128 - nonempty != expected_coverage["accepted_without_abstractions"]
        or max_abstractions != expected_coverage["max_abstractions_per_target"]
        or declined_artifacts != expected_coverage["declined_artifacts"]
    ):
        raise CheckedSliceError("checked replay coverage changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-checked-type-slice-replay"
        or manifest.get("state") != "checked-slice-replay-no-proof-or-ledger-credit"
        or manifest.get("population", {}).get("held_out_inspected") is not False
        or manifest.get("population", {}).get("proof_producers_executed") is not False
        or manifest.get("population", {}).get("ledger_writes") != 0
    ):
        raise CheckedSliceError("manifest contract changed")
    commit = manifest.get("tooling_commit")
    if not isinstance(commit, str) or len(commit) < 9:
        raise CheckedSliceError("tooling commit is malformed")
    tooling_files = manifest.get("tooling_files")
    if not isinstance(tooling_files, list) or len(tooling_files) != 5:
        raise CheckedSliceError("tooling inventory changed")
    for item in tooling_files:
        path = item.get("path")
        if not isinstance(path, str) or sha256_bytes(git_blob(commit, path)) != item.get("sha256"):
            raise CheckedSliceError(f"tooling identity changed: {path}")
    source_root = pathlib.Path(manifest["source_archive"]["root"])
    observation_root = pathlib.Path(manifest["observation_archive"]["root"])
    observation_path = observation_root / manifest["observation_archive"]["file"]
    if not source_root.is_dir() or not observation_root.is_dir():
        raise CheckedSliceError("external replay archive is unavailable")
    if (
        sha256(source_root / "mapping.json") != manifest["source_archive"]["mapping_sha256"]
        or sha256(observation_path) != manifest["observation_archive"]["file_sha256"]
        or observation_path.stat().st_size != manifest["observation_archive"]["bytes"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_root.stat().st_mode) != 0o555
    ):
        raise CheckedSliceError("external replay evidence changed or is mutable")
    mapping = load(source_root / "mapping.json")
    observation = load(observation_path)
    validate_observation(manifest, observation, mapping, source_root)
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_CHECKED_TYPE_SLICE_REPLAY_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "accepted=128|declined=10|held_out=0|proofs=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, CheckedSliceError) as error:
        print(f"autogenesis-checked-type-slice-replay: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
