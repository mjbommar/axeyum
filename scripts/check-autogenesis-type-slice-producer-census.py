#!/usr/bin/env python3
"""Verify the fixed-budget proof-free type-slice producer census."""

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
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-type-slice-producer-census-v1.json"
BASE_SCRIPT = ROOT / "scripts/check-autogenesis-auto-param-binder-replay.py"
SPEC = importlib.util.spec_from_file_location("auto_param_binder_replay_base", BASE_SCRIPT)
assert SPEC is not None and SPEC.loader is not None
BASE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = BASE
SPEC.loader.exec_module(BASE)

PRODUCER = "bounded-pi-equality-reflexivity-v1"
PRODUCER_POLICY = "type-slice-reflexivity-census-v1"
EXPECTED_COVERAGE = {
    "admissible-proof": 2,
    "kernel-rejection:candidate-typecheck-failed": 46,
    "producer-decline:binder-budget-exceeded": 1,
    "producer-decline:terminal-not-constant-headed-equality": 40,
    "producer-decline:terminal-not-exact-equality": 49,
}
ADMISSIBLE = {
    "r053.ndjson": "16600053e2afaa0d4d0bfa559fbac367bfeb41b860912f10c236cdcb82e08b53",
    "r070.ndjson": "15725b2125daf99a7f779d218f36de67fe85dc42eaae4e1db23f55e5b628856a",
}


class ProducerCensusError(RuntimeError):
    """The census is absent, mutable, stale, malformed, or overclaimed."""


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
        raise ProducerCensusError(f"{path} is not an object")
    return value


def require_hash(value: Any, context: str) -> None:
    try:
        BASE.require_hash(value, context)
    except BASE.BinderReplayError as error:
        raise ProducerCensusError(str(error)) from error


def git_blob(commit: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise ProducerCensusError(f"tooling blob is unavailable: {commit}:{path}")
    return result.stdout


def validate_mapping(mapping: dict[str, Any]) -> list[dict[str, Any]]:
    try:
        return BASE.validate_mapping(mapping)
    except BASE.BinderReplayError as error:
        raise ProducerCensusError(str(error)) from error


def validate_search(search: Any, outcome: str, artifact: str) -> None:
    if not isinstance(search, dict):
        raise ProducerCensusError("row lacks structured proof search")
    if (
        search.get("producer") != PRODUCER
        or search.get("outcome") != outcome.split(":", 1)[0]
        or search.get("max_binders") != 8
        or search.get("max_constructed_nodes") != 16
    ):
        raise ProducerCensusError("producer identity, outcome, or budget changed")
    reason = outcome.partition(":")[2] or None
    if search.get("reason") != reason:
        raise ProducerCensusError("structured outcome reason changed")
    if outcome.startswith("producer-decline:"):
        if set(search) != {
            "producer",
            "outcome",
            "reason",
            "detail",
            "max_binders",
            "max_constructed_nodes",
        }:
            raise ProducerCensusError("producer decline payload changed")
        detail = search.get("detail")
        if not isinstance(detail, str) or not detail:
            raise ProducerCensusError("producer decline detail is absent")
        expected_detail = {
            "binder-budget-exceeded": "binder budget exceeded",
            "terminal-not-constant-headed-equality": "terminal goal is not constant-headed equality",
            "terminal-not-exact-equality": "terminal goal is not an exact Eq application",
        }[reason]
        if not detail.startswith(expected_detail):
            raise ProducerCensusError("producer decline detail disagrees with reason")
        return
    for field in ("proof_sha256",):
        require_hash(search.get(field), f"proof search {field}")
    binders = search.get("binders")
    nodes = search.get("constructed_nodes")
    if not isinstance(binders, int) or not 0 <= binders <= 8:
        raise ProducerCensusError("constructed proof binder count is invalid")
    if not isinstance(nodes, int) or not 0 < nodes <= 16:
        raise ProducerCensusError("constructed proof node count is invalid")
    if outcome.startswith("kernel-rejection:"):
        detail = search.get("detail")
        if not isinstance(detail, str) or not detail.startswith("DeclarationValueMismatch"):
            raise ProducerCensusError("kernel rejection is not the expected typed refusal")
        return
    if outcome != "admissible-proof" or artifact not in ADMISSIBLE:
        raise ProducerCensusError("unexpected non-decline producer outcome")
    if (
        search.get("proof_sha256") != ADMISSIBLE[artifact]
        or search.get("axioms") != 0
        or search.get("theorem_dependencies") != 0
        or search.get("target_dependency") is not False
        or "detail" in search
    ):
        raise ProducerCensusError("admissible proof identity or assurance changed")


def validate_observation(
    manifest: dict[str, Any],
    observation: dict[str, Any],
    mapping: dict[str, Any],
    source_root: pathlib.Path | None,
) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise ProducerCensusError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["development", "train"],
        "held_out_inspected": False,
        "proof_producers_executed": True,
        "proof_bodies_requested": False,
        "ledger_writes": 0,
        "targets": 138,
    }
    expected_budget = {
        "producer": PRODUCER,
        "max_binders": 8,
        "max_constructed_nodes": 16,
        "producer_invocations": 138,
        "retries": 0,
    }
    if (
        observation.get("schema_version") != 1
        or observation.get("kind") != "axeyum-autogenesis-type-slice-producer-census"
        or observation.get("state") != "diagnostic-fixed-budget-no-ledger-credit"
        or observation.get("policy_version") != BASE.POLICY_VERSION
        or observation.get("producer_policy") != PRODUCER_POLICY
        or observation.get("authority") != expected_authority
        or observation.get("budget") != expected_budget
        or observation.get("coverage") != EXPECTED_COVERAGE
        or observation.get("mapping_sha256") != manifest["source_archive"]["mapping_sha256"]
        or claimed != manifest["observation_archive"]["observation_sha256"]
    ):
        raise ProducerCensusError("producer census contract changed")
    mapping_rows = validate_mapping(mapping)
    rows = observation.get("rows")
    if not isinstance(rows, list) or len(rows) != 138:
        raise ProducerCensusError("observation population changed")
    by_artifact = {row["artifact_file"]: row for row in mapping_rows}
    seen: set[str] = set()
    outcomes: Counter[str] = Counter()
    schemas: Counter[str] = Counter()
    changed: Counter[str] = Counter()
    normalized_artifacts: set[str] = set()
    abstractions = 0
    rewrites = 0
    abstracted_rows = 0
    admissible_abstracted = 0
    for row in rows:
        if not isinstance(row, dict):
            raise ProducerCensusError("observation row is malformed")
        artifact = row.get("artifact_file")
        if artifact in seen or artifact not in by_artifact:
            raise ProducerCensusError("observation row identity changed")
        seen.add(artifact)
        mapped = by_artifact[artifact]
        for field in ("artifact_file", "fact_id", "family", "partition", "target_definition"):
            if row.get(field) != mapped.get(field):
                raise ProducerCensusError(f"observation mapping changed: {artifact}")
        require_hash(row.get("stream_sha256"), "source stream")
        if source_root is not None and sha256(source_root / "streams" / artifact) != row["stream_sha256"]:
            raise ProducerCensusError(f"source stream changed: {artifact}")
        outcome = row.get("outcome")
        if outcome not in EXPECTED_COVERAGE:
            raise ProducerCensusError(f"unexpected producer outcome: {outcome}")
        outcomes[outcome] += 1
        validate_search(row.get("proof_search"), outcome, artifact)
        receipt = row.get("receipt")
        try:
            count, row_changed, row_rewrites = BASE.validate_receipt(receipt, row)
        except BASE.BinderReplayError as error:
            raise ProducerCensusError(str(error)) from error
        schemas[receipt["schema_version"]] += 1
        abstractions += count
        abstracted_rows += count > 0
        admissible_abstracted += count > 0 and outcome == "admissible-proof"
        rewrites += row_rewrites
        changed.update(row_changed)
        if row_changed:
            normalized_artifacts.add(artifact)
    if (
        dict(outcomes) != EXPECTED_COVERAGE
        or schemas != Counter({BASE.V1_SCHEMA: 128, BASE.V2_SCHEMA: 10})
        or abstractions != 152
        or abstracted_rows != 114
        or admissible_abstracted != 0
        or rewrites != 164
        or changed != BASE.EXPECTED_DECLARATIONS
        or normalized_artifacts != BASE.NORMALIZED_ARTIFACTS
        or {row["artifact_file"] for row in rows if row["outcome"] == "admissible-proof"}
        != set(ADMISSIBLE)
    ):
        raise ProducerCensusError("producer census totals changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-type-slice-producer-census"
        or manifest.get("state") != "diagnostic-fixed-budget-no-ledger-credit"
        or manifest.get("population") != {
            "train_development": 138,
            "held_out_inspected": False,
            "proof_bodies_requested": False,
            "ledger_writes": 0,
        }
        or manifest.get("producer") != {
            "policy": PRODUCER_POLICY,
            "operation": PRODUCER,
            "max_binders": 8,
            "max_constructed_nodes": 16,
            "invocations": 138,
            "retries": 0,
        }
        or manifest.get("slice_population") != {
            "exact_without_abstractions": 24,
            "semantically_abstracted": 114,
            "definition_abstractions": 152,
            "admissible_exact": 2,
            "admissible_abstracted": 0,
        }
        or manifest.get("coverage") != EXPECTED_COVERAGE
        or manifest.get("admissible_artifacts") != sorted(ADMISSIBLE)
    ):
        raise ProducerCensusError("manifest contract changed")
    commit = manifest.get("tooling_commit")
    if not isinstance(commit, str) or len(commit) != 40:
        raise ProducerCensusError("tooling commit is malformed")
    tooling_files = manifest.get("tooling_files")
    if not isinstance(tooling_files, list) or len(tooling_files) != 2:
        raise ProducerCensusError("tooling inventory changed")
    for item in tooling_files:
        path = item.get("path")
        if not isinstance(path, str) or sha256_bytes(git_blob(commit, path)) != item.get("sha256"):
            raise ProducerCensusError(f"tooling identity changed: {path}")
    source_root = pathlib.Path(manifest["source_archive"]["root"])
    observation_root = pathlib.Path(manifest["observation_archive"]["root"])
    observation_path = observation_root / manifest["observation_archive"]["file"]
    regression = manifest["observation_archive"].get("default_regression")
    expected_regression = {
        "file": "default-observation.json",
        "bytes": 2_151_767,
        "mode": "0444",
        "file_sha256": "969b53a44ed31166b94c611af406ab46c07f5be2b7e1aa9a5ceff1aac78dc5c5",
        "observation_sha256": "49c36e75fcaedef1f76ee1b99268903cc2a10192a549c8b835acf4e1c1f181ec",
    }
    if regression != expected_regression:
        raise ProducerCensusError("default-route regression identity changed")
    regression_path = observation_root / regression["file"]
    if not source_root.is_dir() or not observation_root.is_dir():
        raise ProducerCensusError("external census archive is unavailable")
    if (
        sha256(source_root / "mapping.json") != manifest["source_archive"]["mapping_sha256"]
        or sha256(observation_path) != manifest["observation_archive"]["file_sha256"]
        or observation_path.stat().st_size != manifest["observation_archive"]["bytes"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or sha256(regression_path) != regression["file_sha256"]
        or regression_path.stat().st_size != regression["bytes"]
        or stat.S_IMODE(regression_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_root.stat().st_mode) != 0o555
    ):
        raise ProducerCensusError("external producer evidence changed or is mutable")
    validate_observation(
        manifest,
        load(observation_path),
        load(source_root / "mapping.json"),
        source_root,
    )
    baseline_manifest = {
        "source_archive": {"mapping_sha256": manifest["source_archive"]["mapping_sha256"]},
        "observation_archive": {"observation_sha256": regression["observation_sha256"]},
        "coverage": {
            "accepted_receipts": 138,
            "declined_selection": 0,
            "exact_v1_receipts": 128,
            "normalized_v2_receipts": 10,
            "abstractions": 152,
            "rewritten_occurrences": 164,
            "normalized_artifacts": sorted(BASE.NORMALIZED_ARTIFACTS),
        },
    }
    try:
        BASE.validate_observation(
            baseline_manifest,
            load(regression_path),
            load(source_root / "mapping.json"),
            source_root,
        )
    except BASE.BinderReplayError as error:
        raise ProducerCensusError(f"default route regressed: {error}") from error
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_TYPE_SLICE_PRODUCER_CENSUS_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "admissible=2|kernel_rejections=46|producer_declines=90|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ProducerCensusError) as error:
        print(f"autogenesis-type-slice-producer-census: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
