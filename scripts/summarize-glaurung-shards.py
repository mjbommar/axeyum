#!/usr/bin/env python3
"""Validate and aggregate one complete sharded Glaurung QF_BV run.

The child processes are a memory envelope, not independent samples. This
script therefore proves that their manifests and instance records form an
exact disjoint partition of the pinned parent capture before summing any
validity or performance field. Publication mode additionally requires clean,
reproducible Axeyum source identity and a successful 4 GiB `/usr/bin/time`
record for every child process.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import re
import tempfile
from pathlib import Path
from typing import Any, NoReturn, Sequence


SOURCE_ARTIFACT_VERSION = 31
SUMMARY_SCHEMA = "axeyum-glaurung-qfbv-sharded-summary-v1"
SHARD_SET_SCHEMA = "glaurung-qfbv-shard-set-v1"
PARTITION = "u64::from_be_bytes(sha256[0:8]) modulo shard_count"
STAGE_KEYS = (
    "word_preprocess_s",
    "bit_blast_s",
    "cnf_encode_s",
    "cnf_inprocess_s",
    "solve_s",
    "model_lift_s",
    "model_replay_s",
)
CONFIG_SHARD_FIELDS = {
    "config_hash",
    "corpus",
    "corpus_hash",
    "corpus_manifest",
    "corpus_source",
}
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
TIME_RSS_RE = re.compile(
    r"^\s*Maximum resident set size \(kbytes\): (\d+)\s*$", re.MULTILINE
)
TIME_EXIT_RE = re.compile(r"^\s*Exit status: (\d+)\s*$", re.MULTILINE)


class SummaryError(ValueError):
    """A shard input violates the full-corpus evidence contract."""


def fail(message: str) -> NoReturn:
    raise SummaryError(message)


def require_mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
    return value


def require_list(value: Any, location: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{location} must be a JSON array")
    return value


def require_bool(value: Any, location: str) -> bool:
    if not isinstance(value, bool):
        fail(f"{location} must be a boolean")
    return value


def require_int(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{location} must be an integer")
    return value


def require_number(value: Any, location: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        fail(f"{location} must be a number")
    result = float(value)
    if not math.isfinite(result):
        fail(f"{location} must be finite")
    return result


def require_string(value: Any, location: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{location} must be a non-empty string")
    return value


def require_sha256(value: Any, location: str, *, prefixed: bool = False) -> str:
    text = require_string(value, location)
    digest = text.removeprefix("sha256:") if prefixed else text
    if prefixed and not text.startswith("sha256:"):
        fail(f"{location} must start with `sha256:`")
    if not SHA256_RE.fullmatch(digest):
        fail(f"{location} must contain a lowercase SHA-256 digest")
    return digest


def require_count(value: Any, expected: int, location: str) -> None:
    actual = require_int(value, location)
    if actual != expected:
        fail(f"{location} must be {expected}, got {actual}")


def require_zero(value: Any, location: str) -> None:
    require_count(value, 0, location)


def read_bytes(path: Path) -> bytes:
    try:
        return path.read_bytes()
    except OSError as error:
        fail(f"read {path}: {error}")


def load_json(path: Path) -> tuple[dict[str, Any], bytes]:
    data = read_bytes(path)
    try:
        value = json.loads(
            data,
            parse_constant=lambda token: fail(
                f"parse {path}: non-finite JSON number {token}"
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"parse {path}: {error}")
    return require_mapping(value, str(path)), data


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_hash(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), allow_nan=False
    ).encode()
    return "sha256:" + sha256(encoded)


def load_capture_index(path: Path) -> tuple[dict[str, dict[str, Any]], str]:
    value, data = load_json(path)
    if require_int(value.get("version"), f"{path}: version") != 1:
        fail(f"{path}: only capture index version 1 is supported")
    if value.get("logic") != "QF_BV":
        fail(f"{path}: logic must be QF_BV")
    result: dict[str, dict[str, Any]] = {}
    for index, raw_entry in enumerate(require_list(value.get("files"), f"{path}: files")):
        location = f"{path}: files[{index}]"
        entry = require_mapping(raw_entry, location)
        path_value = require_string(entry.get("path"), f"{location}.path")
        if path_value in result:
            fail(f"{path}: duplicate capture path {path_value}")
        expected = require_string(entry.get("expected"), f"{location}.expected")
        if expected not in {"sat", "unsat"}:
            fail(f"{location}.expected must be sat or unsat")
        tiers = require_list(entry.get("tiers"), f"{location}.tiers")
        if not tiers or any(not isinstance(tier, str) or not tier for tier in tiers):
            fail(f"{location}.tiers must contain non-empty strings")
        result[path_value] = {
            "expected": expected,
            "family": require_string(entry.get("family"), f"{location}.family"),
            "tiers": tiers,
        }
    if not result:
        fail(f"{path}: capture index must not be empty")
    return result, sha256(data)


def validate_shard_set(
    shard_set_path: Path, parent_capture_index: Path
) -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]], dict[str, Any]]:
    value, shard_set_bytes = load_json(shard_set_path)
    if value.get("schema") != SHARD_SET_SCHEMA:
        fail(f"{shard_set_path}: schema must be {SHARD_SET_SCHEMA}")
    if value.get("partition") != PARTITION:
        fail(f"{shard_set_path}: unsupported partition rule")
    count = require_int(value.get("shard_count"), f"{shard_set_path}: shard_count")
    if count <= 1:
        fail(f"{shard_set_path}: shard_count must be greater than one")
    declared_files = require_int(value.get("files"), f"{shard_set_path}: files")
    parent, parent_digest = load_capture_index(parent_capture_index)
    require_count(declared_files, len(parent), f"{shard_set_path}: files")
    declared_parent = require_sha256(
        value.get("parent_capture_index_sha256"),
        f"{shard_set_path}: parent_capture_index_sha256",
    )
    if declared_parent != parent_digest:
        fail(f"{shard_set_path}: parent capture index digest mismatch")

    raw_shards = require_list(value.get("shards"), f"{shard_set_path}: shards")
    require_count(len(raw_shards), count, f"{shard_set_path}: shard list length")
    shards: list[dict[str, Any]] = []
    union: dict[str, tuple[dict[str, Any], int]] = {}
    seen_directories: set[str] = set()
    seen_tiers: set[str] = set()
    root = shard_set_path.parent
    for index, raw_shard in enumerate(raw_shards):
        location = f"{shard_set_path}: shards[{index}]"
        shard = require_mapping(raw_shard, location)
        directory = require_string(shard.get("directory"), f"{location}.directory")
        tier = require_string(shard.get("tier"), f"{location}.tier")
        if directory in seen_directories or tier in seen_tiers:
            fail(f"{location}: shard directories and tiers must be unique")
        seen_directories.add(directory)
        seen_tiers.add(tier)
        expected_name = f"full-shard-{index:02d}-of-{count:02d}"
        if directory != expected_name or tier != expected_name:
            fail(f"{location}: expected deterministic name {expected_name}")
        child_path = root / directory / "capture-index-v1.json"
        child, child_digest = load_capture_index(child_path)
        declared_digest = require_sha256(
            shard.get("capture_index_sha256"), f"{location}.capture_index_sha256"
        )
        if declared_digest != child_digest:
            fail(f"{location}: child capture index digest mismatch")
        require_count(shard.get("files"), len(child), f"{location}.files")
        for query_path, metadata in child.items():
            if query_path in union:
                fail(f"{location}: duplicate path across shards: {query_path}")
            if metadata["tiers"] != [tier]:
                fail(f"{location}: {query_path} must belong only to tier {tier}")
            digest = Path(query_path).stem
            if not SHA256_RE.fullmatch(digest):
                fail(f"{location}: query filename must be a lowercase SHA-256")
            if int(digest[:16], 16) % count != index:
                fail(f"{location}: {query_path} violates the partition rule")
            parent_entry = parent.get(query_path)
            if parent_entry is None:
                fail(f"{location}: {query_path} is absent from the parent capture")
            if (
                metadata["expected"] != parent_entry["expected"]
                or metadata["family"] != parent_entry["family"]
            ):
                fail(f"{location}: {query_path} metadata differs from the parent")
            union[query_path] = (metadata, index)
        shards.append(
            {
                "index": index,
                "directory": directory,
                "tier": tier,
                "files": len(child),
                "capture_index": child,
                "capture_index_sha256": child_digest,
                "capture_index_path": child_path,
            }
        )
    missing = sorted(set(parent) - set(union))
    if missing:
        fail(f"{shard_set_path}: shard union misses parent path {missing[0]}")
    require_count(len(union), declared_files, f"{shard_set_path}: union files")
    identity = {
        "shard_set": shard_set_path,
        "shard_set_sha256": sha256(shard_set_bytes),
        "parent_capture_index": parent_capture_index,
        "parent_capture_index_sha256": parent_digest,
        "files": declared_files,
        "path_set_sha256": canonical_hash(sorted(union)),
    }
    return shards, parent, identity


def validate_determinism(config: dict[str, Any], location: str) -> None:
    profile = require_mapping(config.get("determinism"), f"{location}.determinism")
    if profile.get("profile") != "axeyum-bench-fixed-seeds-v1":
        fail(f"{location}.determinism.profile is unsupported")
    sat = require_mapping(profile.get("sat_bv"), f"{location}.determinism.sat_bv")
    if sat.get("adapter") != "rustsat-batsat":
        fail(f"{location}.determinism.sat_bv.adapter must be rustsat-batsat")
    if require_number(sat.get("random_seed"), f"{location}.random_seed") != 91_648_253:
        fail(f"{location}.determinism.sat_bv.random_seed is not pinned")
    if require_number(sat.get("random_var_freq"), f"{location}.random_var_freq") != 0:
        fail(f"{location}.determinism.sat_bv.random_var_freq must be zero")
    for field in ("random_polarity", "random_initial_activity"):
        if require_bool(sat.get(field), f"{location}.{field}"):
            fail(f"{location}.determinism.sat_bv.{field} must be false")
    z3 = require_mapping(profile.get("z3"), f"{location}.determinism.z3")
    if require_int(z3.get("random_seed"), f"{location}.z3.random_seed") != 0:
        fail(f"{location}.determinism.z3.random_seed must be zero")
    if not require_bool(z3.get("set_explicitly"), f"{location}.z3.set_explicitly"):
        fail(f"{location}.determinism.z3 seed must be explicit")


def validate_config(
    config: dict[str, Any], path: Path, policy: str, allow_exploratory: bool
) -> dict[str, str]:
    location = f"{path}: config"
    expected_mode = "off" if policy == "raw" else "default"
    rewrite = require_mapping(config.get("rewrite"), f"{location}.rewrite")
    if rewrite.get("mode") != expected_mode:
        fail(f"{location}.rewrite.mode must be {expected_mode}")
    if policy == "canonical" and rewrite.get("rule_set") != "axeyum-rewrite-default-v4":
        fail(f"{location}.rewrite.rule_set must be axeyum-rewrite-default-v4")
    if require_int(config.get("jobs"), f"{location}.jobs") != 1:
        fail(f"{location}.jobs must be 1")
    if require_int(config.get("manifest_validation_jobs"), f"{location}.manifest_validation_jobs") != 8:
        fail(f"{location}.manifest_validation_jobs must be 8")
    for field in (
        "compare_z3",
        "require_in_process_z3",
        "require_deterministic_resources",
    ):
        if not require_bool(config.get(field), f"{location}.{field}"):
            fail(f"{location}.{field} must be true")
    reproducible = require_bool(
        config.get("require_reproducible_run"), f"{location}.require_reproducible_run"
    )
    experiment = require_mapping(config.get("experiment"), f"{location}.experiment")
    source = require_mapping(experiment.get("source"), f"{location}.experiment.source")
    dirty = require_bool(source.get("dirty"), f"{location}.experiment.source.dirty")
    if not allow_exploratory and (not reproducible or dirty):
        fail(f"{location}: publication requires reproducible_run=true and dirty=false")
    validate_determinism(config, location)
    resources = require_mapping(config.get("resources"), f"{location}.resources")
    if resources.get("profile") != "axeyum-qfbv-cold-bounded-v1":
        fail(f"{location}.resources.profile is unsupported")
    limits = require_mapping(resources.get("limits"), f"{location}.resources.limits")
    pairs = (
        ("search", "resource_limit"),
        ("dag_nodes", "node_budget"),
        ("cnf_variables", "cnf_variable_budget"),
        ("cnf_clauses", "cnf_clause_budget"),
    )
    for resource_field, config_field in pairs:
        value = require_int(limits.get(resource_field), f"{location}.resources.limits.{resource_field}")
        if value <= 0 or value != require_int(config.get(config_field), f"{location}.{config_field}"):
            fail(f"{location}: resource limit {resource_field} is invalid or inconsistent")
    timeout = require_int(config.get("timeout_ms"), f"{location}.timeout_ms")
    if timeout <= 0 or timeout != require_int(
        resources.get("wall_clock_safety_timeout_ms"),
        f"{location}.resources.wall_clock_safety_timeout_ms",
    ):
        fail(f"{location}: wall-clock safety timeout is invalid or inconsistent")
    return {
        "environment_hash": require_sha256(
            experiment.get("environment_hash"),
            f"{location}.experiment.environment_hash",
            prefixed=True,
        ),
        "source_revision": require_string(
            source.get("revision"), f"{location}.experiment.source.revision"
        ),
        "backend": require_string(config.get("backend"), f"{location}.backend"),
        "compare_backend": require_string(
            config.get("compare_backend"), f"{location}.compare_backend"
        ),
        "dirty": str(dirty).lower(),
        "reproducible": str(reproducible).lower(),
    }


def validate_time_file(path: Path) -> dict[str, int]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        fail(f"read {path}: {error}")
    if "MEM_LIMIT_GB=4" not in text:
        fail(f"{path}: command must record MEM_LIMIT_GB=4")
    rss_matches = TIME_RSS_RE.findall(text)
    exit_matches = TIME_EXIT_RE.findall(text)
    if len(rss_matches) != 1 or len(exit_matches) != 1:
        fail(f"{path}: expected exactly one maximum-RSS and exit-status record")
    exit_status = int(exit_matches[0])
    if exit_status != 0:
        fail(f"{path}: process exit status must be zero")
    rss = int(rss_matches[0])
    if rss <= 0 or rss > 4 * 1024 * 1024:
        fail(f"{path}: maximum RSS must be within the 4 GiB envelope")
    return {"maximum_resident_set_kib": rss, "exit_status": exit_status}


def validate_summary(
    artifact: dict[str, Any], expected_files: int, path: Path
) -> dict[str, Any]:
    summary = require_mapping(artifact.get("summary"), f"{path}: summary")
    require_count(summary.get("files"), expected_files, f"{path}: summary.files")
    require_count(summary.get("decided"), expected_files, f"{path}: summary.decided")
    for field in (
        "unknown",
        "unsupported",
        "errors",
        "disagree",
        "model_replay_failures",
    ):
        require_zero(summary.get(field), f"{path}: summary.{field}")
    sat = require_int(summary.get("sat"), f"{path}: summary.sat")
    unsat = require_int(summary.get("unsat"), f"{path}: summary.unsat")
    if sat < 0 or unsat < 0 or sat + unsat != expected_files:
        fail(f"{path}: sat + unsat must equal shard size")
    manifest = require_mapping(summary.get("manifest"), f"{path}: summary.manifest")
    for field in ("expected", "compared", "agree"):
        require_count(manifest.get(field), expected_files, f"{path}: summary.manifest.{field}")
    require_zero(manifest.get("disagree"), f"{path}: summary.manifest.disagree")
    oracle = require_mapping(summary.get("oracle"), f"{path}: summary.oracle")
    if not require_bool(oracle.get("enabled"), f"{path}: summary.oracle.enabled"):
        fail(f"{path}: oracle must be enabled")
    for field in ("compared", "agree"):
        require_count(oracle.get(field), expected_files, f"{path}: summary.oracle.{field}")
    for field in ("disagree", "skipped"):
        require_zero(oracle.get(field), f"{path}: summary.oracle.{field}")
    layers = require_mapping(summary.get("layer_attribution"), f"{path}: summary.layer_attribution")
    require_count(layers.get("instances"), expected_files, f"{path}: layer_attribution.instances")
    stages = {
        key: require_number(layers.get(key), f"{path}: layer_attribution.{key}")
        for key in STAGE_KEYS
    }
    if any(value < 0 for value in stages.values()):
        fail(f"{path}: stage times must be non-negative")
    pipeline = require_number(layers.get("total_pipeline_s"), f"{path}: layer_attribution.total_pipeline_s")
    if not math.isclose(sum(stages.values()), pipeline, rel_tol=1e-9, abs_tol=1e-12):
        fail(f"{path}: stage times must sum to total_pipeline_s")
    comparison = require_mapping(summary.get("client_comparison"), f"{path}: summary.client_comparison")
    require_count(comparison.get("instances"), expected_files, f"{path}: client_comparison.instances")
    axeyum = require_number(comparison.get("axeyum_total_s"), f"{path}: client_comparison.axeyum_total_s")
    z3 = require_number(comparison.get("z3_total_s"), f"{path}: client_comparison.z3_total_s")
    ratio = require_number(comparison.get("axeyum_over_z3_ratio"), f"{path}: client_comparison.axeyum_over_z3_ratio")
    if z3 <= 0 or not math.isclose(axeyum, pipeline, rel_tol=1e-9, abs_tol=1e-12):
        fail(f"{path}: client totals are invalid")
    if not math.isclose(ratio, axeyum / z3, rel_tol=1e-9, abs_tol=1e-12):
        fail(f"{path}: client ratio does not match its totals")
    rewrite = require_mapping(summary.get("rewrite"), f"{path}: summary.rewrite")
    for field in ("decision_changes", "sat_unsat_conflicts"):
        require_zero(rewrite.get(field), f"{path}: summary.rewrite.{field}")
    construction = require_mapping(layers.get("construction"), f"{path}: construction")
    aig = require_mapping(construction.get("aig"), f"{path}: construction.aig")
    cnf = require_mapping(construction.get("cnf"), f"{path}: construction.cnf")
    counters = {
        "aig_nodes_created": require_int(aig.get("nodes_created"), f"{path}: aig.nodes_created"),
        "cnf_clauses_emitted": require_int(cnf.get("clauses_emitted"), f"{path}: cnf.clauses_emitted"),
        "cnf_variables": sum(
            require_int(instance.get("layer_attribution", {}).get("cnf_variables"), f"{path}: instance.cnf_variables")
            for instance in require_list(artifact.get("instances"), f"{path}: instances")
        ),
    }
    if any(value < 0 for value in counters.values()):
        fail(f"{path}: construction counters must be non-negative")
    return {
        "sat": sat,
        "unsat": unsat,
        "axeyum_total_s": axeyum,
        "z3_total_s": z3,
        "stages": stages,
        "rewrite": {
            field: require_int(rewrite.get(field), f"{path}: summary.rewrite.{field}")
            for field in (
                "applications",
                "changed_instances",
                "decision_changes",
                "decision_matches",
                "sat_unsat_conflicts",
            )
        },
        "construction": counters,
    }


def validate_instances(
    artifact: dict[str, Any], capture_index: dict[str, dict[str, Any]], path: Path
) -> None:
    instances = require_list(artifact.get("instances"), f"{path}: instances")
    require_count(len(instances), len(capture_index), f"{path}: instance count")
    seen: set[str] = set()
    for index, raw_instance in enumerate(instances):
        location = f"{path}: instances[{index}]"
        instance = require_mapping(raw_instance, location)
        manifest = require_mapping(instance.get("corpus_manifest"), f"{location}.corpus_manifest")
        query_path = require_string(manifest.get("path"), f"{location}.corpus_manifest.path")
        if query_path in seen:
            fail(f"{path}: duplicate artifact instance {query_path}")
        seen.add(query_path)
        expected_entry = capture_index.get(query_path)
        if expected_entry is None:
            fail(f"{path}: artifact contains unmanifested path {query_path}")
        expected = require_string(manifest.get("expected"), f"{location}.corpus_manifest.expected")
        outcome = require_string(instance.get("outcome"), f"{location}.outcome")
        if expected != expected_entry["expected"] or outcome != expected:
            fail(f"{path}: {query_path} outcome does not match the capture verdict")
        if manifest.get("family") != expected_entry["family"]:
            fail(f"{path}: {query_path} family does not match the capture index")
        if manifest.get("tiers") != expected_entry["tiers"]:
            fail(f"{path}: {query_path} tier does not match the capture index")
        if not require_bool(manifest.get("decision_compared"), f"{location}.decision_compared"):
            fail(f"{path}: {query_path} was not compared with its manifest verdict")
        if not require_bool(manifest.get("decision_agrees"), f"{location}.decision_agrees"):
            fail(f"{path}: {query_path} disagrees with its manifest verdict")
        oracle = require_mapping(instance.get("oracle"), f"{location}.oracle")
        if oracle.get("outcome") != outcome:
            fail(f"{path}: {query_path} disagrees with the Z3 oracle")
        for field in ("enabled", "decision_compared", "decision_agrees"):
            if not require_bool(oracle.get(field), f"{location}.oracle.{field}"):
                fail(f"{path}: {query_path} oracle field {field} must be true")
        replay = instance.get("model_replay_ms")
        if outcome == "sat" and (replay is None or require_number(replay, f"{location}.model_replay_ms") < 0):
            fail(f"{path}: SAT instance {query_path} lacks original-model replay")
    if seen != set(capture_index):
        missing = sorted(set(capture_index) - seen)
        fail(f"{path}: artifact misses manifested path {missing[0]}")


def normalized_config(config: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(config)
    for field in CONFIG_SHARD_FIELDS:
        result.pop(field, None)
    return result


def summarize(
    shard_set_path: Path,
    parent_capture_index: Path,
    policy: str,
    artifact_paths: Sequence[Path],
    *,
    allow_exploratory: bool = False,
) -> dict[str, Any]:
    shards, _parent, shard_identity = validate_shard_set(
        shard_set_path.resolve(), parent_capture_index.resolve()
    )
    resolved_artifacts = [path.resolve() for path in artifact_paths]
    if len(resolved_artifacts) != len(shards) or len(set(resolved_artifacts)) != len(resolved_artifacts):
        fail("exactly one unique artifact is required for every shard")
    # Match by the deterministic shard filename before parsing so only one
    # large v31 artifact is resident at a time. The selected tier inside each
    # artifact is still validated below; the filename is not trusted as
    # evidence identity.
    artifact_by_name: dict[str, Path] = {}
    for path in resolved_artifacts:
        if path.stem in artifact_by_name:
            fail(f"duplicate artifact filename stem {path.stem}")
        artifact_by_name[path.stem] = path

    expected_config: dict[str, Any] | None = None
    identity: dict[str, str] | None = None
    rows: list[dict[str, Any]] = []
    totals: dict[str, Any] = {
        "files": 0,
        "sat": 0,
        "unsat": 0,
        "axeyum_total_s": 0.0,
        "z3_total_s": 0.0,
        "stages": {key: 0.0 for key in STAGE_KEYS},
        "rewrite": {
            "applications": 0,
            "changed_instances": 0,
            "decision_changes": 0,
            "decision_matches": 0,
            "sat_unsat_conflicts": 0,
        },
        "construction": {
            "aig_nodes_created": 0,
            "cnf_clauses_emitted": 0,
            "cnf_variables": 0,
        },
    }
    for shard in shards:
        tier = shard["tier"]
        path = artifact_by_name.pop(tier, None)
        if path is None:
            fail(f"missing artifact for tier {tier}")
        artifact, artifact_bytes = load_json(path)
        artifact_digest = sha256(artifact_bytes)
        if require_int(artifact.get("version"), f"{path}: version") != SOURCE_ARTIFACT_VERSION:
            fail(f"{path}: artifact version must be {SOURCE_ARTIFACT_VERSION}")
        config = require_mapping(artifact.get("config"), f"{path}: config")
        configured_manifest = require_mapping(
            config.get("corpus_manifest"), f"{path}: config.corpus_manifest"
        )
        selected_tier = require_string(
            configured_manifest.get("selected_tier"), f"{path}: selected_tier"
        )
        if selected_tier != tier:
            fail(f"{path}: configured tier must be {tier}")
        current_identity = validate_config(config, path, policy, allow_exploratory)
        current_config = normalized_config(config)
        if expected_config is None:
            expected_config = current_config
            identity = current_identity
        elif current_config != expected_config or current_identity != identity:
            fail(f"{path}: normalized configuration or source identity differs across shards")
        manifest_path = shard["capture_index_path"].with_name("manifest-v1.json")
        manifest_bytes = read_bytes(manifest_path)
        manifest = require_mapping(config.get("corpus_manifest"), f"{path}: corpus_manifest")
        manifest_hash = require_sha256(
            manifest.get("content_hash"), f"{path}: corpus_manifest.content_hash", prefixed=True
        )
        if manifest_hash != sha256(manifest_bytes):
            fail(f"{path}: configured manifest digest does not match manifest-v1.json")
        require_count(manifest.get("selected_entries"), shard["files"], f"{path}: selected_entries")
        summary = validate_summary(artifact, shard["files"], path)
        validate_instances(artifact, shard["capture_index"], path)
        time_path = path.with_suffix(".time")
        time_record = validate_time_file(time_path)
        row = {
            "index": shard["index"],
            "tier": tier,
            "files": shard["files"],
            "artifact": str(path),
            "artifact_sha256": artifact_digest,
            "time_record": str(time_path),
            "manifest_sha256": manifest_hash,
            "capture_index_sha256": shard["capture_index_sha256"],
            **summary,
            **time_record,
        }
        rows.append(row)
        totals["files"] += shard["files"]
        for field in ("sat", "unsat"):
            totals[field] += summary[field]
        for field in ("axeyum_total_s", "z3_total_s"):
            totals[field] += summary[field]
        for group in ("stages", "rewrite", "construction"):
            for field, value in summary[group].items():
                totals[group][field] += value
    if artifact_by_name:
        fail(f"unexpected artifact {sorted(artifact_by_name)[0]}")
    require_count(totals["files"], shard_identity["files"], "aggregate files")
    if totals["sat"] + totals["unsat"] != totals["files"]:
        fail("aggregate sat + unsat must equal files")
    assert expected_config is not None and identity is not None
    totals["axeyum_over_z3_ratio"] = totals["axeyum_total_s"] / totals["z3_total_s"]
    totals["maximum_resident_set_kib"] = max(
        row["maximum_resident_set_kib"] for row in rows
    )
    totals["publication_ready"] = not allow_exploratory
    return {
        "schema": SUMMARY_SCHEMA,
        "source_artifact_version": SOURCE_ARTIFACT_VERSION,
        "policy": policy,
        "contract": {
            "coverage": "exact disjoint shard union equals the byte-pinned parent capture index",
            "validity": "every query is decided and agrees with its trusted manifest and in-process Z3; every SAT model replays against original assertions",
            "process": "one jobs=1 process per deterministic shard under a recorded hard 4 GiB envelope",
            "timing": "child process stage/client totals are summed; maximum RSS is the maximum child-process peak and is not additive",
            "trust": "Glaurung corpus verdicts and Z3 are untrusted differential evidence; Axeyum model/proof replay remains the acceptance boundary",
        },
        "capture": {
            "shard_set": str(shard_identity["shard_set"]),
            "shard_set_sha256": shard_identity["shard_set_sha256"],
            "parent_capture_index": str(shard_identity["parent_capture_index"]),
            "parent_capture_index_sha256": shard_identity["parent_capture_index_sha256"],
            "path_set_sha256": shard_identity["path_set_sha256"],
            "files": shard_identity["files"],
            "shards": len(shards),
        },
        "identity": {
            **identity,
            "normalized_config_sha256": canonical_hash(expected_config),
        },
        "normalized_config": expected_config,
        "shards": rows,
        "aggregate": totals,
    }


def write_json_atomic(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n"
    temporary: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as handle:
            temporary = handle.name
            handle.write(rendered)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except OSError as error:
        if temporary is not None:
            try:
                os.unlink(temporary)
            except OSError:
                pass
        fail(f"write {path}: {error}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shard-set", required=True, type=Path)
    parser.add_argument("--parent-capture-index", required=True, type=Path)
    parser.add_argument("--policy", required=True, choices=("raw", "canonical"))
    parser.add_argument("--artifact", action="append", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument(
        "--allow-exploratory-source",
        action="store_true",
        help="accept dirty/non-reproducible artifacts but mark the summary non-publishable",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output = args.out.resolve()
    inputs = [path.resolve() for path in args.artifact]
    if output in inputs:
        print("summary output must not overwrite an input artifact", file=os.sys.stderr)
        return 1
    try:
        result = summarize(
            args.shard_set,
            args.parent_capture_index,
            args.policy,
            inputs,
            allow_exploratory=args.allow_exploratory_source,
        )
        write_json_atomic(output, result)
    except SummaryError as error:
        try:
            output.unlink(missing_ok=True)
        except OSError as remove_error:
            print(f"remove stale {output}: {remove_error}", file=os.sys.stderr)
        print(error, file=os.sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
