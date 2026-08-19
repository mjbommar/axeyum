#!/usr/bin/env python3
"""Verify the kernel-backed semantic abstraction debt census."""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-semantic-abstraction-census-v1.json"
PRODUCER_SCRIPT = ROOT / "scripts/check-autogenesis-type-slice-producer-census.py"
SPEC = importlib.util.spec_from_file_location("type_slice_producer_census_base", PRODUCER_SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PRODUCER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PRODUCER
SPEC.loader.exec_module(PRODUCER)

EXPECTED_POPULATION = {
    "abstracted_rows": 114,
    "bindings": 152,
    "source_occurrences": 244,
    "rendered_names": 30,
    "exact_definition_identities": 32,
    "variant_names": ["Int.gcd", "Nat.gcd"],
}
EXPECTED_SHAPES = {
    "predicate-equivalence": {"identities": 5, "bindings": 73},
    "pointwise-function-equation": {"identities": 15, "bindings": 50},
    "nullary-observational-projections": {"identities": 12, "bindings": 29},
}
EXPECTED_TRUSTED = {"theorem": 6346, "axiom": 27, "quotient": 20, "opaque": 7}
EXPECTED_TOOLING = {
    "commit": "efe7f0b70121db45205ad947ea04465e06f0451e",
    "path": "crates/axeyum-lean-import/examples/semantic_abstraction_census.rs",
    "sha256": "0d6c27398c58d508a651fcdd2d5cc1cc0ebe3efaf83aac18c3bf287ccd13ea75",
}
EXPECTED_SOURCE_ARCHIVE = {
    "root": "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1",
    "lean_version": "4.30.0",
    "lean_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
}
EXPECTED_OBSERVATION_ARCHIVE = {
    "root": "/nas3/data/axeyum/autogenesis/semantic-abstraction/efe7f0b70-mathlib-v4.30.0-census-v1",
    "file": "observation.json",
    "bytes": 279971,
    "mode": "0444",
    "file_sha256": "215372dc525a6467b51e598c9ca54d18540cf538a45e4119f8f9bb6098c1ba00",
    "observation_sha256": "3c2a5d670255f9911ba96e4219803dbe7a61838407610785ca82cec78b5c3c6a",
}
HASH_FIELDS = {"source_content_sha256", "instantiated_type_sha256"}


class SemanticCensusError(RuntimeError):
    """The semantic census is absent, mutable, stale, malformed, or overclaimed."""


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
        raise SemanticCensusError(f"{path} is not an object")
    return value


def require_hash(value: Any, context: str) -> None:
    try:
        PRODUCER.require_hash(value, context)
    except PRODUCER.ProducerCensusError as error:
        raise SemanticCensusError(str(error)) from error


def git_blob(commit: str, path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise SemanticCensusError(f"tooling blob is unavailable: {commit}:{path}")
    return result.stdout


def string_list(value: Any, context: str, *, nonempty: bool = False) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) and item for item in value):
        raise SemanticCensusError(f"{context} is not a string inventory")
    if value != sorted(set(value)) or (nonempty and not value):
        raise SemanticCensusError(f"{context} is not sorted, unique, and nonempty")
    return value


def validate_definition(row: Any) -> tuple[str, int, int, Counter[str]]:
    if not isinstance(row, dict):
        raise SemanticCensusError("definition descriptor is malformed")
    name = row.get("name")
    if not isinstance(name, str) or not name:
        raise SemanticCensusError("definition name is malformed")
    for field in HASH_FIELDS:
        require_hash(row.get(field), f"definition {field}")
    universes = string_list(row.get("universe_sha256"), "definition universes")
    for digest in universes:
        require_hash(digest, "definition universe")
    artifacts = string_list(row.get("artifacts"), "definition artifacts", nonempty=True)
    facts = string_list(row.get("facts"), "definition facts", nonempty=True)
    families = string_list(row.get("families"), "definition families", nonempty=True)
    first_artifact = row.get("first_artifact")
    bindings = row.get("bindings")
    occurrences = row.get("source_occurrences")
    if (
        first_artifact not in artifacts
        or not isinstance(bindings, int)
        or bindings != len(artifacts)
        or bindings != len(facts)
        or not isinstance(occurrences, int)
        or occurrences < bindings
        or not families
    ):
        raise SemanticCensusError("definition population identity changed")
    pi_binders = row.get("type_pi_binders")
    lambda_binders = row.get("value_lambda_binders")
    nodes = row.get("value_expression_nodes")
    returns_prop = row.get("returns_prop")
    body_kind = row.get("value_body_kind")
    if (
        not isinstance(pi_binders, int)
        or pi_binders < 0
        or not isinstance(lambda_binders, int)
        or lambda_binders < 0
        or not isinstance(nodes, int)
        or nodes < 1
        or not isinstance(returns_prop, bool)
        or body_kind
        not in {"bvar", "fvar", "sort", "const", "projection", "application", "lambda", "pi", "let", "literal"}
    ):
        raise SemanticCensusError("definition expression shape is malformed")
    expected_shape = (
        "predicate-equivalence"
        if returns_prop
        else "nullary-observational-projections"
        if pi_binders == 0
        else "pointwise-function-equation"
    )
    if row.get("contract_shape") != expected_shape:
        raise SemanticCensusError("contract shape disagrees with checked definition type")
    rewrites = row.get("normalization_rewrites")
    if not isinstance(rewrites, int) or rewrites < 0:
        raise SemanticCensusError("normalization rewrite count is malformed")
    trusted_raw = row.get("trusted_closure")
    if not isinstance(trusted_raw, dict) or not trusted_raw:
        raise SemanticCensusError("trusted implementation closure is absent")
    if not set(trusted_raw) <= {"axiom", "theorem", "opaque", "quotient"}:
        raise SemanticCensusError("trusted closure kind changed")
    trusted = Counter()
    for kind, names in trusted_raw.items():
        trusted[kind] = len(string_list(names, f"trusted {kind}", nonempty=True))
    direct_theorems = string_list(row.get("direct_theorem_dependencies"), "direct theorems")
    axioms = string_list(row.get("axiom_footprint"), "axiom footprint")
    if not set(direct_theorems) <= set(trusted_raw.get("theorem", [])):
        raise SemanticCensusError("direct theorem is absent from trusted closure")
    identity = "|".join(
        [name, row["source_content_sha256"], row["instantiated_type_sha256"], *universes]
    )
    return identity, bindings, occurrences, trusted


def validate_observation(manifest: dict[str, Any], observation: dict[str, Any]) -> None:
    unsigned = dict(observation)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise SemanticCensusError("inner observation identity changed")
    expected_authority = {
        "partitions_inspected": ["development", "train"],
        "held_out_inspected": False,
        "proof_bodies_exposed_to_contracts_or_producers": False,
        "contracts_generated": 0,
        "ledger_writes": 0,
    }
    expected_source = {
        "producer_observation_file_sha256": manifest["producer_observation"]["file_sha256"],
        "producer_observation_sha256": manifest["producer_observation"]["observation_sha256"],
        "type_slice_policy": "contaminated-definition-boundary-auto-param-binders-v3",
        "producer_policy": "type-slice-reflexivity-census-v1",
    }
    population = observation.get("population")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind") != "axeyum-autogenesis-semantic-abstraction-census"
        or observation.get("state") != "diagnostic-no-contract-or-ledger-credit"
        or observation.get("authority") != expected_authority
        or observation.get("source") != expected_source
        or not isinstance(population, dict)
        or {key: population.get(key) for key in EXPECTED_POPULATION} != EXPECTED_POPULATION
        or population.get("bindings_by_contract_shape")
        != {shape: values["bindings"] for shape, values in EXPECTED_SHAPES.items()}
        or claimed != manifest["observation_archive"]["observation_sha256"]
    ):
        raise SemanticCensusError("semantic census contract changed")
    definitions = observation.get("definitions")
    if not isinstance(definitions, list) or len(definitions) != 32:
        raise SemanticCensusError("definition identity population changed")
    identities = set()
    names: defaultdict[str, int] = defaultdict(int)
    shapes: defaultdict[str, dict[str, int]] = defaultdict(lambda: {"identities": 0, "bindings": 0})
    trusted = Counter()
    bindings = 0
    occurrences = 0
    artifacts = set()
    ordering = []
    for row in definitions:
        identity, row_bindings, row_occurrences, row_trusted = validate_definition(row)
        if identity in identities:
            raise SemanticCensusError("definition identity repeats")
        identities.add(identity)
        name = row["name"]
        names[name] += 1
        shape = row["contract_shape"]
        shapes[shape]["identities"] += 1
        shapes[shape]["bindings"] += row_bindings
        trusted.update(row_trusted)
        bindings += row_bindings
        occurrences += row_occurrences
        artifacts.update(row["artifacts"])
        ordering.append((name, row["source_content_sha256"]))
    variants = sorted(name for name, count in names.items() if count > 1)
    if (
        ordering != sorted(ordering)
        or len(names) != 30
        or variants != ["Int.gcd", "Nat.gcd"]
        or dict(shapes) != EXPECTED_SHAPES
        or dict(trusted) != EXPECTED_TRUSTED
        or bindings != 152
        or occurrences != 244
        or len(artifacts) != 114
    ):
        raise SemanticCensusError("semantic abstraction totals changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-semantic-abstraction-census"
        or manifest.get("state") != "diagnostic-no-contract-or-ledger-credit"
        or manifest.get("population") != EXPECTED_POPULATION
        or manifest.get("contract_shapes") != EXPECTED_SHAPES
        or manifest.get("trusted_closure_occurrences") != EXPECTED_TRUSTED
        or manifest.get("source_archive") != EXPECTED_SOURCE_ARCHIVE
        or manifest.get("observation_archive") != EXPECTED_OBSERVATION_ARCHIVE
    ):
        raise SemanticCensusError("manifest contract changed")
    commit = manifest.get("tooling_commit")
    tooling_files = manifest.get("tooling_files")
    if commit != EXPECTED_TOOLING["commit"]:
        raise SemanticCensusError("tooling commit changed")
    if tooling_files != [{"path": EXPECTED_TOOLING["path"], "sha256": EXPECTED_TOOLING["sha256"]}]:
        raise SemanticCensusError("tooling inventory changed")
    item = tooling_files[0]
    path = item.get("path")
    if not isinstance(path, str) or sha256_bytes(git_blob(commit, path)) != item.get("sha256"):
        raise SemanticCensusError("tooling identity changed")
    try:
        producer_manifest = PRODUCER.validate()
    except PRODUCER.ProducerCensusError as error:
        raise SemanticCensusError(f"producer source is invalid: {error}") from error
    producer_root = pathlib.Path(manifest["producer_observation"]["root"])
    producer_path = producer_root / manifest["producer_observation"]["file"]
    if (
        producer_path != pathlib.Path(producer_manifest["observation_archive"]["root"]) / producer_manifest["observation_archive"]["file"]
        or sha256(producer_path) != manifest["producer_observation"]["file_sha256"]
        or producer_manifest["observation_archive"]["observation_sha256"]
        != manifest["producer_observation"]["observation_sha256"]
    ):
        raise SemanticCensusError("producer observation identity changed")
    observation_root = pathlib.Path(manifest["observation_archive"]["root"])
    observation_path = observation_root / manifest["observation_archive"]["file"]
    if (
        not observation_root.is_dir()
        or sha256(observation_path) != manifest["observation_archive"]["file_sha256"]
        or observation_path.stat().st_size != manifest["observation_archive"]["bytes"]
        or stat.S_IMODE(observation_path.stat().st_mode) != 0o444
        or stat.S_IMODE(observation_root.stat().st_mode) != 0o555
    ):
        raise SemanticCensusError("external semantic census changed or is mutable")
    validate_observation(manifest, load(observation_path))
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_SEMANTIC_ABSTRACTION_CENSUS_OK|"
            f"{manifest['observation_archive']['observation_sha256']}|"
            "rows=114|bindings=152|names=30|identities=32|contracts=0|held_out=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, SemanticCensusError) as error:
        print(f"autogenesis-semantic-abstraction-census: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
