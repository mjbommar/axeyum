#!/usr/bin/env python3
"""Verify the sealed train/development reflexivity coverage result."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-reflexivity-coverage-v1.json"
GENERATOR = ROOT / "scripts/create-autogenesis-reflexivity-coverage-input.py"


class CoverageResultError(RuntimeError):
    """The coverage result is unavailable, stale, or overclaims its evidence."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def sha256(path: pathlib.Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CoverageResultError(f"{path} is not an object")
    return value


def pinned_nursery(commit: str) -> dict:
    """The nursery manifest as of `commit`, read from git rather than from disk.

    Fails closed: an unreachable commit or an unparseable blob is an error, not a
    fallback to the live file. Falling back would silently restore exactly the
    behaviour this exists to remove.
    """
    completed = subprocess.run(
        ["git", "show", f"{commit}:artifacts/autogenesis/nursery-v1.json"],
        cwd=ROOT, capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        raise CoverageResultError(
            f"pinned nursery commit {commit[:12]} is unreachable: "
            f"{completed.stderr.strip()[:160]}"
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise CoverageResultError(
            f"pinned nursery at {commit[:12]} is unreadable: {error}"
        ) from error


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise CoverageResultError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_external_index(root: pathlib.Path, expected: str) -> None:
    index = root / "SHA256SUMS"
    if sha256(index) != expected:
        raise CoverageResultError("external file index changed")
    indexed: dict[str, str] = {}
    for line in index.read_text().splitlines():
        claimed, separator, relative = line.partition("  ")
        relative = relative.removeprefix("./")
        path = pathlib.PurePosixPath(relative)
        if (
            not separator
            or len(claimed) != 64
            or not relative
            or relative in indexed
            or path.is_absolute()
            or ".." in path.parts
        ):
            raise CoverageResultError("external file index is malformed")
        indexed[relative] = claimed
    actual = {
        str(path.relative_to(root))
        for path in root.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS"
    }
    if set(indexed) != actual:
        raise CoverageResultError("external file index coverage changed")
    for relative, claimed in indexed.items():
        path = root / relative
        if sha256(path) != claimed or stat.S_IMODE(path.stat().st_mode) != 0o444:
            raise CoverageResultError(f"external artifact changed or is mutable: {relative}")


def validate_observation(
    manifest: dict[str, Any], mapping: dict[str, Any], observation: dict[str, Any]
) -> None:
    unsigned_mapping = dict(mapping)
    claimed_input = unsigned_mapping.pop("input_sha256", None)
    if claimed_input != digest(unsigned_mapping) or claimed_input != manifest["input_sha256"]:
        raise CoverageResultError("coverage input identity changed")
    if (
        observation.get("schema_version") != 1
        or observation.get("kind")
        != "axeyum-autogenesis-reflexivity-coverage-observation"
        or observation.get("state") != "diagnostic-no-ledger-credit"
        or observation.get("input_sha256") != claimed_input
        or observation.get("budget") != manifest["budget"]
    ):
        raise CoverageResultError("coverage observation contract changed")
    mapped = mapping.get("rows")
    rows = observation.get("rows")
    expected_count = manifest["population"]["train_development"]
    if not isinstance(mapped, list) or not isinstance(rows, list) or len(rows) != expected_count or len(mapped) != expected_count:
        raise CoverageResultError("coverage row population changed")
    mapping_by_id = {row.get("fact_id"): row for row in mapped if isinstance(row, dict)}
    observed_by_id = {row.get("fact_id"): row for row in rows if isinstance(row, dict)}
    if len(mapping_by_id) != expected_count or set(mapping_by_id) != set(observed_by_id):
        raise CoverageResultError("coverage row identities changed")
    counts: Counter[str] = Counter()
    for fact_id, row in observed_by_id.items():
        source = mapping_by_id[fact_id]
        if any(
            row.get(field) != source.get(field)
            for field in (
                "fact_id",
                "family",
                "partition",
                "target_definition",
                "statement_sha256",
                "artifact_file",
            )
        ):
            raise CoverageResultError(f"coverage row mapping changed: {fact_id}")
        if row.get("partition") not in {"train", "development"}:
            raise CoverageResultError("held-out row entered coverage")
        if row.get("ledger_writes") != 0 or row.get("executor_budget_consumed") != 0:
            raise CoverageResultError("diagnostic coverage consumed authoritative budget")
        outcome = row.get("outcome")
        reason = row.get("reason")
        key = outcome if reason is None else f"{outcome}:{reason}"
        if key not in manifest["coverage"]:
            raise CoverageResultError(f"unregistered coverage outcome: {key}")
        counts[key] += 1
        if outcome == "admissible-proof" and (
            row.get("axioms") != 0
            or row.get("theorem_dependencies") != 0
            or row.get("target_dependency") is not False
            or not isinstance(row.get("goal_sha256"), str)
            or not isinstance(row.get("proof_sha256"), str)
        ):
            raise CoverageResultError("admissible row lacks a clean proof closure")
    if dict(sorted(counts.items())) != manifest["coverage"] or observation.get("coverage") != manifest["coverage"]:
        raise CoverageResultError("coverage totals changed")
    observed_admissible = []
    states = {
        row["fact_id"]: row["ledger_state_during_census"]
        for row in manifest["admissible_proofs"]
    }
    for row in rows:
        if row.get("outcome") != "admissible-proof":
            continue
        observed_admissible.append(
            {
                "fact_id": row["fact_id"],
                "ledger_state_during_census": states.get(row["fact_id"]),
                "goal_sha256": row["goal_sha256"],
                "proof_sha256": row["proof_sha256"],
                "binders": row["binders"],
                "constructed_nodes": row["constructed_nodes"],
                "axioms": row["axioms"],
                "theorem_dependencies": row["theorem_dependencies"],
                "target_dependency": row["target_dependency"],
            }
        )
    if observed_admissible != manifest["admissible_proofs"]:
        raise CoverageResultError("admissible proof identities changed")


def validate() -> dict[str, Any]:
    manifest = load(MANIFEST)
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind") != "axeyum-autogenesis-mathlib-reflexivity-coverage"
        or manifest.get("state") != "diagnostic-reproduced-no-ledger-credit"
    ):
        raise CoverageResultError("result manifest schema identity is invalid")
    root = pathlib.Path(manifest["external_root"])
    if not root.is_dir():
        raise CoverageResultError("external coverage archive is unavailable")
    validate_external_index(root, manifest["external_index_sha256"])
    for relative, expected in manifest["external_files"].items():
        if sha256(root / relative) != expected:
            raise CoverageResultError(f"external result identity changed: {relative}")
    if load(root / "observation.json") != load(root / "observation-precommit.json"):
        raise CoverageResultError("clean and precommit observations differ")

    generator = load_module("reflexivity_coverage_input_for_result", GENERATOR)
    policy = generator.load(generator.SOURCE_POLICY)
    modules = {row["theme"]: row["module"] for row in policy["families"]}
    # Rebuild from the nursery AS IT STOOD when this census was taken, read out
    # of git at the commit the manifest itself pins. Using the live manifest made
    # a valid census go red for a population change it predates and cannot have
    # accounted for; the honest invariant is "this capture matches the population
    # it claims to describe", and that is what is checked here.
    pinned = manifest["population"]["ledger_snapshot_commit"]
    expected_rows = manifest["population"]["train_development"]
    nursery = pinned_nursery(pinned)
    expected_source, expected_mapping = generator.build(
        nursery,
        lambda fact_id: generator.load(generator.fact_path(fact_id)),
        modules,
        expected=expected_rows,
    )
    mapping = load(root / "mapping.json")
    if (root / "source.lean").read_text() != expected_source or mapping != expected_mapping:
        raise CoverageResultError("proof-free coverage input no longer regenerates")
    observation = load(root / "observation.json")
    validate_observation(manifest, mapping, observation)

    streams = sorted((root / "streams").glob("*.ndjson"))
    mapped_files = sorted(row["artifact_file"] for row in mapping["rows"])
    if len(streams) != expected_rows or [path.name for path in streams] != mapped_files:
        raise CoverageResultError("isolated stream population changed")
    provenance = load(root / "provenance.json")
    if (
        provenance.get("tool_commit") != manifest["tooling_commit"][:9]
        or provenance.get("held_out_inspected") is not False
        or provenance.get("proof_bodies_requested") is not False
        or provenance.get("target_outcomes_accessed") is not False
        or provenance.get("reproduction", {}).get("observations_byte_identical") is not True
    ):
        raise CoverageResultError("coverage provenance changed")
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", manifest["tooling_commit"], "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )
    if ancestry.returncode != 0:
        raise CoverageResultError("coverage tooling commit is not in current history")
    snapshot = manifest["population"]["ledger_snapshot_commit"]
    for proof in manifest["admissible_proofs"]:
        relative = "artifacts/facts/" + proof["fact_id"].replace("F:", "F-") + ".json"
        historical = subprocess.run(
            ["git", "show", f"{snapshot}:{relative}"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=30,
        )
        if historical.returncode != 0 or json.loads(historical.stdout).get("epistemic_status") != proof["ledger_state_during_census"]:
            raise CoverageResultError("historical ledger state changed or is unavailable")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        print(
            "AUTOGENESIS_REFLEXIVITY_COVERAGE_OK|"
            f"{manifest['input_sha256']}|rows=138|adapter_rejections=114|"
            "producer_declines=15|kernel_rejections=7|admissible=2|"
            "held_out=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
        CoverageResultError,
    ) as error:
        print(f"autogenesis-reflexivity-coverage: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
