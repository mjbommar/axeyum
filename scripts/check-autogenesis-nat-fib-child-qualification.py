#!/usr/bin/env python3
"""Verify the proof-free qualification of the two newly ready Fibonacci children."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-fib-child-qualification-v1.json"
FACTS = ROOT / "artifacts/facts"


class QualificationError(RuntimeError):
    """The qualification inputs, observations, or authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise QualificationError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = load(MANIFEST) if manifest is None else manifest
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-child-qualification"
        or manifest.get("state")
        != "relation-boundary-measured-child-selected-no-proof-credit"
    ):
        raise QualificationError("manifest identity changed")
    tooling = manifest["tooling"]
    if sha256(ROOT / tooling["path"]) != tooling["sha256"]:
        raise QualificationError("probe tooling changed")
    source = manifest["source"]
    census_path = pathlib.Path(source["producer_census"])
    if sha256(census_path) != source["producer_census_sha256"]:
        raise QualificationError("producer census changed")
    census = load(census_path)
    census_rows = {row["fact_id"]: row for row in census["rows"]}
    archive = manifest["observation_archive"]
    archive_root = pathlib.Path(archive["root"])
    if (
        stat.S_IMODE(archive_root.stat().st_mode) != 0o555
        or sha256(archive_root / "SHA256SUMS") != archive["index_sha256"]
    ):
        raise QualificationError("observation archive changed or is mutable")
    observations = {}
    for relative, expected_sha in archive["files"].items():
        path = archive_root / relative
        if sha256(path) != expected_sha or stat.S_IMODE(path.stat().st_mode) != 0o444:
            raise QualificationError(f"archived observation changed: {relative}")
        observations[relative.removesuffix(".json")] = load(path)
    candidates = manifest["candidates"]
    if not isinstance(candidates, list) or len(candidates) != 2:
        raise QualificationError("candidate population changed")
    selected_fact_id = manifest["selection"]["fact_id"]
    if selected_fact_id != candidates[0]["fact_id"]:
        raise QualificationError("selected child changed")
    for candidate in candidates:
        fact = load(FACTS / (candidate["fact_id"].replace("F:", "F-") + ".json"))
        if fact.get("depends_on") != ["F:ml430-nat-fib-add-two-b86e0c82"]:
            raise QualificationError("candidate dependency changed")
        if candidate["fact_id"] == selected_fact_id:
            status = fact.get("epistemic_status")
            if status == "open":
                if fact.get("evidence") != [] or any(
                    key in fact for key in ("proof_route", "axiom_footprint")
                ):
                    raise QualificationError("open selected candidate carries admission fields")
            elif (
                status != "proved"
                or fact.get("proof_route") != "kernel-lean"
                or fact.get("axiom_footprint") != []
                or not isinstance(fact.get("evidence"), list)
                or not fact["evidence"]
                or any(row.get("check_status") != "checked" for row in fact["evidence"])
            ):
                raise QualificationError(
                    "settled selected candidate lacks checked axiom-free kernel evidence"
                )
        elif (
            fact.get("epistemic_status") != "open"
            or fact.get("evidence") != []
            or any(key in fact for key in ("proof_route", "axiom_footprint"))
        ):
            raise QualificationError("deferred candidate ledger state changed")
        for unlock_id in candidate["direct_unlocks"]:
            unlock = load(FACTS / (unlock_id.replace("F:", "F-") + ".json"))
            if unlock.get("depends_on") != [candidate["fact_id"]]:
                raise QualificationError("candidate direct unlock changed")
        stream = pathlib.Path(source["coverage_root"]) / "streams" / candidate[
            "artifact_file"
        ]
        if sha256(stream) != candidate["stream_sha256"]:
            raise QualificationError("candidate stream changed")
        row = census_rows[candidate["fact_id"]]
        abstractions = [item["source_name"] for item in row["receipt"]["abstractions"]]
        if (
            row["outcome"] != candidate["prior_producer_outcome"]
            or row["receipt"]["receipt_sha256"]
            != candidate["type_slice_receipt_sha256"]
            or abstractions != candidate["slice_abstractions"]
            or len(row["receipt"]["retained"]) != candidate["slice_retained"]
        ):
            raise QualificationError("candidate type-slice evidence changed")
        observation = observations[candidate["artifact_file"].removesuffix(".ndjson")]
        if (
            observation.get("authority")
            != {
                "kernel_submissions": 0,
                "ledger_writes": 0,
                "proof_search_invocations": 0,
            }
            or observation.get("source", {}).get("stream_sha256")
            != candidate["stream_sha256"]
            or observation.get("source", {}).get("target_definition")
            != candidate["target_definition"]
            or observation.get("result", {}).get("original_head")
            != candidate["original_head"]
            or observation.get("result", {}).get("whnf_head")
            != candidate["whnf_head"]
        ):
            raise QualificationError("relation probe observation changed")
    authority = manifest["authority"]
    if authority != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "proof_search_invocations": 0,
        "kernel_submissions": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise QualificationError("qualification authority changed")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        selected = manifest["selection"]
        print(
            "AUTOGENESIS_NAT_FIB_CHILD_QUALIFICATION_OK|"
            f"selected={selected['source_name']}|candidates=2|"
            "proof_search=0|kernel_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, QualificationError) as error:
        print(f"autogenesis-nat-fib-child-qualification: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
