#!/usr/bin/env python3
"""Verify the proof-free qualification of newly ready Nat.gcd_fib_add_self."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-fib-add-self-qualification-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-gcd-fib-add-self-5a92d5e3.json"


class QualificationError(RuntimeError):
    """The candidate, proof-free measurements, or zero-credit authority changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise QualificationError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve(path: str) -> pathlib.Path:
    value = pathlib.Path(path)
    return value if value.is_absolute() else ROOT / value


def exact_row(rows: list[dict[str, Any]], key: str, value: str) -> dict[str, Any]:
    matches = [row for row in rows if row.get(key) == value]
    if len(matches) != 1:
        raise QualificationError(f"expected one {key}={value} row, found {len(matches)}")
    return matches[0]


def validate(manifest: dict[str, Any] | None = None) -> dict[str, Any]:
    manifest = load(MANIFEST) if manifest is None else manifest
    if (
        manifest.get("schema_version") != 1
        or manifest.get("kind")
        != "axeyum-autogenesis-mathlib-nat-gcd-fib-add-self-qualification"
        or manifest.get("state")
        != "newly-ready-exact-equality-qualified-no-proof-credit"
    ):
        raise QualificationError("manifest identity changed")

    inputs = manifest["inputs"]
    loaded: dict[str, dict[str, Any]] = {}
    for name in ("unlock_admission", "reviewed_nursery", "dispatch_baseline", "producer_census"):
        row = inputs[name]
        path = resolve(row["path"])
        if sha256(path) != row["sha256"]:
            raise QualificationError(f"{name} identity changed")
        loaded[name] = load(path)
    stream = inputs["proof_isolated_stream"]
    if sha256(resolve(stream["path"])) != stream["sha256"]:
        raise QualificationError("proof-isolated stream identity changed")
    tooling = inputs["relation_probe"]
    if (
        sha256(resolve(tooling["path"])) != tooling["sha256"]
        or tooling["tooling_commit"]
        != "3dac4f57b11ec19bae23c300a78839b6e4ac48c8"
    ):
        raise QualificationError("relation-probe tooling identity changed")

    candidate = manifest["candidate"]
    fact = load(FACT)
    fact_status = fact.get("epistemic_status")
    fact_evidence = fact.get("evidence")
    live_state_valid = (
        fact_status == "open"
        and fact_evidence == []
        and not any(key in fact for key in ("proof_route", "axiom_footprint"))
    ) or (
        fact_status == "proved"
        and fact.get("proof_route") == "kernel-lean"
        and fact.get("axiom_footprint") == []
        and isinstance(fact_evidence, list)
        and len(fact_evidence) == 1
        and fact_evidence[0].get("kind") == "kernel-term"
        and fact_evidence[0].get("check_status") == "checked"
    )
    if (
        candidate["fact_id"] != "F:ml430-nat-gcd-fib-add-self-5a92d5e3"
        or candidate["candidate_id"]
        != "5a92d5e3a2e1adbd9f94ff325825fa9c3dee0ae5ad082f98754e40f9fc761c70"
        or candidate["source_name"] != "Nat.gcd_fib_add_self"
        or candidate["partition"] != "train"
        or fact.get("formal", {}).get("statement") != candidate["statement"]
        or fact.get("depends_on") != candidate["depends_on"]
        or not live_state_valid
    ):
        raise QualificationError("live candidate identity or monotonic state changed")

    admission = loaded["unlock_admission"]
    if (
        admission.get("state") != "durably-admitted-archived-and-clean-replayed"
        or admission.get("identities", {}).get("admission_event_sha256")
        != candidate["unlock_event_sha256"]
        or admission.get("identities", {}).get("readiness_delta_sha256")
        != candidate["readiness_delta_sha256"]
        or admission.get("result", {}).get("newly_ready") != [candidate["fact_id"]]
    ):
        raise QualificationError("unlock evidence changed")

    nursery = exact_row(
        loaded["reviewed_nursery"]["reviewed_candidates"],
        "candidate_id",
        candidate["candidate_id"],
    )
    if (
        nursery.get("name") != candidate["source_name"]
        or nursery.get("statement") != candidate["statement"]
        or nursery.get("module") != candidate["module"]
        or nursery.get("disposition") != "evaluation-eligible"
    ):
        raise QualificationError("reviewed nursery candidate changed")

    baseline = exact_row(
        loaded["dispatch_baseline"]["rows"], "fact_id", candidate["fact_id"]
    )
    expected_dispatch = {
        "outcome": baseline["outcome"],
        "decline_reason": baseline["decline_reason"],
        "registered_operation_ids": baseline["registered_operation_ids"],
        "executor_budget_consumed": baseline["executor_budget_consumed"],
        "statement_adapter_ready": baseline["statement_adapter_ready"],
        "reflexivity_candidate_checked": baseline["reflexivity_candidate_checked"],
    }
    if manifest["prior_dispatch"] != expected_dispatch:
        raise QualificationError("prior dispatch evidence changed")

    census = exact_row(
        loaded["producer_census"]["rows"], "fact_id", candidate["fact_id"]
    )
    measured = manifest["proof_free_measurement"]
    receipt = census["receipt"]
    proof_search = census["proof_search"]
    abstractions = [
        {
            "source_name": row["source_name"],
            "source_occurrences": row["source_occurrences"],
            "source_content_sha256": row["source_content_sha256"],
        }
        for row in receipt["abstractions"]
    ]
    expected_prior = {
        "name": proof_search["producer"],
        "outcome": census["outcome"],
        "binders": proof_search["binders"],
        "constructed_nodes": proof_search["constructed_nodes"],
        "max_binders": proof_search["max_binders"],
        "max_constructed_nodes": proof_search["max_constructed_nodes"],
        "proof_sha256": proof_search["proof_sha256"],
    }
    if (
        census.get("partition") != "train"
        or census.get("artifact_file") != measured["artifact_file"]
        or census.get("target_definition") != measured["target_definition"]
        or census.get("stream_sha256") != stream["sha256"]
        or receipt.get("receipt_sha256") != measured["type_slice_receipt_sha256"]
        or len(receipt.get("retained", [])) != measured["slice_retained"]
        or abstractions != measured["slice_abstractions"]
        or measured["prior_producer"] != expected_prior
    ):
        raise QualificationError("producer census measurement changed")

    relation = measured["relation_probe"]
    if (
        measured["lean_version"] != "4.30.0"
        or measured["lean_githash"]
        != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        or relation
        != {
            "binders": 2,
            "original_head": "Eq",
            "whnf_head": "Eq",
            "whnf_goal": "Eq.{1} AxNat (AxNat.gcd (AxNat.fib #1) (AxNat.fib (HAdd.hAdd.{0, 0, 0} AxNat AxNat AxNat (instHAdd.{0} AxNat instAddNat) #0 #1))) (AxNat.gcd (AxNat.fib #1) (AxNat.fib #0))",
        }
    ):
        raise QualificationError("relation measurement changed")

    boundary = manifest["qualified_boundary"]
    if (
        boundary.get("classification")
        != "non-reflexive-exact-equality-requiring-mathematical-composition"
        or boundary.get("required_local_constructions")
        != [
            "Fibonacci successor-addition identity",
            "coprime-factor divisibility cancellation",
            "gcd equality from the same divisors",
        ]
        or boundary.get("next_action")
        != "preregister one bounded support-first construction plan before any r091 target submission"
    ):
        raise QualificationError("qualified capability boundary changed")

    if manifest["authority"] != {
        "partitions_inspected": ["train"],
        "held_out_inspected": False,
        "proof_bodies_inspected": False,
        "proof_search_invocations": 0,
        "kernel_submissions": 0,
        "executor_invocations": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise QualificationError("qualification authority changed")
    return manifest


def main() -> int:
    try:
        manifest = validate()
        measured = manifest["proof_free_measurement"]
        print(
            "AUTOGENESIS_NAT_GCD_FIB_ADD_SELF_QUALIFICATION_OK|"
            f"fact={manifest['candidate']['fact_id']}|relation={measured['relation_probe']['whnf_head']}|"
            f"retained={measured['slice_retained']}|abstractions={len(measured['slice_abstractions'])}|"
            "proof_search=0|kernel_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, QualificationError) as error:
        print(f"autogenesis-nat-gcd-fib-add-self-qualification: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
