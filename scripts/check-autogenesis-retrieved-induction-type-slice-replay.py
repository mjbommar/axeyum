#!/usr/bin/env python3
"""Validate the outcome-selected checked type-slice replay artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
AUTO = ROOT / "artifacts/autogenesis"
MAPPING = AUTO / "retrieved-induction-type-slice-input-v1.json"
REPLAY = AUTO / "retrieved-induction-type-slice-replay-v1.json"
TRUSTED = {"axiom", "theorem", "opaque", "quotient"}
RECEIPT_KINDS = {
    "axeyum-proof-free-type-slice-receipt-v1",
    "axeyum-proof-free-type-slice-receipt-v2",
}


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical_digest(value: Any) -> str:
    return digest_bytes(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    )


def validate(
    mapping: dict[str, Any],
    replay: dict[str, Any],
    source_directory: Path | None = None,
) -> dict[str, Any]:
    mapping_rows = mapping.get("rows")
    if (
        mapping.get("kind")
        != "axeyum-autogenesis-retrieved-induction-type-slice-input"
        or mapping.get("state") != "proof-free-source-input"
        or not isinstance(mapping_rows, list)
        or len(mapping_rows) != 25
        or mapping.get("authority", {}).get("held_out_inspected") is not False
        or mapping.get("authority", {}).get("target_outcomes_accessed") is not True
    ):
        raise ValueError("type-slice input authority or population changed")
    unsigned = dict(replay)
    claimed = unsigned.pop("observation_sha256", None)
    if claimed != canonical_digest(unsigned):
        raise ValueError("replay observation digest changed")
    if (
        replay.get("kind") != "axeyum-autogenesis-checked-type-slice-replay"
        or replay.get("state") != "checked-slice-replay-no-proof-or-ledger-credit"
        or replay.get("policy_version")
        != "contaminated-definition-boundary-auto-param-binders-v3"
        or replay.get("coverage") != {"accepted-receipt": 25}
        or replay.get("mapping_sha256") != digest_bytes(MAPPING.read_bytes())
        or replay.get("population_selection")
        != {
            "selection": "measured type-slice-generalization obstruction rows",
            "source_kind": "axeyum-autogenesis-retrieved-induction-type-slice-input",
            "target_outcomes_accessed": True,
        }
    ):
        raise ValueError("replay contract or source binding changed")
    authority = replay.get("authority", {})
    if authority != {
        "held_out_inspected": False,
        "ledger_writes": 0,
        "partitions_inspected": ["development", "train"],
        "proof_bodies_requested": False,
        "proof_producers_executed": False,
        "targets": 25,
    }:
        raise ValueError("replay authority changed")
    expected = {row["artifact_file"]: row for row in mapping_rows}
    rows = replay.get("rows")
    if not isinstance(rows, list) or len(rows) != 25:
        raise ValueError("replay population changed")
    seen: set[str] = set()
    abstractions: dict[str, int] = {}
    normalized = 0
    for row in rows:
        artifact = row.get("artifact_file")
        if artifact in seen or artifact not in expected:
            raise ValueError("replay row identity changed")
        seen.add(artifact)
        mapped = expected[artifact]
        for field in ("fact_id", "family", "partition", "target_definition"):
            if row.get(field) != mapped.get(field):
                raise ValueError(f"replay mapping changed for {artifact}")
        if row.get("outcome") != "accepted-receipt" or "decline" in row:
            raise ValueError(f"type-slice row is not accepted: {artifact}")
        if source_directory is not None:
            source = source_directory / artifact
            if not source.is_file() or digest_bytes(source.read_bytes()) != row.get(
                "stream_sha256"
            ):
                raise ValueError(f"external source stream changed: {artifact}")
        receipt = row.get("receipt")
        if not isinstance(receipt, dict):
            raise TypeError(f"type-slice receipt is absent: {artifact}")
        receipt_unsigned = dict(receipt)
        receipt_claimed = receipt_unsigned.pop("receipt_sha256", None)
        if receipt_claimed != canonical_digest(receipt_unsigned):
            raise ValueError(f"type-slice receipt digest changed: {artifact}")
        if (
            receipt.get("schema_version") not in RECEIPT_KINDS
            or receipt.get("policy_version")
            != "contaminated-definition-boundary-auto-param-binders-v3"
            or receipt.get("specialization_verified") is not True
            or receipt.get("source", {}).get("stream_sha256")
            != row.get("stream_sha256")
            or receipt.get("source", {}).get("target") != row.get("target_definition")
        ):
            raise ValueError(f"type-slice receipt contract changed: {artifact}")
        retained = receipt.get("retained")
        bound = receipt.get("abstractions")
        if not isinstance(retained, list) or any(
            not isinstance(item, dict) or item.get("kind") in TRUSTED
            for item in retained
        ):
            raise ValueError(f"type-slice retained a trusted declaration: {artifact}")
        if not isinstance(bound, list) or not 1 <= len(bound) <= 3:
            raise ValueError(f"type-slice abstraction inventory changed: {artifact}")
        for position, item in enumerate(bound):
            if not isinstance(item, dict) or item.get("binder_position") != position:
                raise ValueError(f"type-slice binder order changed: {artifact}")
            name = item.get("source_name")
            if not isinstance(name, str) or not name:
                raise ValueError(f"type-slice abstraction identity changed: {artifact}")
            abstractions[name] = abstractions.get(name, 0) + 1
        normalization = receipt.get("transport_normalization")
        if normalization is not None:
            normalized += 1
    return {
        "targets": len(rows),
        "accepted": len(rows),
        "normalized_receipts": normalized,
        "distinct_abstractions": len(abstractions),
        "external_streams_checked": len(rows) if source_directory is not None else 0,
    }


_LIVE_MAPPING = json.loads(MAPPING.read_text())


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-directory", type=Path)
    args = parser.parse_args()
    result = validate(_LIVE_MAPPING, json.loads(REPLAY.read_text()), args.source_directory)
    print(
        "RETRIEVED_INDUCTION_TYPE_SLICE_REPLAY|"
        + "|".join(f"{key}={value}" for key, value in result.items())
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
