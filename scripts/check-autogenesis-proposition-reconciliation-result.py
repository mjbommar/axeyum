#!/usr/bin/env python3
"""Fail-closed checker for the six proposition reconciliation events."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PROPOSALS = ROOT / "artifacts/autogenesis/proposition-reconciliation-proposals-v1.json"
RESULT = ROOT / "artifacts/autogenesis/proposition-reconciliation-result-v1.json"
BEFORE = ROOT / "artifacts/autogenesis/open-ranked-proposition-census-v1.json"
AFTER = ROOT / "artifacts/autogenesis/open-ranked-proposition-census-v2.json"
FACTS = ROOT / "artifacts/facts"


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    proposals = json.loads(PROPOSALS.read_text())
    result = json.loads(RESULT.read_text())
    before = json.loads(BEFORE.read_text())
    after = json.loads(AFTER.read_text())
    if result.get("source", {}).get("proposals_sha256") != file_sha256(PROPOSALS):
        raise SystemExit("reconciliation result does not bind the proposals artifact")
    proposal_source = proposals.get("source", {})
    index_path = ROOT / proposal_source.get("kernel_lemma_index_path", "")
    if (
        not index_path.is_file()
        or proposal_source.get("kernel_lemma_index_sha256") != file_sha256(index_path)
    ):
        raise SystemExit("proposals do not bind the archived pre-reconciliation index")
    transactions = {
        row["transaction_sha256"]: row for row in proposals.get("proposals", [])
    }
    events = result.get("events", [])
    if len(transactions) != 6 or len(events) != 6:
        raise SystemExit("expected exactly six proposals and six events")
    reconciled = set()
    for event in events:
        claimed = event.get("event_sha256")
        unsigned = dict(event)
        unsigned.pop("event_sha256", None)
        if claimed != digest(unsigned):
            raise SystemExit("reconciliation event digest is invalid")
        if (
            event.get("kind") != "axeyum-autogenesis-durable-reconciliation-event"
            or event.get("event_type") != "fact-reconciled"
            or event.get("production_credit")
            != {"operation_id": None, "autonomous": False, "classification": "no_operation"}
        ):
            raise SystemExit("event claims admission or production credit")
        identity = event["identity"]
        transaction = transactions.get(identity["transaction_sha256"])
        if transaction is None:
            raise SystemExit("event does not bind one prepared proposal")
        if identity["fact_id"] != transaction["identity"]["fact_id"]:
            raise SystemExit("event fact differs from transaction")
        fact_path = FACTS / f"{identity['fact_id'].replace(':', '-')}.json"
        fact = json.loads(fact_path.read_text())
        if digest(fact) != identity["after_fact_sha256"]:
            raise SystemExit("live fact differs from durable after-state")
        evidence = fact.get("evidence", [])
        if (
            fact.get("epistemic_status") != "proved"
            or fact.get("proof_route") != "kernel-lean"
            or fact.get("axiom_footprint") != []
            or len(evidence) != 1
            or evidence[0].get("kernel_declaration") != identity["native_theorem"]
            or "checker_operation" in evidence[0]
        ):
            raise SystemExit("reconciled fact assurance or production identity is wrong")
        reconciled.add(identity["fact_id"])
    before_matches = {row["fact_id"] for row in before.get("matches", [])}
    excluded = set(after.get("excluded_population_fact_ids", []))
    if reconciled != before_matches or excluded != reconciled:
        raise SystemExit("v1 matches, reconciled facts, and v2 exclusions differ")
    if (
        before["census"]["goal_count"] != 57
        or before["census"]["compatible_pair_count"] != 6
        or after["census"]["goal_count"] != 51
        or after["census"]["compatible_pair_count"] != 0
        or after["census"]["held_out_access_count"] != 0
    ):
        raise SystemExit("pre/post census boundary is not the reviewed 57 -> 51 transition")
    print(
        "AUTOGENESIS_RECONCILIATION_RESULT_OK|facts=6|events=6|"
        "goals=57->51|matches=6->0|operations=0|autonomous=0|held_out=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
