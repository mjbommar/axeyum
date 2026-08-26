#!/usr/bin/env python3
"""Fail closed if the imported Nat.ModEq bridge assay loses its boundary."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/nat-modeq-imported-bridge-assay-v1.json"
EXPECTED_FACTS = {
    "F:ml430-nat-add-modeq-left-e3b1fba9",
    "F:ml430-nat-add-modeq-right-e2f11f21",
    "F:ml430-nat-modulus-modeq-zero-fd9af096",
}


def fail(message: str) -> None:
    raise SystemExit(f"nat-modeq-imported-bridge-assay: {message}")


def main() -> None:
    document = json.loads(ARTIFACT.read_text())
    if document.get("schema_version") != 1 or document.get("kind") != "axeyum-autogenesis-nat-modeq-imported-bridge-assay":
        fail("schema identity changed")
    if document.get("state") != "diagnostic-only-no-operation-or-admission-authority":
        fail("diagnostic authority boundary changed")

    adapter = document.get("source_adapter", {})
    adapter_path = ROOT / adapter.get("path", "")
    if not adapter_path.is_file():
        fail("source adapter is absent")
    digest = hashlib.sha256(adapter_path.read_bytes()).hexdigest()
    if digest != adapter.get("sha256"):
        fail("source adapter hash drifted")
    text = adapter_path.read_text()
    if "theorem " in text or ":= by" in text:
        fail("proof-free adapter gained proof material")

    candidates = document.get("candidate_assay", [])
    if len(candidates) != 8 or len({row.get("name") for row in candidates}) != 8:
        fail("candidate population changed")
    contaminated = [row for row in candidates if row.get("axiom_footprint")]
    transportable = [row for row in candidates if row.get("usable") is True]
    if len(contaminated) != 6 or any(row.get("axiom_footprint") != ["propext"] for row in contaminated):
        fail("expected six propext-bearing shortcuts")
    if [row.get("name") for row in transportable] != ["Nat.ModEq.refl"]:
        fail("transportable candidate boundary changed")

    outcomes = document.get("target_outcomes", [])
    if {row.get("fact_id") for row in outcomes} != EXPECTED_FACTS:
        fail("target population changed")
    for row in outcomes:
        if row.get("transported_candidates") != ["Nat.ModEq.refl"]:
            fail(f"{row.get('fact_id')}: transported candidate set changed")
        if row.get("transport_declines") != 7 or row.get("construction_result") != "NoTypedApplication" or row.get("admitted") is not False:
            fail(f"{row.get('fact_id')}: measured decline changed")
        # The assay is an immutable record of an earlier producer failure. Its
        # zero-conversion census is historical, not a mutable count of current
        # ledger status; a later, different operation may therefore settle the
        # target without falsifying this observation.

    census = document.get("census", {})
    expected = {
        "targets": 3,
        "candidate_theorems": 8,
        "candidates_with_nonempty_axiom_footprint": 6,
        "candidates_transportable": 1,
        "targets_converted": 0,
    }
    if census != expected:
        fail("census disagrees with checked rows")
    print("nat-modeq-imported-bridge-assay: ok (3 targets, 8 candidates, 6 propext, 0 conversions)")


if __name__ == "__main__":
    main()
