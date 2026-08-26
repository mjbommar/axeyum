#!/usr/bin/env python3
"""Validate the 3/3 imported Nat.mod behavior-contract family receipt."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/nat-modeq-remainder-contract-v2.json"
EXPECTED_FACTS = {
    "F:ml430-nat-add-modeq-left-e3b1fba9",
    "F:ml430-nat-add-modeq-right-e2f11f21",
    "F:ml430-nat-modulus-modeq-zero-fd9af096",
}
EXPECTED_ROOTS = {
    "Axeyum.Autogenesis.Candidate.NatModRemainder.addModLeft",
    "Axeyum.Autogenesis.Candidate.NatModRemainder.addModRight",
    "Axeyum.Autogenesis.Candidate.NatModRemainder.modSelf",
}


def fail(message: str) -> None:
    raise SystemExit(f"nat-modeq-remainder-contract-v2: {message}")


def main() -> None:
    document = json.loads(ARTIFACT.read_text())
    if document.get("schema_version") != 2 or document.get("kind") != "axeyum-autogenesis-nat-modeq-remainder-contract":
        fail("schema identity changed")
    if document.get("state") != "three-of-three-operation-eligible-not-registered-not-admitted":
        fail("authority boundary changed")

    contract = document.get("contract_source", {})
    source = ROOT / contract.get("path", "")
    if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest() != contract.get("sha256"):
        fail("contract source is absent or drifted")
    if set(contract.get("candidate_roots", [])) != EXPECTED_ROOTS or contract.get("lean_axiom_footprint") != []:
        fail("candidate roots or footprint changed")
    proof_source = source.read_text().split("namespace Axeyum.Autogenesis.Candidate.NatModRemainder", 1)[-1]
    forbidden = ("Nat.mod_self", "Nat.add_mod_left", "Nat.add_mod_right", "Classical", "propext")
    if any(token in proof_source for token in forbidden):
        fail("proof bodies gained a forbidden shortcut")
    for required in ("modCoreGoFuelCongr", "modCoreEqMod", "addModLeft", "addModRight", "modSelf"):
        if f"theorem {required}" not in proof_source:
            fail(f"shared proof spine lost {required}")

    inputs = document.get("external_inputs", [])
    if len(inputs) != 4 or sum(row.get("role") == "candidate-family" for row in inputs) != 1:
        fail("external input population changed")
    if {row.get("fact_id") for row in inputs if row.get("role") == "proof-free-target"} != EXPECTED_FACTS:
        fail("proof-free target population changed")
    for row in inputs:
        if not isinstance(row.get("bytes"), int) or row["bytes"] <= 0:
            fail("external input byte count is absent")
        digest = row.get("sha256", "")
        if len(digest) != 64 or any(char not in "0123456789abcdef" for char in digest):
            fail("external input hash is malformed")

    outcomes = document.get("outcomes", [])
    if len(outcomes) != 3 or {row.get("fact_id") for row in outcomes} != EXPECTED_FACTS:
        fail("outcome population changed")
    for row in outcomes:
        for key, expected in {
            "transported_candidates": 3,
            "transport_added": 2,
            "transport_reused": 1,
            "axiom_footprint": [],
            "theorem_dependencies": 1,
            "target_dependency": False,
            "independently_admitted": True,
        }.items():
            if row.get(key) != expected:
                fail(f"{row.get('fact_id')}: outcome field {key} changed")
        for key in ("goal_sha256", "proof_sha256", "target_content_sha256"):
            identity = row.get(key, "")
            if len(identity) != 64 or any(char not in "0123456789abcdef" for char in identity):
                fail(f"{row.get('fact_id')}: {key} is malformed")
        fact = json.loads((ROOT / "artifacts/facts" / (row["fact_id"].replace(":", "-") + ".json")).read_text())
        if fact.get("epistemic_status") != "open":
            fail(f"{row.get('fact_id')}: target is no longer open; archive or supersede this eligibility receipt")

    if document.get("census") != {
        "frozen_siblings": 3,
        "siblings_converted": 3,
        "remaining_siblings": 0,
        "operation_registration_bar": 3,
        "operation_registration_eligible": True,
        "facts_settled": 0,
    }:
        fail("census disagrees with checked rows")
    print("nat-modeq-remainder-contract-v2: ok (3/3 eligible, empty footprint, 0 facts settled)")


if __name__ == "__main__":
    main()
