#!/usr/bin/env python3
"""Fail closed if the first imported Nat.mod behavior contract loses its boundary."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/nat-modeq-remainder-contract-v1.json"
EXPECTED_FACT = "F:ml430-nat-modulus-modeq-zero-fd9af096"


def fail(message: str) -> None:
    raise SystemExit(f"nat-modeq-remainder-contract: {message}")


def main() -> None:
    document = json.loads(ARTIFACT.read_text())
    if document.get("schema_version") != 1 or document.get("kind") != "axeyum-autogenesis-nat-modeq-remainder-contract":
        fail("schema identity changed")
    if document.get("state") != "one-of-three-diagnostic-no-operation-or-admission-authority":
        fail("authority boundary changed")

    contract = document.get("contract_source", {})
    source = ROOT / contract.get("path", "")
    if not source.is_file():
        fail("contract source is absent")
    if hashlib.sha256(source.read_bytes()).hexdigest() != contract.get("sha256"):
        fail("contract source hash drifted")
    if contract.get("lean_axiom_footprint") != []:
        fail("contract is not empty-footprint")
    text = source.read_text()
    proof = text.split("theorem modSelf", 1)[-1]
    forbidden = ("Nat.mod_self", "Nat.add_mod_left", "Nat.add_mod_right", "Classical", "propext")
    if any(token in proof for token in forbidden):
        fail("contract source gained a forbidden shortcut")
    required = ("Nat.mod.eq_def", "unfold Nat.modCore", "unfold Nat.modCore.go")
    if any(token not in text for token in required):
        fail("implementation-local proof spine changed")

    inputs = document.get("external_inputs", [])
    if len(inputs) != 2 or {row.get("role") for row in inputs} != {"candidate", "proof-free-target"}:
        fail("external input population changed")
    for row in inputs:
        if not isinstance(row.get("bytes"), int) or row["bytes"] <= 0:
            fail("external input byte count is absent")
        digest = row.get("sha256", "")
        if len(digest) != 64 or any(char not in "0123456789abcdef" for char in digest):
            fail("external input hash is malformed")

    outcome = document.get("outcome", {})
    if outcome.get("fact_id") != EXPECTED_FACT:
        fail("target identity changed")
    required_outcome = {
        "transported": True,
        "transport_added": 1,
        "transport_reused": 0,
        "binders_used": 1,
        "application_depth": 1,
        "terms_considered": 3,
        "axiom_footprint": [],
        "target_dependency": False,
        "independently_admitted": True,
    }
    for key, expected in required_outcome.items():
        if outcome.get(key) != expected:
            fail(f"outcome field {key} changed")

    fact = json.loads((ROOT / "artifacts/facts" / (EXPECTED_FACT.replace(":", "-") + ".json")).read_text())
    if fact.get("epistemic_status") != "open":
        fail("diagnostic target is no longer open; regenerate or archive the receipt")
    if document.get("census") != {
        "frozen_siblings": 3,
        "siblings_converted": 1,
        "remaining_siblings": 2,
        "operation_registration_bar": 3,
    }:
        fail("census disagrees with the checked outcome")
    print("nat-modeq-remainder-contract: ok (1/3 converted, empty footprint, no authority)")


if __name__ == "__main__":
    main()
