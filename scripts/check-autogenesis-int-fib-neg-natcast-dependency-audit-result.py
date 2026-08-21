#!/usr/bin/env python3
"""Verify the sealed 36-root negative-natural Fibonacci audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-natcast-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-natcast-dependency-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-natcast-dependency-audit-v1")
AUDIT = PACK / "audit.json"
MANIFEST = PACK / "manifest.json"
RESULT_SHA256 = "6b06b0ecfc0bb0c1bd6be931c63977a4466eb2dd71412563e2bd16853a9c83d4"


class IntFibNegNatcastDependencyAuditResultError(RuntimeError):
    """The sealed classification or its no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegNatcastDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise IntFibNegNatcastDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise IntFibNegNatcastDependencyAuditResultError("measured natcast result changed")
    if result.get("kind") != "axeyum-autogenesis-int-fib-neg-natcast-dependency-audit-result" or result.get("state") != "transport-clean-parity-and-fib-odd-core-assumption-bearing" or sha256(PLAN) != "6738be781656bff722710679555a4cd2a4beb8b0fb445ecdba46f6dfd1b02bc3" or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or sha256(MANIFEST) != "1c722edb023be56a2ec4232c42b76a97647ee74589267993180eb3c5e424e3dc" or sha256(AUDIT) != "3ab13740a7ce1c9b1bfdbe917ee9976316b0e9f953a74a21ccf74e099a6e9bb2" or AUDIT.stat().st_size != 13_497:
        raise IntFibNegNatcastDependencyAuditResultError("producer or pack changed")
    audit = load(AUDIT)
    rows = audit["rows"]
    empty = [row["name"] for row in rows if row["class"] == "empty-footprint"]
    bearing = [row["name"] for row in rows if row["class"] != "empty-footprint"]
    by_name = {row["name"]: row for row in rows}
    fib_odd = by_name["Int.fib_of_odd"]
    if audit["summary"] != {"population": 36, "class_counts": {"empty-footprint": 18, "other-assumption-bearing": 0, "propext-bearing": 18}, "all_roots_empty": False} or audit["rendered_material"] != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0} or result.get("summary") != {"population": 36, "empty_footprint": 18, "propext_bearing": 18, "other_assumption_bearing": 0} or result.get("empty_footprint_roots") != empty or result.get("assumption_bearing_roots") != bearing:
        raise IntFibNegNatcastDependencyAuditResultError("classification changed")
    expected_fib_odd = {"name": "Int.fib_of_odd", "declaration_sha256": fib_odd["declaration_sha256"], "direct_theorem_dependencies": ["_private.Mathlib.Data.Int.Fib.Basic.0.Int.fib_of_odd._proof_1_2"]}
    if result.get("key_frontier", {}).get("fib_odd") != expected_fib_odd or fib_odd["class"] != "propext-bearing" or result.get("decision") != {"official_natcast_composition_authorized": False, "next_action": "preregister a proof-free statement and footprint qualification of the private Int.fib_of_odd proof root before choosing direct recurrence reconstruction"}:
        raise IntFibNegNatcastDependencyAuditResultError("key frontier or decision changed")
    if result.get("authority", {}).get("ledger_writes") != 0 or result["authority"].get("proof_terms_rendered") != 0 or result["budget"].get("batch_importer_runs") != 1:
        raise IntFibNegNatcastDependencyAuditResultError("budget or authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_NATCAST_DEPENDENCY_AUDIT_RESULT_OK|roots=36|clean=18|bearing=18|next=Int.fib_of_odd|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegNatcastDependencyAuditResultError) as error:
        print(f"autogenesis-int-fib-neg-natcast-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
