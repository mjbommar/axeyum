#!/usr/bin/env python3
"""Verify the one-pass public Euclidean equation carrier audit result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/euclidean-public-equation-carrier-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/euclidean-public-equation-carrier-audit-plan-v1.json"
TOOL = ROOT / (
    "crates/axeyum-lean-import/examples/euclidean_public_equation_carrier_audit.rs"
)
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "3bd0073ba-public-equation-carrier-audit-v1"
)
MANIFEST = PACK / "manifest.json"
CARRIERS = [
    "Nat.modCore_eq",
    "Nat.modCore_eq_mod",
    "and_false",
    "and_self",
    "eq_false",
    "eq_self",
    "eq_true",
    "false_and",
    "ite_cond_eq_false",
    "ite_cond_eq_true",
]


class EquationCarrierAuditResultError(RuntimeError):
    """The producing tool, exact result, carrier set, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise EquationCarrierAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != "544bde51a25e42f309ef7fecd1dae521527cf4efd2b1b01dccca9c0f07556edd":
        raise EquationCarrierAuditResultError("tracked audit result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise EquationCarrierAuditResultError("measured equation carrier audit changed")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-public-equation-carrier-audit-result"
        or result.get("state")
        != "public-equation-direct-closure-classified-no-replacement-authority"
    ):
        raise EquationCarrierAuditResultError("equation carrier result identity changed")
    if (
        sha256(PLAN) != "9dd589df594ee950f2f81faa23f3e5622d2e0ac1e1ffd5bedaff9edcfb1903ec"
        or sha256(TOOL) != "3bd0073ba7bba09f7adf337b4585e4ba6c2e75f195e9db436fe5cfa0dc496f9b"
    ):
        raise EquationCarrierAuditResultError("plan or producing tool identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "d057571a94427c83449db1cd973618e1affdd19170db551b26f388acdaa56ac8"
    ):
        raise EquationCarrierAuditResultError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "audit_result": (
            "audit-result.json",
            "544bde51a25e42f309ef7fecd1dae521527cf4efd2b1b01dccca9c0f07556edd",
            8795,
        ),
        "audit_stderr": (
            "audit.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
    }.items():
        row = manifest[key]
        path = PACK / row["path"]
        if (
            row.get("path") != expected[0]
            or row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise EquationCarrierAuditResultError(f"{key} identity or mode changed")
    rows = result["rows"]
    carriers = [row["name"] for row in rows if row.get("class") == "propext-bearing"]
    if carriers != CARRIERS:
        raise EquationCarrierAuditResultError("child carrier set changed")
    private_fuel = next(
        row
        for row in rows
        if row["name"]
        == "_private.Init.Data.Nat.Div.Basic.0.Nat.div.go.fuel_congr"
    )
    if private_fuel["class"] != "empty-footprint" or private_fuel["axiom_footprint"] != []:
        raise EquationCarrierAuditResultError("private quotient fuel congruence changed")
    if result["summary"] != {
        "class_counts": {
            "empty-footprint": 13,
            "other-assumption-bearing": 0,
            "propext-bearing": 10,
        },
        "population": 23,
    }:
        raise EquationCarrierAuditResultError("audit aggregate changed")
    if result["authority"] != {
        "evaluation_credit": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
        "fact_status_changes": 0,
        "importer_runs": 1,
        "ledger_writes": 0,
        "new_authored_theorem_submissions": 0,
        "proof_bearing_stream_reads": 1,
        "proof_terms_rendered": 0,
        "replacement_source_compilations": 0,
        "retries": 0,
        "support_theorem_credit": 0,
        "theorem_values_rendered": 0,
    }:
        raise EquationCarrierAuditResultError("no-replacement authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_EQUATION_CARRIER_AUDIT_RESULT_OK|"
            "population=23|empty=13|propext=10|private_div_fuel=empty|"
            "importer_runs=1/1|replacements=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        StopIteration,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        EquationCarrierAuditResultError,
    ) as error:
        print(f"autogenesis-euclidean-equation-carrier-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
