#!/usr/bin/env python3
"""Verify the sealed extended-gcd root audit and its no-credit conclusion."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/extended-gcd-root-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-root-audit-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "609241d91-extended-gcd-root-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "8e1622b359f9e0c1418cc139036162787c39843cbdff7229cb997bd7adceaa9f"
PLAN_SHA256 = "2791de5262a079f785985b678842a50661b3d07187e5e980c2e5877ee98b6239"
MANIFEST_SHA256 = "f7a9ad05d609a2fe54da044d5c30c964a53b9432fccf6548ca254026c4a95ab8"
DEPENDENCIES = [
    "Eq.trans",
    "Int.mul_zero",
    "Nat.xgcdAux_val",
    "Nat.xgcd_val",
    "_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P",
    "add_zero",
    "congr",
    "congrArg",
    "eq_self",
    "mul_one",
    "of_eq_true",
    "zero_add",
]


class ExtendedGcdRootAuditResultError(RuntimeError):
    """The evidence identity, measured decline, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdRootAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise ExtendedGcdRootAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise ExtendedGcdRootAuditResultError("measured extended-gcd result changed")
    if (
        result.get("kind") != "axeyum-autogenesis-extended-gcd-root-audit-result"
        or result.get("state")
        != "official-extended-gcd-root-is-propext-bearing-exact-dependency-descent-required"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise ExtendedGcdRootAuditResultError("result producer or pack changed")
    identities = [
        ("extended-gcd.ndjson", 2_497_293, "97d21c35c8b86c425ce850d2774ed8c60a07ae9a7070c21df536e4e503e400fb"),
        ("export.stderr", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("audit-result.json", 1_383, "be141ec98208e0b761ba53272ed89ce961cd8acda08db3df1476a5814140e715"),
        ("audit.stderr", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ]
    for name, size, digest in identities:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise ExtendedGcdRootAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if (
        audit.get("ordered_roots") != ["Nat.gcd_eq_gcd_ab"]
        or audit.get("rows") != [result["row"]]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("input")
        != {
            "path": str(PACK / "extended-gcd.ndjson"),
            "bytes": 2_497_293,
            "sha256": "97d21c35c8b86c425ce850d2774ed8c60a07ae9a7070c21df536e4e503e400fb",
            "stream_axioms": ["Quot.sound", "propext"],
        }
    ):
        raise ExtendedGcdRootAuditResultError("batch measurement changed")
    row = result.get("row", {})
    if (
        row.get("name") != "Nat.gcd_eq_gcd_ab"
        or row.get("declaration_sha256")
        != "e3089f3bbc88369a1449c5da8e0558e07114bd322bf8d6dc29100dd9d425747e"
        or row.get("class") != "propext-bearing"
        or row.get("axiom_footprint")
        != ["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"]
        or row.get("direct_theorem_dependencies") != DEPENDENCIES
        or result.get("summary")
        != {
            "population": 1,
            "empty_footprint": 0,
            "propext_bearing": 1,
            "direct_theorem_dependency_count": 12,
            "coefficient_adapter_authorized": False,
            "exact_dependency_audit_required": True,
        }
    ):
        raise ExtendedGcdRootAuditResultError("decline or dependency frontier changed")
    if result.get("budget") != {
        "exporter_invocations": 1,
        "batch_importer_runs": 1,
        "proof_bearing_stream_reads": 1,
        "retries": 0,
        "reconstruction_source_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    } or result.get("authority") != {
        "proof_terms_rendered": 0,
        "theorem_types_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ExtendedGcdRootAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_ROOT_AUDIT_RESULT_OK|root=Nat.gcd_eq_gcd_ab|"
            "class=propext-bearing|dependencies=12|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdRootAuditResultError,
    ) as error:
        print(f"autogenesis-extended-gcd-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
