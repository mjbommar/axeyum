#!/usr/bin/env python3
"""Verify the sealed extended-gcd dependency split and next frontier."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/extended-gcd-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-dependency-audit-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "609241d91-extended-gcd-dependency-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "461eb6066ed5bf8ebd3c07d160c9597d2a4554a7b461fb915666a1c8e2f21459"
PLAN_SHA256 = "c93e5cfa758256112342e9e04459c93d940b958eb4edda688b15a57b35a9c67d"
MANIFEST_SHA256 = "a9177779f2ef4adaf35f4d170c7b2a08eaa1c3a5c76de7ffb10bd43f0baeff49"
CORE = {
    "Nat.xgcdAux_val",
    "Nat.xgcd_val",
    "_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P",
}


class ExtendedGcdDependencyAuditResultError(RuntimeError):
    """The dependency evidence, coefficient split, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise ExtendedGcdDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise ExtendedGcdDependencyAuditResultError("measured dependency result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-extended-gcd-dependency-audit-result"
        or result.get("state")
        != "coefficient-core-is-propext-bearing-xgcd-val-terminal-and-eighteen-novel-dependencies-exposed"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise ExtendedGcdDependencyAuditResultError("result producer or pack changed")
    for name, size, digest in [
        ("audit-result.json", 4_871, "5bea79eb9401647917d3bdf7bb5a1f441ccc4510b271d230efe7a5c6ba7f6775"),
        ("audit.stderr", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ]:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise ExtendedGcdDependencyAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if (
        audit.get("rows") != result.get("rows")
        or audit.get("ordered_roots") != [row["name"] for row in result["rows"]]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        or audit.get("summary")
        != {
            "all_roots_empty": False,
            "class_counts": {
                "empty-footprint": 8,
                "other-assumption-bearing": 0,
                "propext-bearing": 4,
            },
            "population": 12,
        }
    ):
        raise ExtendedGcdDependencyAuditResultError("batch measurement changed")
    rows = {row["name"]: row for row in result["rows"]}
    if set(rows) != set(audit["ordered_roots"]):
        raise ExtendedGcdDependencyAuditResultError("measured population changed")
    if any(rows[name]["class"] != "propext-bearing" for name in CORE):
        raise ExtendedGcdDependencyAuditResultError("coefficient-core split changed")
    if (
        rows["Nat.xgcd_val"]["axiom_footprint"] != ["propext"]
        or rows["Nat.xgcd_val"]["direct_theorem_dependencies"] != []
        or result.get("summary")
        != {
            "population": 12,
            "empty_footprint": 8,
            "propext_bearing": 4,
            "candidate_coefficient_core_empty": 0,
            "candidate_coefficient_core_propext_bearing": 3,
            "xgcd_val_direct_theorem_dependencies": 0,
            "novel_candidate_dependency_count": 18,
            "explicit_extended_gcd_reconstruction_authorized": False,
            "exact_novel_dependency_audit_required": True,
        }
        or len(result.get("novel_candidate_dependencies", [])) != 18
        or len(set(result["novel_candidate_dependencies"])) != 18
    ):
        raise ExtendedGcdDependencyAuditResultError("terminal root or frontier changed")
    measured = set(rows)
    expected_novel: list[str] = []
    for name in ["Nat.xgcdAux_val", "_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P"]:
        for dependency in rows[name]["direct_theorem_dependencies"]:
            if dependency not in measured and dependency not in expected_novel:
                expected_novel.append(dependency)
    if result.get("novel_candidate_dependencies") != expected_novel:
        raise ExtendedGcdDependencyAuditResultError("novel dependency derivation changed")
    if result.get("budget") != {
        "exporter_invocations": 0,
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
        raise ExtendedGcdDependencyAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_DEPENDENCY_AUDIT_RESULT_OK|roots=12|"
            "empty=8|core_propext=3|novel=18|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdDependencyAuditResultError,
    ) as error:
        print(f"autogenesis-extended-gcd-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
