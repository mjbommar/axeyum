#!/usr/bin/env python3
"""Verify that only the generic fix equation contaminates generated gcd."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/generated-gcd-novel-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/generated-gcd-novel-dependency-audit-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-generated-gcd-novel-dependency-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "30698c40a963f6d39880a366cb318bc4da60ae5907957cb9731961fda75ca107"
PLAN_SHA256 = "729aa56b7a35db2545c276cd1619af5de25b8b369e6bbf88be6f870aaa3bee78"
MANIFEST_SHA256 = "911879361c1dabffde75aa997fefb58bd72d7f983c281faf1ca33cb9d955febd"


class GeneratedGcdNovelDependencyAuditResultError(RuntimeError):
    """The measured split, reconstruction boundary, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise GeneratedGcdNovelDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise GeneratedGcdNovelDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise GeneratedGcdNovelDependencyAuditResultError("measured novel result changed")
    if (
        result.get("kind")
        != "axeyum-autogenesis-generated-gcd-novel-dependency-audit-result"
        or result.get("state")
        != "generic-well-founded-fix-equation-is-sole-generated-gcd-assumption-carrier"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise GeneratedGcdNovelDependencyAuditResultError("result producer or pack changed")
    for name, digest, size in [
        (
            "audit-result.json",
            "4428f9a60bb2a0b329316ac707e92b248997264d36876e0869be4ac0cae1613b",
            2_145,
        ),
        (
            "audit.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
    ]:
        path = PACK / name
        if (
            stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != size
            or sha256(path) != digest
        ):
            raise GeneratedGcdNovelDependencyAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if (
        audit.get("rows") != result.get("rows")
        or audit.get("ordered_roots") != [row["name"] for row in result["rows"]]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
    ):
        raise GeneratedGcdNovelDependencyAuditResultError("batch measurement changed")
    bearing = [row for row in result["rows"] if row["axiom_footprint"]]
    empty = [row for row in result["rows"] if not row["axiom_footprint"]]
    if (
        [row["name"] for row in bearing] != ["WellFounded.Nat.fix_eq"]
        or len(empty) != 2
        or result.get("summary")
        != {
            "population": 3,
            "empty_footprint": 2,
            "other_assumption_bearing": 1,
            "sole_assumption_carrier": "WellFounded.Nat.fix_eq",
            "private_termination_proof_empty": True,
            "argument_pusher_empty": True,
            "primitive_reconstruction_plan_authorized": True,
        }
    ):
        raise GeneratedGcdNovelDependencyAuditResultError("sole-carrier decision changed")
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
        raise GeneratedGcdNovelDependencyAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_GENERATED_GCD_NOVEL_DEPENDENCY_AUDIT_RESULT_OK|"
            "roots=3|empty=2|sole_carrier=WellFounded.Nat.fix_eq|"
            "reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        GeneratedGcdNovelDependencyAuditResultError,
    ) as error:
        print(f"autogenesis-generated-gcd-novel-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
