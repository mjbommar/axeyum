#!/usr/bin/env python3
"""Verify the declined target-side coprime cancellation root audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-target-cancellation-root-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/coprime-target-cancellation-root-audit-plan-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/coprime_target_support_audit.rs"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "b6bda2a04-coprime-target-root-audit-v1"
)
MANIFEST = PACK / "manifest.json"
DECLINED_FOOTPRINT = ["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"]


class CoprimeRootAuditResultError(RuntimeError):
    """The root evidence, shortcut decline, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CoprimeRootAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    result = canonical if result is None else result
    if result != canonical:
        raise CoprimeRootAuditResultError("measured coprime root audit changed")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-coprime-target-cancellation-root-audit-result"
        or result.get("state")
        != "target-cancellation-shortcut-declined-two-assumption-bearing-roots"
    ):
        raise CoprimeRootAuditResultError("coprime root result identity changed")
    if (
        sha256(PLAN) != "2d90479e4a9fa45fbd2b753e167f48593ef434bf4080abeb885bc0e89b388ff5"
        or sha256(TOOL) != "b6bda2a04af219753a14b4cb1512bae59374d52f36975085c31de99aa990e096"
    ):
        raise CoprimeRootAuditResultError("plan or producing tool identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "9a82ab1d116bb3250881c575cd41b8cfa85aa2105a9c25e34749a747dd842be6"
    ):
        raise CoprimeRootAuditResultError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "proof_bearing_stream": (
            "coprime-roots.ndjson",
            "5d5f7293590ad4f6b43a8bb4cc16fbca4873c2f3ceb0f775dad787d1888d8f9d",
            1162279,
        ),
        "audit_result": (
            "audit-result.json",
            "0950547fa6bb988357c7887694ecc3c3c9782d5f084881001fb37978e4475567",
            2692,
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
            raise CoprimeRootAuditResultError(f"{key} identity or mode changed")
    roots = result["roots"]
    for name in [
        "Nat.Coprime.coprime_dvd_left",
        "Nat.Coprime.dvd_of_dvd_mul_left",
    ]:
        if roots[name]["axiom_footprint"] != DECLINED_FOOTPRINT or roots[name]["accepted"] is not False:
            raise CoprimeRootAuditResultError("assumption-bearing shortcut changed")
    if (
        roots["Nat.Coprime.eq_1"]["axiom_footprint"] != []
        or roots["Nat.Coprime.eq_1"]["accepted"] is not True
    ):
        raise CoprimeRootAuditResultError("empty definition equation changed")
    if result["summary"] != {
        "population": 3,
        "class_counts": {
            "empty-footprint": 1,
            "propext-bearing": 2,
            "other-assumption-bearing": 0,
        },
        "all_roots_empty": False,
        "accepted_target_route": False,
    }:
        raise CoprimeRootAuditResultError("shortcut decision changed")
    if result["budget"] != {
        "exporter_invocations": 1,
        "importer_runs": 1,
        "retries": 0,
        "authored_support_compilations": 0,
        "new_theorem_submissions": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
    }:
        raise CoprimeRootAuditResultError("audit budget changed")
    if result["authority"] != {
        "proof_terms_rendered": 0,
        "theorem_values_rendered": 0,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise CoprimeRootAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_COPRIME_TARGET_ROOT_AUDIT_RESULT_OK|roots=3|empty=1|"
            "declined=2|footprint=Quot+propext|support_submissions=0|"
            "target_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        CoprimeRootAuditResultError,
    ) as error:
        print(f"autogenesis-coprime-target-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
