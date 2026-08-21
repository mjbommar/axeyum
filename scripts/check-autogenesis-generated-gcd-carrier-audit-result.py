#!/usr/bin/env python3
"""Verify the generated gcd carrier's exact novel frontier."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/generated-gcd-carrier-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/generated-gcd-carrier-audit-plan-v1.json"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-generated-gcd-carrier-audit-v1"
)
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit-result.json"
RESULT_SHA256 = "73fe1e77a36d48b2906271607866f4bee39ea99fd86ef01514044fa32477ce16"
PLAN_SHA256 = "e4afafd9b9f792fc3d5799dc9fa9c21e26b4191c09f79ae78948e4756838cbcf"
MANIFEST_SHA256 = "9f18edbf8cc990e0f4e62910e9b06e836fc2809d4501ea2d3e07e3b3495d994b"
CLEAN = ["Eq.trans", "congrArg", "congrFun'"]


class GeneratedGcdCarrierAuditResultError(RuntimeError):
    """The carrier evidence, derived frontier, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise GeneratedGcdCarrierAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise GeneratedGcdCarrierAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise GeneratedGcdCarrierAuditResultError("measured carrier result changed")
    if (
        result.get("kind") != "axeyum-autogenesis-generated-gcd-carrier-audit-result"
        or result.get("state")
        != "generated-gcd-carrier-localized-to-three-novel-dependencies"
        or sha256(PLAN) != PLAN_SHA256
        or stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
    ):
        raise GeneratedGcdCarrierAuditResultError("result producer or pack changed")
    for name, digest, size in [
        (
            "audit-result.json",
            "4ca628ffbe258d33617acda48434cf35716c8e6e97fddb2597b0c298e8196e24",
            1_376,
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
            raise GeneratedGcdCarrierAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if (
        audit.get("rows") != [result["carrier"]]
        or audit.get("ordered_roots") != [result["carrier"]["name"]]
        or audit.get("rendered_material")
        != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
    ):
        raise GeneratedGcdCarrierAuditResultError("batch measurement changed")
    dependencies = result["carrier"]["direct_theorem_dependencies"]
    novel = [name for name in dependencies if name not in CLEAN]
    if (
        result.get("already_measured_clean_dependencies") != CLEAN
        or result.get("novel_dependency_frontier") != novel
        or len(novel) != 3
        or result.get("summary")
        != {
            "population": 1,
            "empty_footprint": 0,
            "direct_dependency_population": 6,
            "already_measured_clean_population": 3,
            "novel_dependency_population": 3,
            "primitive_reconstruction_authorized": False,
        }
    ):
        raise GeneratedGcdCarrierAuditResultError("derived frontier changed")
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
        raise GeneratedGcdCarrierAuditResultError("no-reconstruction authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_GENERATED_GCD_CARRIER_AUDIT_RESULT_OK|carrier=1|"
            "direct=6|known_clean=3|novel=3|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        GeneratedGcdCarrierAuditResultError,
    ) as error:
        print(f"autogenesis-generated-gcd-carrier-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
