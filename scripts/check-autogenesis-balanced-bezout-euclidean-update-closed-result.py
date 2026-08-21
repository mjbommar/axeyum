#!/usr/bin/env python3
"""Verify the accepted closed balanced-Bezout Euclidean update."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-closed-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-closed-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/208efaef2-balanced-bezout-euclidean-update-closed-v1/manifest.json")
PLAN_SHA256 = "ffa795f4eccdc079ced46bd35628aa9301f5643d0b8a6312b55c695dfa024e02"
MANIFEST_SHA256 = "f1b06c41b192ab9fd205a3af0400548788f0e24ebe8ab3ab02e7e5f56a5e9f35"
AUDIT_SHA256 = "31d32a7ae940f4ccebc06f65a15949094b24beececa4beb42064c1d47c7e9bae"
DEPENDENCIES = ["Axeyum.Autogenesis.balancedBezoutEuclideanUpdateV2", "Axeyum.Autogenesis.balancedBezoutMulAssocLeafV1", "Axeyum.Autogenesis.balancedBezoutRightDistribLeafV1"]
EXECUTION = {"source_copies": 3, "compiler_invocations": 3, "successful_compilations": 3, "exporter_invocations": 1, "importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}


class BalancedBezoutClosedUpdateResultError(RuntimeError):
    """The closed theorem, exact dependencies, evidence, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutClosedUpdateResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-closed-result", "closed-update-reconstructed-twice-empty-footprint-exact-three-dependencies"):
        raise BalancedBezoutClosedUpdateResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != {"path": "artifacts/autogenesis/balanced-bezout-euclidean-update-closed-plan-v1.json", "sha256": PLAN_SHA256, "commit": "8b60ed825530b4d4f90aeb35a4f89723add1731c"}:
        raise BalancedBezoutClosedUpdateResultError("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}:
        raise BalancedBezoutClosedUpdateResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise BalancedBezoutClosedUpdateResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutClosedUpdateResultError("execution changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.balancedBezoutEuclideanUpdateClosedV1" or theorem.get("declaration_sha256") != "06a337b7154949a4aaf2dd3ca17084cc0f608c6c4613bc40927280c74b135b91" or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES or theorem.get("audit_sha256") != AUDIT_SHA256 or theorem.get("fresh_reconstructions") != 2 or theorem.get("audits_byte_identical") is not True:
        raise BalancedBezoutClosedUpdateResultError("theorem measurement changed")
    for path in (MANIFEST.parent / "audit-1.json", MANIFEST.parent / "audit-2.json"):
        if sha256(path) != AUDIT_SHA256:
            raise BalancedBezoutClosedUpdateResultError("fresh audits differ")
    cleanup = {"exact_temporary_paths_removed": 9, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
    if result.get("cleanup") != cleanup or manifest.get("cleanup") != cleanup:
        raise BalancedBezoutClosedUpdateResultError("cleanup changed")
    boundary = {"closed_update_credit": 1, "required_next_increment": "preregister generic official-gcd balanced-Bezout induction using the accepted quotient witness, closed update, and clean gcd leaves", "generic_gcd_submission_authorized": False}
    if result.get("next_boundary") != boundary or manifest.get("next_boundary") != boundary:
        raise BalancedBezoutClosedUpdateResultError("next boundary changed")
    authority = {"closed_update_credit": 1, "generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != authority:
        raise BalancedBezoutClosedUpdateResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_CLOSED_UPDATE_RESULT_OK|compilations=3|exports=1|imports=2|empty=2/2|dependencies=3|generic_gcd=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutClosedUpdateResultError) as error:
        print(f"autogenesis-balanced-bezout-closed-update-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
