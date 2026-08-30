#!/usr/bin/env python3
"""Verify the accepted official-representation gcd zero-left theorem."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-zero-left-root-export-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-zero-left-root-export-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/0a73f8458-official-gcd-zero-left-root-v1/manifest.json")
PLAN_SHA256 = "88430300df6e8ed6b3beb9ca834d808e3cc9379205ecac6e1d73742620bd8d9c"
MANIFEST_SHA256 = "f7d01b5c782b098fce84d8ce342d53c7da70bc2fe8d59864e0d44d04c095ff0e"
STREAM_SHA256 = "824399899916c72329f201c0ea8c1b0fe25315ea013c4f392586668f67f606a0"
AUDIT_SHA256 = "27fc809c6e634453589aeedd5ae37527bc8f4c3412d6ba6ae141be12ed33d4de"
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 2, "successful_importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
BOUNDARY = {"official_gcd_zero_left_completed": True, "required_next_increment": "reconstruct the official-representation Nat.gcd successor computation leaf, then preregister composition with the accepted generic balanced-Bezout theorem", "official_gcd_succ_completed": False}
AUTHORITY = {"official_gcd_zero_left_credit": 1, "official_gcd_succ_credit": 0, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdZeroLeftRootExportResultError(RuntimeError):
    """The theorem, sealed evidence, cleanup, or bounded authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdZeroLeftRootExportResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-zero-left-root-export-result", "official-gcd-zero-left-reconstructed-twice-empty-footprint"):
        raise OfficialGcdZeroLeftRootExportResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-zero-left-root-export-plan-v1.json", "sha256": PLAN_SHA256, "commit": "b866b31eec94a3ed72a40d4df304a80ae2c169f5"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdZeroLeftRootExportResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdZeroLeftRootExportResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdZeroLeftRootExportResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if manifest.get("state") != result.get("state"):
        raise OfficialGcdZeroLeftRootExportResultError("manifest state changed")
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdZeroLeftRootExportResultError("execution changed")
    stream = {"bytes": 509474, "maximum_bytes": 2000000, "sha256": STREAM_SHA256, "root_selected": True}
    if result.get("stream") != stream:
        raise OfficialGcdZeroLeftRootExportResultError("stream measurement changed")
    manifest_stream = manifest.get("stream", {})
    if (manifest_stream.get("bytes"), manifest_stream.get("maximum_bytes"), manifest_stream.get("sha256")) != (509474, 2000000, STREAM_SHA256):
        raise OfficialGcdZeroLeftRootExportResultError("manifest stream measurement changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.nat_gcd_zero_left" or theorem.get("contract") != "forall n : Nat, Nat.gcd 0 n = n" or theorem.get("declaration_sha256") != "e4f6c7e3971f5751bd1e889e9bfc28b7035d9f47204f7aafa5efc06b97cf3555" or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != ["Axeyum.Autogenesis.gcdModel_zero_left"] or theorem.get("audit_sha256") != AUDIT_SHA256 or theorem.get("fresh_reconstructions") != 2 or theorem.get("audits_byte_identical") is not True or theorem.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise OfficialGcdZeroLeftRootExportResultError("theorem measurement changed")
    audits = [load(MANIFEST.parent / "audit-1.json"), load(MANIFEST.parent / "audit-2.json")]
    if any(sha256(MANIFEST.parent / f"audit-{index}.json") != AUDIT_SHA256 for index in (1, 2)) or audits[0] != audits[1]:
        raise OfficialGcdZeroLeftRootExportResultError("fresh audits differ")
    audit = audits[0]
    expected_row = {"axiom_footprint": [], "class": "empty-footprint", "declaration_sha256": "e4f6c7e3971f5751bd1e889e9bfc28b7035d9f47204f7aafa5efc06b97cf3555", "direct_theorem_dependencies": ["Axeyum.Autogenesis.gcdModel_zero_left"], "name": "Axeyum.Autogenesis.nat_gcd_zero_left"}
    if audit.get("ordered_roots") != ["Axeyum.Autogenesis.nat_gcd_zero_left"] or audit.get("summary", {}).get("all_roots_empty") is not True or audit.get("rows") != [expected_row] or audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise OfficialGcdZeroLeftRootExportResultError("audit content changed")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise OfficialGcdZeroLeftRootExportResultError("cleanup changed")
    if result.get("next_boundary") != BOUNDARY or manifest.get("next_boundary") != BOUNDARY:
        raise OfficialGcdZeroLeftRootExportResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdZeroLeftRootExportResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_ZERO_LEFT_ROOT_EXPORT_RESULT_OK|stream_bytes=509474|imports=2|empty=1/1|zero_left=1|succ=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdZeroLeftRootExportResultError) as error:
        print(f"autogenesis-official-gcd-zero-left-root-export-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
