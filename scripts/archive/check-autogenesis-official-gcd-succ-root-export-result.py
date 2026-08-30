#!/usr/bin/env python3
"""Verify the accepted official-representation gcd successor theorem."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-succ-root-export-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-succ-root-export-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/dfcff00d1-official-gcd-succ-root-v1/manifest.json")
PLAN_SHA256 = "3ca42bb288b35af77cbffb91f3262359b9192e49eddbd32a02369c1460d42714"
MANIFEST_SHA256 = "c1ebf421a26764d7796932c49ebbc6d1c3a889a665e6d4830a28a78b97f83a2a"
STREAM_SHA256 = "2af40b2c7d89a0959bbe3018da60841ea1dc933ae2f40112ae84d95feab6044c"
AUDIT_SHA256 = "99f03a2a0c958d348357c301e38d724923a6dcca9ffb6e89b557ff2963ff83af"
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 2, "successful_importer_runs": 2, "proof_bearing_stream_reads": 2, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
BOUNDARY = {"official_representation_gcd_leaves_completed": True, "required_next_increment": "preregister composition of both accepted official-representation gcd leaves into the accepted generic balanced-Bezout kernel", "closed_gcd_balanced_bezout_completed": False}
AUTHORITY = {"inherited_official_gcd_zero_left_credit": 1, "new_official_gcd_succ_credit": 1, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdSuccRootExportResultError(RuntimeError):
    """The theorem, representation, evidence, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdSuccRootExportResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-succ-root-export-result", "official-representation-gcd-successor-reconstructed-twice-empty-footprint"):
        raise OfficialGcdSuccRootExportResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-succ-root-export-plan-v1.json", "sha256": PLAN_SHA256, "commit": "fb1a3613e1026a80df6454fdd76bdc19a5939a94"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdSuccRootExportResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdSuccRootExportResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdSuccRootExportResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if manifest.get("state") != result.get("state") or result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdSuccRootExportResultError("manifest state or execution changed")
    stream = {"bytes": 511748, "maximum_bytes": 2000000, "sha256": STREAM_SHA256, "root_selected": True, "representation": "official-mathlib-well-founded"}
    if result.get("stream") != stream:
        raise OfficialGcdSuccRootExportResultError("stream measurement changed")
    manifest_stream = manifest.get("stream", {})
    if (manifest_stream.get("bytes"), manifest_stream.get("maximum_bytes"), manifest_stream.get("sha256")) != (511748, 2000000, STREAM_SHA256):
        raise OfficialGcdSuccRootExportResultError("manifest stream measurement changed")
    theorem = result.get("theorem", {})
    if theorem.get("name") != "Axeyum.Autogenesis.nat_gcd_succ" or theorem.get("contract") != "given mod_lt_succ, forall m n, Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m)" or theorem.get("declaration_sha256") != "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16" or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != ["Axeyum.Autogenesis.gcdModel_succ"] or theorem.get("audit_sha256") != AUDIT_SHA256 or theorem.get("fresh_reconstructions") != 2 or theorem.get("audits_byte_identical") is not True or theorem.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise OfficialGcdSuccRootExportResultError("theorem measurement changed")
    audits = [load(MANIFEST.parent / "audit-1.json"), load(MANIFEST.parent / "audit-2.json")]
    if any(sha256(MANIFEST.parent / f"audit-{index}.json") != AUDIT_SHA256 for index in (1, 2)) or audits[0] != audits[1]:
        raise OfficialGcdSuccRootExportResultError("fresh audits differ")
    expected_row = {"axiom_footprint": [], "class": "empty-footprint", "declaration_sha256": "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16", "direct_theorem_dependencies": ["Axeyum.Autogenesis.gcdModel_succ"], "name": "Axeyum.Autogenesis.nat_gcd_succ"}
    audit = audits[0]
    if audit.get("ordered_roots") != ["Axeyum.Autogenesis.nat_gcd_succ"] or audit.get("summary", {}).get("all_roots_empty") is not True or audit.get("rows") != [expected_row] or audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise OfficialGcdSuccRootExportResultError("audit content changed")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise OfficialGcdSuccRootExportResultError("cleanup changed")
    if result.get("next_boundary") != BOUNDARY or manifest.get("next_boundary") != BOUNDARY:
        raise OfficialGcdSuccRootExportResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdSuccRootExportResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_SUCC_ROOT_EXPORT_RESULT_OK|stream_bytes=511748|imports=2|empty=1/1|official_leaves=2|closed=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdSuccRootExportResultError) as error:
        print(f"autogenesis-official-gcd-succ-root-export-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
