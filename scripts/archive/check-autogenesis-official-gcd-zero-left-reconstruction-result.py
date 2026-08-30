#!/usr/bin/env python3
"""Verify the fail-closed unbounded-export gcd-zero-left decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-zero-left-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-zero-left-reconstruction-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/96a6a4c34-official-gcd-zero-left-v1/manifest.json")
PLAN_SHA256 = "b28fa0765c6868f2a3b855b9f3681de0ee5dc63f716b3174696099af22175b97"
MANIFEST_SHA256 = "a1f0baf855dfd7c4956693fa002f075263cce4b841997da7b519070440b74d04"
EXECUTION = {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 1, "exporter_invocations": 1, "importer_runs": 1, "successful_importer_runs": 0, "proof_bearing_stream_reads": 1, "retries": 0, "second_import_skipped_after_first_failure": True}
DECLINE = {"operation": "independently import the complete-module export", "class": "resource-limit", "error": "RecordLimit", "limit": 2000000, "stream_bytes": 340033933, "root_selection_used": False, "theorem_submitted": False, "partial_kernel_published": False}
AUTHORITY = {"official_gcd_zero_left_credit": 0, "official_gcd_succ_credit": 0, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdZeroLeftResultError(RuntimeError):
    """The resource decline, sealed evidence, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdZeroLeftResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-zero-left-reconstruction-result", "source-compiled-unbounded-export-hit-import-record-limit-no-theorem-credit"):
        raise OfficialGcdZeroLeftResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-zero-left-reconstruction-plan-v1.json", "sha256": PLAN_SHA256, "commit": "3e6373de5"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdZeroLeftResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdZeroLeftResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdZeroLeftResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdZeroLeftResultError("execution accounting changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise OfficialGcdZeroLeftResultError("typed decline changed")
    if sha256(MANIFEST.parent / "official-gcd-zero-left.ndjson") != "fb37a6d73ccde73a327dc55172acce4d03562e782330fc87d9d6b1b8e5f3e509":
        raise OfficialGcdZeroLeftResultError("oversized stream identity changed")
    if sha256(MANIFEST.parent / "audit-1.stderr") != "6dda8334f0cf36b058a55dae9eb0d149c623aebd6d9e950b6ca3b010003942d6":
        raise OfficialGcdZeroLeftResultError("import decline evidence changed")
    cleanup = {"exact_temporary_paths_removed": 3, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}
    if result.get("cleanup") != cleanup or manifest.get("cleanup") != cleanup:
        raise OfficialGcdZeroLeftResultError("cleanup changed")
    boundary = result.get("next_boundary", {})
    if boundary.get("importer_limit_increase_authorized") is not False or boundary.get("source_proof_change_authorized") is not False or boundary.get("official_gcd_zero_left_completed") is not False or manifest.get("next_boundary") != boundary:
        raise OfficialGcdZeroLeftResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdZeroLeftResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_ZERO_LEFT_DECLINE_OK|compiled=1|stream_bytes=340033933|record_limit=2000000|imports=0/1|credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdZeroLeftResultError) as error:
        print(f"autogenesis-official-gcd-zero-left-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
