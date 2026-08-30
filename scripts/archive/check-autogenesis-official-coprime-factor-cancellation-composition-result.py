#!/usr/bin/env python3
"""Verify the retained official cancellation exact-reuse decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-composition-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-coprime-factor-cancellation-composition-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/dd15493b6-official-coprime-factor-cancellation-v1/manifest.json")
WRAPPER = MANIFEST.parent / "executed-wrapper.rs"
BODY = MANIFEST.parent / "executed-body.rs"
PLAN_SHA256 = "8ffb90ee24e5ae9e30a34ab07b422feb69167227444c319566ed6224334b0632"
WRAPPER_SHA256 = "f61420c2a83c61ef83e780216273639b77c0cb9286e846964972bdcb7cdf285a"
BODY_SHA256 = "4c193eed8a110c08127bdbecb494a946d1050aceff5de4f431b824a1127bfa66"
MANIFEST_SHA256 = "6c10af58550827c1f2ae9c7b50c4124128a941ab82e2f83b66a4c38ee15f7b5d"
EXECUTION = {"complete_invocations": 1, "input_stream_reads": 8, "successful_composition_operations": 3, "successful_specialization_operations": 3, "final_theorem_submissions": 0, "retries": 0, "second_invocation_skipped": True}
DECLINE = {"operation": "compose both clean multiplication leaves into the closed generic kernel", "class": "NoAdditions", "interpretation": "both exact declarations are already present and require explicit checked reuse", "partial_kernel_published": False}
BOUNDARY = {"required_next_increment": "preregister exact identity and compatibility reuse for both multiplication leaves, then compose only residual cancellation, all-Nat adapter, and native positive cancellation"}
AUTHORITY = {"official_cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialCancellationCompositionResultError(RuntimeError):
    """The exact-reuse decline, evidence, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialCancellationCompositionResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-coprime-factor-cancellation-composition-result", "first-run-declined-at-already-present-clean-mul-leaves-no-retry"):
        raise OfficialCancellationCompositionResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != {"path": "artifacts/autogenesis/official-coprime-factor-cancellation-composition-plan-v1.json", "sha256": PLAN_SHA256, "commit": "dd15493b6"}:
        raise OfficialCancellationCompositionResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialCancellationCompositionResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialCancellationCompositionResultError("evidence pack is not sealed")
    implementation = result.get("implementation", {})
    if sha256(WRAPPER) != WRAPPER_SHA256 or sha256(BODY) != BODY_SHA256 or implementation.get("wrapper_sha256") != WRAPPER_SHA256 or implementation.get("body_sha256") != BODY_SHA256:
        raise OfficialCancellationCompositionResultError("implementation identity changed")
    manifest = load(MANIFEST)
    if manifest.get("state") != result.get("state") or result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialCancellationCompositionResultError("state or execution changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise OfficialCancellationCompositionResultError("decline changed")
    if (MANIFEST.parent / "run-1.json").read_bytes() != b"":
        raise OfficialCancellationCompositionResultError("failed run published output")
    diagnostic = "official-gcd-balanced-bezout-composition: clean-multiplication-leaves composition declined: NoAdditions\n"
    if (MANIFEST.parent / "run-1.stderr").read_text() != diagnostic:
        raise OfficialCancellationCompositionResultError("diagnostic changed")
    if result.get("next_boundary") != BOUNDARY or manifest.get("next_boundary") != BOUNDARY:
        raise OfficialCancellationCompositionResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialCancellationCompositionResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_COMPOSITION_RESULT_OK|invocations=1|mul_leaves=already-present|final=0|retries=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialCancellationCompositionResultError) as error:
        print(f"autogenesis-official-cancellation-composition-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
