#!/usr/bin/env python3
"""Verify the retained official-kernel composition decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-plan-v1.json"
SOURCE = ROOT / "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/9ec4bcfa1-official-gcd-balanced-bezout-official-kernel-v1/manifest.json")
PLAN_SHA256 = "e93e4bd2ae2d60cf949a30359ad7d619c574b7e6775ca8a5785efac7c01591c0"
SOURCE_SHA256 = "f212cf184eaf596b0ff9e25dc73e875e7d3e235d7c86e45539cbd69a5782ee38"
MANIFEST_SHA256 = "6c415e21f6d0816cf59b4fcd4f576d4259e0be0dae9323849ba187fe3a5f69c6"
EXECUTION = {"binary_builds": 1, "complete_invocations": 1, "input_stream_reads": 5, "successful_composition_operations": 3, "failed_composition_operations": 1, "successful_specialization_operations": 2, "closed_balanced_bezout_submissions": 0, "retries": 0, "second_invocation_skipped_after_first_decline": True}
DECLINE = {"operation": "compose the accepted generic balanced-Bezout theorem into the official r082 base after both gcd leaves and modulo adapter", "class": "unsupported-missing-declaration", "first_rejected": "Acc", "declaration_kind": "recursive-inductive", "proof_material_rendered": False, "partial_kernel_published": False}
BOUNDARY = {"required_next_increment": "preregister the reverse composition direction: keep the accepted generic theorem kernel as the base and compose only Nat.mod_lt plus the three accepted leaf/adapter roots into it", "generic_kernel_as_base_selected": True, "closed_gcd_balanced_bezout_completed": False}
AUTHORITY = {"inherited_official_gcd_zero_left_credit": 1, "inherited_official_gcd_succ_credit": 1, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdBalancedBezoutOfficialKernelResultError(RuntimeError):
    """The decline evidence, execution, boundary, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutOfficialKernelResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-official-kernel-result", "first-invocation-declined-at-missing-recursive-Acc-no-retry"):
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-plan-v1.json", "sha256": PLAN_SHA256, "commit": "1d03f09b33dff6dea6f9c2b6c82684e5617b90ea"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("evidence pack is not sealed")
    expected_implementation = {"path": "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs", "sha256": SOURCE_SHA256, "commit": "f1e0edb577d06408faab4019b599b612201f5f92"}
    if sha256(SOURCE) != SOURCE_SHA256 or result.get("implementation") != expected_implementation:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("implementation identity changed")
    manifest = load(MANIFEST)
    if manifest.get("state") != result.get("state") or result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("state or execution changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("decline changed")
    if (MANIFEST.parent / "run-1.json").read_bytes() != b"":
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("failed run published output")
    diagnostic = (MANIFEST.parent / "run-1.stderr").read_text()
    if diagnostic != 'official-gcd-balanced-bezout-composition: generic-balanced-bezout composition declined: UnsupportedMissingDeclaration { name: "Acc", kind: "recursive-inductive" }\n':
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("diagnostic changed")
    if result.get("next_boundary") != BOUNDARY or manifest.get("next_boundary") != BOUNDARY:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdBalancedBezoutOfficialKernelResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_OFFICIAL_KERNEL_RESULT_OK|invocations=1|first_rejected=Acc|closed=0|retries=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutOfficialKernelResultError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-official-kernel-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
