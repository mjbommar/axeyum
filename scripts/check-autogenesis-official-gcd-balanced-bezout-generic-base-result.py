#!/usr/bin/env python3
"""Verify the retained generic-kernel-base exact-reuse decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-generic-base-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-generic-base-plan-v1.json"
SOURCE = ROOT / "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/47343f64f-official-gcd-balanced-bezout-generic-base-v1/manifest.json")
PLAN_SHA256 = "c412cff4cc767c8e676bb09ac623db07f3121f64e9ed0e55a676a4076fd3dc51"
SOURCE_SHA256 = "61a1df4c50fd269183d75a0aceeb11dd4f231ea1d077b74f9f526f360b657d8e"
MANIFEST_SHA256 = "c7335778428d520e5872637371ebbe1a9a89fc3742d4e82ea512283e440efb6b"
EXECUTION = {"binary_builds": 1, "complete_invocations": 1, "input_stream_reads": 5, "successful_composition_operations": 0, "failed_composition_operations": 1, "successful_specialization_operations": 0, "closed_balanced_bezout_submissions": 0, "retries": 0, "second_invocation_skipped_after_first_decline": True}
DECLINE = {"operation": "compose Nat.mod_lt from r082 into the accepted generic balanced-Bezout kernel", "class": "no-additions", "first_rejected": "Nat.mod_lt", "interpretation": "the exact theorem is already present in the generic kernel and must be reused under an explicit identity check rather than composed", "proof_material_rendered": False, "partial_kernel_published": False}
BOUNDARY = {"required_next_increment": "preregister exact Nat.mod_lt reuse across the two pinned kernels, then compose only modLtSucc and the two gcd leaves into the generic base", "exact_reuse_selected": True, "closed_gcd_balanced_bezout_completed": False}
AUTHORITY = {"inherited_official_gcd_zero_left_credit": 1, "inherited_official_gcd_succ_credit": 1, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdBalancedBezoutGenericBaseResultError(RuntimeError):
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
        raise OfficialGcdBalancedBezoutGenericBaseResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-generic-base-result", "first-invocation-declined-at-exact-Nat-mod-lt-reuse-no-retry"):
        raise OfficialGcdBalancedBezoutGenericBaseResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-generic-base-plan-v1.json", "sha256": PLAN_SHA256, "commit": "2d62fc4a7b87dccdb7a050129942d403831a0665"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdBalancedBezoutGenericBaseResultError("evidence pack is not sealed")
    expected_implementation = {"path": "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs", "sha256": SOURCE_SHA256, "commit": "c4bf44f90f1752a307cc8d7dd625a9a7f793bf78"}
    if sha256(SOURCE) != SOURCE_SHA256 or result.get("implementation") != expected_implementation:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("implementation identity changed")
    manifest = load(MANIFEST)
    if manifest.get("state") != result.get("state") or result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("state or execution changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("decline changed")
    if (MANIFEST.parent / "run-1.json").read_bytes() != b"":
        raise OfficialGcdBalancedBezoutGenericBaseResultError("failed run published output")
    if (MANIFEST.parent / "run-1.stderr").read_text() != "official-gcd-balanced-bezout-composition: Nat.mod_lt composition declined: NoAdditions\n":
        raise OfficialGcdBalancedBezoutGenericBaseResultError("diagnostic changed")
    if result.get("next_boundary") != BOUNDARY or manifest.get("next_boundary") != BOUNDARY:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("next boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdBalancedBezoutGenericBaseResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_GENERIC_BASE_RESULT_OK|invocations=1|Nat.mod_lt=already-present|closed=0|retries=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutGenericBaseResultError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-generic-base-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
