#!/usr/bin/env python3
"""Verify the fail-closed gcd/Bézout specialization decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-closed-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-closed-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/0e23382f8-official-gcd-balanced-bezout-closed-v1/manifest.json")
PLAN_SHA256 = "89bd1b7c9bb22af7a5ea26c365fdcaaefca2ebd26d69ebf3191d0c847b3f2124"
MANIFEST_SHA256 = "c136a95253f6259e5faed9f10ffa9c0e475f5f5be85c7c3c7a57d5efcaa44d7a"
EXECUTION = {"binary_builds": 1, "complete_invocations": 1, "input_stream_reads": 4, "intermediate_specialization_operations": 3, "generic_composition_attempts": 1, "closed_theorem_submissions": 0, "retries": 0, "second_invocation_skipped_after_first_decline": True}
DECLINE = {"operation": "compose accepted generic balanced-Bezout theorem into accepted target-owned gcd support kernel", "class": "type-shape-mismatch", "first_rejected": "WellFounded.fix", "source_type_shape_sha256": "f45b230503d6ddc03c61714008f6165dd055ff995d927507fc6d7aaffcf6afd6", "target_type_shape_sha256": "0c2e9552a1056133fbd4e6a318344cfb1310468f7d2113efb37ebba0bf6ef32c", "proof_material_rendered": False, "partial_kernel_published": False}
AUTHORITY = {"closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdBalancedBezoutClosedResultError(RuntimeError):
    """The decline, sealed evidence, or zero-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutClosedResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-closed-result", "first-complete-invocation-declined-at-well-founded-fix-type-shape-no-retry"):
        raise OfficialGcdBalancedBezoutClosedResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-closed-plan-v1.json", "sha256": PLAN_SHA256, "commit": "0e23382f8"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdBalancedBezoutClosedResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdBalancedBezoutClosedResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdBalancedBezoutClosedResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    executed_source = MANIFEST.parent / "nat_gcd_succ_specialization.executed.rs"
    expected_implementation = {"repository_path": "crates/axeyum-lean-import/examples/nat_gcd_succ_specialization.rs", "pack_path": "nat_gcd_succ_specialization.executed.rs", "bytes": 48565, "sha256": "253e4b149c4611b5fef918b3cfd19be020b49fffc71d6e759b3807049c0cd99f", "mode": "--closed-balanced-bezout"}
    if manifest.get("implementation") != expected_implementation or sha256(executed_source) != expected_implementation["sha256"]:
        raise OfficialGcdBalancedBezoutClosedResultError("executed implementation identity changed")
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdBalancedBezoutClosedResultError("execution accounting changed")
    if result.get("decline") != DECLINE or manifest.get("decline") != DECLINE:
        raise OfficialGcdBalancedBezoutClosedResultError("typed decline changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdBalancedBezoutClosedResultError("zero authority changed")
    boundary = result.get("next_boundary", {})
    if boundary.get("closed_specialization_completed") is not False or boundary.get("compatibility_override_authorized") is not False or manifest.get("next_boundary") != boundary:
        raise OfficialGcdBalancedBezoutClosedResultError("next boundary changed")
    if result.get("implementation") != {"path": "crates/axeyum-lean-import/examples/nat_gcd_succ_specialization.rs", "sha256": "253e4b149c4611b5fef918b3cfd19be020b49fffc71d6e759b3807049c0cd99f", "mode": "--closed-balanced-bezout"}:
        raise OfficialGcdBalancedBezoutClosedResultError("implementation identity changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_CLOSED_DECLINE_OK|invocations=1|first_rejected=WellFounded.fix|closed_credit=0|retries=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutClosedResultError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-closed-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
