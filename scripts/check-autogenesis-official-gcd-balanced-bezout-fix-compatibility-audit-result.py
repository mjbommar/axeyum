#!/usr/bin/env python3
"""Verify the sealed proof-free WellFounded.fix closure audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-fix-compatibility-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-fix-compatibility-audit-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/7550b31c4-official-gcd-balanced-bezout-fix-audit-v1/manifest.json")
PLAN_SHA256 = "8bcdce7de9f955a77aaf1a3a07d6766d0ec1e15f8cb439c19025de6b6b57f2dc"
MANIFEST_SHA256 = "b6cfa19fadc1651daca57bae21dad29d501cd8938b1bc493211b2eac6196d423"
AUDIT_SHA256 = "3275b3cab096ec016702b175dfb1aa63e0e450747ad1bb88d4cbfb6727d5f4e7"
EXECUTION = {"binary_builds": 1, "complete_invocations": 2, "input_stream_reads": 8, "intermediate_specialization_operations": 6, "closure_audits": 2, "closed_theorem_submissions": 0, "retries": 0}
OBSERVATION = {"audit_sha256": AUDIT_SHA256, "audits_byte_identical": True, "source_closure_count": 9, "target_closure_count": 5, "closure_union_count": 9, "class_counts": {"kernel-type-shape": 4, "missing-target": 4, "type-shape-mismatch": 1}, "root": "WellFounded.fix", "source_root_kind": "definition", "target_root_kind": "definition", "source_root_type_shape_sha256": "f45b230503d6ddc03c61714008f6165dd055ff995d927507fc6d7aaffcf6afd6", "target_root_type_shape_sha256": "0c2e9552a1056133fbd4e6a318344cfb1310468f7d2113efb37ebba0bf6ef32c", "missing_target_names": ["WellFounded.apply", "WellFounded.fixF", "WellFounded.intro", "WellFounded.rec"], "representation_conclusion": "generic source retains the official inductive WellFounded package while the target support kernel uses the native definition representation", "rendered_material": {"proof_terms": 0, "theorem_types": 0, "definition_values": 0, "theorem_values": 0}}
BOUNDARY = {"repair": "reconstruct clean gcd computation leaves inside the official generic kernel without importing the native WellFounded representation", "translation_authorized": False, "compatibility_override_authorized": False, "closed_specialization_retry_authorized": False}
AUTHORITY = {"compatibility_audit_credit": 1, "compatibility_override_credit": 0, "translation_credit": 0, "target_reconstruction_credit": 0, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class OfficialGcdBalancedBezoutFixAuditResultError(RuntimeError):
    """The observation, sealed evidence, repair boundary, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutFixAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-fix-compatibility-audit-result", "well-founded-fix-closure-classified-twice-source-official-target-native-incompatible"):
        raise OfficialGcdBalancedBezoutFixAuditResultError("result identity changed")
    expected_plan = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-fix-compatibility-audit-plan-v1.json", "sha256": PLAN_SHA256, "commit": "7550b31c4"}
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != expected_plan:
        raise OfficialGcdBalancedBezoutFixAuditResultError("plan identity changed")
    expected_pack = {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    if sha256(MANIFEST) != MANIFEST_SHA256 or result.get("evidence_pack") != expected_pack:
        raise OfficialGcdBalancedBezoutFixAuditResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise OfficialGcdBalancedBezoutFixAuditResultError("evidence pack is not sealed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise OfficialGcdBalancedBezoutFixAuditResultError("execution accounting changed")
    if result.get("observation") != OBSERVATION or manifest.get("observation") != OBSERVATION:
        raise OfficialGcdBalancedBezoutFixAuditResultError("observation changed")
    for path in (MANIFEST.parent / "audit-1.json", MANIFEST.parent / "audit-2.json"):
        if sha256(path) != AUDIT_SHA256:
            raise OfficialGcdBalancedBezoutFixAuditResultError("audit replay changed")
    executed = MANIFEST.parent / "nat_gcd_succ_specialization.executed.rs"
    if sha256(executed) != "3c9fcae6b04c263922cc92db87e3a88ccb4640438ba72a03bdb083c90f25b629":
        raise OfficialGcdBalancedBezoutFixAuditResultError("executed implementation changed")
    if result.get("selected_next_boundary") != BOUNDARY or manifest.get("selected_next_boundary") != BOUNDARY:
        raise OfficialGcdBalancedBezoutFixAuditResultError("selected repair boundary changed")
    if result.get("authority") != AUTHORITY or manifest.get("authority") != AUTHORITY:
        raise OfficialGcdBalancedBezoutFixAuditResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_FIX_AUDIT_RESULT_OK|runs=2|union=9|missing_target=4|type_mismatch=1|theorem_submissions=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutFixAuditResultError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-fix-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
