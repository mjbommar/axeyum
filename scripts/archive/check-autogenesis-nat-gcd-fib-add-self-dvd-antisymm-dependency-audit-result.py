#!/usr/bin/env python3
"""Verify the exact gcd-shift divisibility-antisymmetry audit result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-plan-v1.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/76462c935-gcd-shift-dvd-antisymm-dependency-audit-v1/manifest.json")
AUDIT = MANIFEST.parent / "audit-result.json"
PLAN_SHA256 = "6770c130445c15ee6a394477eb59281010ebb8177fc648d4e8e884d5ae144cb2"
MANIFEST_SHA256 = "78bfd1a6ff42c82db971c4bc6f91d7d54cfeff42c378404ea21d4ac7c1f8ec24"
AUDIT_SHA256 = "218a420ce0ac2b64d8d101d9fadfdf182d0234f7ac19f21125e8056ab2455d58"
ROOTS = ["Eq.symm", "Nat.eq_zero_of_zero_dvd", "Nat.le_antisymm", "Nat.le_of_dvd", "Nat.succ_pos"]
SUMMARY = {"population": 5, "empty_footprint": 4, "propext_bearing": 1, "other_assumption_bearing": 0, "sole_assumption_carrier": "Nat.le_of_dvd"}
AUTHORITY = {"replacement_source_compilations": 0, "new_theorem_submissions": 0, "exact_target_submissions": 0, "proof_terms_rendered": 0, "theorem_types_rendered": 0, "theorem_values_rendered": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}


class DvdAntisymmDependencyAuditResultError(RuntimeError):
    """The measured carrier, evidence, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise DvdAntisymmDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (1, "axeyum-autogenesis-nat-gcd-fib-add-self-dvd-antisymm-dependency-audit-result", "five-root-audit-complete-le-of-dvd-sole-propext-carrier"):
        raise DvdAntisymmDependencyAuditResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result["plan"]["sha256"] != PLAN_SHA256:
        raise DvdAntisymmDependencyAuditResultError("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or result["evidence_pack"]["sha256"] != MANIFEST_SHA256 or sha256(AUDIT) != AUDIT_SHA256:
        raise DvdAntisymmDependencyAuditResultError("evidence identity changed")
    if stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in MANIFEST.parent.iterdir() if path.is_file()):
        raise DvdAntisymmDependencyAuditResultError("evidence pack is not sealed")
    audit = load(AUDIT)
    if audit.get("ordered_roots") != ROOTS or [row["name"] for row in result["rows"]] != ROOTS or audit.get("rows") != result.get("rows"):
        raise DvdAntisymmDependencyAuditResultError("ordered audit rows changed")
    carriers = [row["name"] for row in result["rows"] if row["axiom_footprint"]]
    if carriers != ["Nat.le_of_dvd"] or result.get("summary") != SUMMARY:
        raise DvdAntisymmDependencyAuditResultError("assumption carrier classification changed")
    if audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise DvdAntisymmDependencyAuditResultError("proof material was rendered")
    if result.get("authority") != AUTHORITY or load(MANIFEST).get("authority") != AUTHORITY:
        raise DvdAntisymmDependencyAuditResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_GCD_SHIFT_DVD_ANTISYMM_AUDIT_RESULT_OK|roots=5|clean=4|carrier=Nat.le_of_dvd|submissions=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, DvdAntisymmDependencyAuditResultError) as error:
        print(f"autogenesis-gcd-shift-dvd-antisymm-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
