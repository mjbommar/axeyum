#!/usr/bin/env python3
"""Verify the private Int.fib_of_odd audit and direct-recurrence decision."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-odd-private-root-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-odd-private-root-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-of-odd-private-root-audit-v1")
AUDIT = PACK / "audit.json"
MANIFEST = PACK / "manifest.json"
RESULT_SHA256 = "fce124c65d3595a3d0a3ada24080c8804356fac184c0236a4155389d32815eb6"
PRIVATE_ROOT = "_private.Mathlib.Data.Int.Fib.Basic.0.Int.fib_of_odd._proof_1_2"


class IntFibOfOddPrivateRootAuditResultError(RuntimeError):
    """The private-root evidence or direct-recurrence decision changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibOfOddPrivateRootAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise IntFibOfOddPrivateRootAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise IntFibOfOddPrivateRootAuditResultError("measured private-root result changed")
    if result.get("state") != "private-root-is-automation-expansion-direct-recurrence-replacement-selected" or sha256(PLAN) != "0bc456f77980f20effd97401f38c4cd7c56b59d79e7e2e297cef8cae4c0e41d9" or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or sha256(MANIFEST) != "f1421560bf189c78db0adde214c732bbd9b82f8f7bd408b1157f87318857bd26" or sha256(AUDIT) != "e0bbb3f6a16f1bc40cf4e87855b65cc3afa5ef0c7b8985d09282286f2ef6e4de":
        raise IntFibOfOddPrivateRootAuditResultError("producer or pack changed")
    audit = load(AUDIT)
    row = audit["rows"][0]
    if audit["ordered_roots"] != [PRIVATE_ROOT] or row["name"] != PRIVATE_ROOT or row["class"] != "propext-bearing" or len(row["direct_theorem_dependencies"]) != 37 or not any(name.startswith("Int.Linear.") for name in row["direct_theorem_dependencies"]) or not any(name.startswith("Lean.Grind.") for name in row["direct_theorem_dependencies"]):
        raise IntFibOfOddPrivateRootAuditResultError("automation expansion changed")
    expected_root = {"name": PRIVATE_ROOT, "declaration_sha256": row["declaration_sha256"], "class": "propext-bearing", "direct_theorem_dependency_count": 37, "contains_linear_arithmetic_automation": True, "contains_grind_automation": True}
    if result.get("root") != expected_root or result.get("decision") != {"compose_private_root": False, "descend_automation_dependencies": False, "next": "preregister a target-owned proof of Int.fib_neg_natCast from Int.fib_add_two, Int.fib_natCast, clean integer transport, and explicit parity/sign induction"}:
        raise IntFibOfOddPrivateRootAuditResultError("decision changed")
    if result.get("authority", {}).get("ledger_writes") != 0 or result["authority"].get("proof_terms_rendered") != 0:
        raise IntFibOfOddPrivateRootAuditResultError("authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_OF_ODD_PRIVATE_ROOT_AUDIT_RESULT_OK|class=propext-bearing|dependencies=37|decision=direct-recurrence|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibOfOddPrivateRootAuditResultError) as error:
        print(f"autogenesis-int-fib-of-odd-private-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
