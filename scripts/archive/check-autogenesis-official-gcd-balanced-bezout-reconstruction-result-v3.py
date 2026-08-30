#!/usr/bin/env python3
"""Verify the balanced-Bezout V3 first-import decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v3.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v3.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/f96a2319d-official-gcd-balanced-bezout-v3-v1/manifest.json")
PLAN_SHA256 = "aa2bfdb5530056d478bcaf809d74e91ef67c05ffbd6959b228493a66fd720fca"
MANIFEST_SHA256 = "683fab713611a5fc3ceb1e0ed4e84cdad0833b46b9cb7d7ff4a3381f62d27ba0"
EXECUTION = {"source_copies": 2, "compiler_invocations": 2, "successful_compilations": 2, "failed_compilations": 0, "exporter_invocations": 1, "importer_runs": 1, "proof_bearing_stream_reads": 1, "second_import_forbidden_by_first_gate": True, "retries": 0}
CLEANUP = {"exact_temporary_paths_removed": 6, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}


class BalancedBezoutResultV3Error(RuntimeError):
    """The first-import decline, footprint, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutResultV3Error(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (3, "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-result", "compiled-exported-first-import-assumption-bearing-second-import-forbidden"):
        raise BalancedBezoutResultV3Error("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v3.json", "sha256": PLAN_SHA256, "commit": "eb061c9bfe2d021a684ba8b32004359c75b9e508"}:
        raise BalancedBezoutResultV3Error("plan identity changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555 or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444 or result.get("evidence_pack") != {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}:
        raise BalancedBezoutResultV3Error("evidence identity or mode changed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutResultV3Error("execution counts changed")
    roots = [
        {"name": "Axeyum.Autogenesis.modQuotientWitnessV3", "declaration_sha256": "5132ea365b8403b82d722b4ae6457d1a8e632d1eab0d52a3eb5d448396bb52ac", "axiom_footprint": ["Quot", "Quot.lift", "Quot.mk", "Quot.sound"], "decisive_dependencies": ["funext", "if_neg", "if_pos", "dif_pos"]},
        {"name": "Axeyum.Autogenesis.officialGcdBalancedBezoutV3", "declaration_sha256": "14d2853b99034e480936acda5af178e45dc7696eb3d75a54458ddf2f197b7c0c", "axiom_footprint": ["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"], "decisive_dependencies": ["Axeyum.Autogenesis.modQuotientWitnessV3", "Mathlib.Tactic.Ring.Common", "Mathlib.Tactic.Ring.of_eq"]},
    ]
    if result.get("roots") != roots:
        raise BalancedBezoutResultV3Error("root measurements changed")
    if manifest.get("audit", {}).get("all_roots_empty") is not False or manifest.get("audit", {}).get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise BalancedBezoutResultV3Error("audit gate or rendering boundary changed")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise BalancedBezoutResultV3Error("cleanup changed")
    if result.get("next_boundary") != {"lean_tactic_source_route_accepted": False, "required_replacement": "construct the quotient witness and balanced Euclidean update with explicit kernel terms and clean arithmetic leaves, avoiding funext, conditional simplifier proofs, and Mathlib ring normalization", "reuse_compilation_as_theorem_credit": False}:
        raise BalancedBezoutResultV3Error("next boundary changed")
    authority = {"generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    manifest_authority = {"generic_theorem_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if result.get("authority") != authority or manifest.get("authority") != manifest_authority:
        raise BalancedBezoutResultV3Error("authority changed")
    if result.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result-v3.py" or result.get("limitations") != "V3 proves only that the convenient Lean tactic route compiles but remains assumption-bearing. It establishes no accepted generic theorem, target specialization, cancellation, Fibonacci target, receipt, evaluation result, fact transition, or ledger write.":
        raise BalancedBezoutResultV3Error("verification or limitation changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_V3_DECLINE_OK|compilations=2|exports=1|imports=1/2|roots_empty=0/2|baseline=3|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutResultV3Error) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-result-v3: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
