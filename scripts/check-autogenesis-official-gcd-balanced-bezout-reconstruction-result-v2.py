#!/usr/bin/env python3
"""Verify the corrected balanced-Bezout V2 compilation decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v2.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v2.json"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/1de1558f7-official-gcd-balanced-bezout-v2-v1/manifest.json")
PLAN_SHA256 = "30d56bc3d4597cc1a2335cfc4032cb3988fdb461f1396fe1a7b48982c06562c9"
MANIFEST_SHA256 = "d5532817d252b359fb7a9fb01324c48b619ad64d8e79b3208fbba3b084c055a0"
DIAGNOSTICS = [
    "unfolded Nat.modCore retains a positive-divisor dependent conditional",
    "congrArg multiplication equalities remain beta-redexes and do not rewrite normalized products",
    "induction hypothesis notation requires an explicit definitional change before contextual rewrite",
]
EXECUTION = {"source_copies": 2, "compiler_invocations": 2, "successful_compilations": 1, "failed_compilations": 1, "exporter_invocations": 0, "importer_runs": 0, "proof_bearing_stream_reads": 0, "retries_after_compilation": 0}
CLEANUP = {"exact_temporary_paths_removed": 6, "preexisting_status_entries_before": 3, "preexisting_status_entries_after": 3, "preexisting_baseline_unchanged": True}


class BalancedBezoutResultV2Error(RuntimeError):
    """The V2 decline, evidence pack, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutResultV2Error(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (
        2,
        "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-result",
        "corrected-main-source-compilation-declined-no-retry-no-theorem-credit",
    ):
        raise BalancedBezoutResultV2Error("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != {
        "path": "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v2.json",
        "sha256": PLAN_SHA256,
        "commit": "f96a2319d1c94be35607b7555028a69b59bb32be",
    }:
        raise BalancedBezoutResultV2Error("plan identity changed")
    if (
        sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or result.get("evidence_pack") != {"path": str(MANIFEST), "sha256": MANIFEST_SHA256, "directory_mode": "0555", "file_mode": "0444"}
    ):
        raise BalancedBezoutResultV2Error("evidence identity or mode changed")
    manifest = load(MANIFEST)
    if result.get("execution") != EXECUTION or manifest.get("execution") != EXECUTION:
        raise BalancedBezoutResultV2Error("execution counts changed")
    if result.get("result") != {
        "generic_main_source_compiled": False,
        "generic_theorems_reconstructed": 0,
        "diagnostic_count": 4,
        "diagnostic_classes": DIAGNOSTICS,
        "proof_material_rendered": False,
    } or manifest.get("diagnostics") != {"count": 4, "classes": DIAGNOSTICS, "proof_material_rendered": False}:
        raise BalancedBezoutResultV2Error("diagnostics changed")
    if result.get("cleanup") != CLEANUP or manifest.get("cleanup") != CLEANUP:
        raise BalancedBezoutResultV2Error("cleanup changed")
    if result.get("next_boundary") != {
        "requires_new_preregistration": True,
        "source_corrections": [
            "eliminate the unfolded Nat.modCore dependent conditional with the existing positive-divisor proof",
            "give the congrArg equalities explicit normalized product types",
            "change the induction hypothesis definitionally to direct Nat.mod and Nat.succ notation before rewriting",
        ],
    }:
        raise BalancedBezoutResultV2Error("next boundary changed")
    authority = {"generic_balanced_bezout_credit": 0, "target_specialization_credit": 0, "cancellation_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    manifest_authority = {**authority, "generic_theorem_credit": 0}
    del manifest_authority["generic_balanced_bezout_credit"]
    if result.get("authority") != authority or manifest.get("authority") != manifest_authority:
        raise BalancedBezoutResultV2Error("authority changed")
    if result.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result-v2.py" or result.get("limitations") != "V2 is a source-compilation decline. It establishes no generic theorem, target specialization, cancellation, Fibonacci target, receipt, evaluation result, fact transition, or ledger write.":
        raise BalancedBezoutResultV2Error("verification or limitation changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_V2_DECLINE_OK|compilations=1/2|exports=0|imports=0|retries=0|baseline=3|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutResultV2Error) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-result-v2: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
