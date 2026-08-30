#!/usr/bin/env python3
"""Verify the official-gcd balanced-Bezout compilation decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v1.json"
MANIFEST = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "72bbf331d-official-gcd-balanced-bezout-v1/manifest.json"
)
PLAN_SHA256 = "f7e1c432e25c1e47f42eddd18a4686f58e6de9df855e612c5e8d6723357def4e"
MANIFEST_SHA256 = "958d0a12b25c94f667d7ad1418d223c58e37098f31a474168f1fcc4370e16e1c"
DIAGNOSTICS = [
    "direct Nat.mod equation rewrite did not match elaborated HMod notation",
    "successor Nat.mod equation rewrite did not match elaborated HMod notation",
    "global quotient-equation rewrite also changed the gcd remainder subterm",
]


class BalancedBezoutResultError(RuntimeError):
    """The measured decline, immutable evidence, cleanup, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-official-gcd-balanced-bezout-reconstruction-result"
        or result.get("state")
        != "main-source-compilation-declined-no-retry-no-theorem-credit"
    ):
        raise BalancedBezoutResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA256 or result.get("plan") != {
        "path": "artifacts/autogenesis/official-gcd-balanced-bezout-reconstruction-plan-v1.json",
        "sha256": PLAN_SHA256,
        "commit": "3af768dc5274984cc0f66a07ec1d3b890b9ffcec",
    }:
        raise BalancedBezoutResultError("preregistered plan identity changed")
    if (
        sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or result.get("evidence_pack")
        != {
            "path": str(MANIFEST),
            "sha256": MANIFEST_SHA256,
            "directory_mode": "0555",
            "file_mode": "0444",
        }
    ):
        raise BalancedBezoutResultError("immutable evidence identity or mode changed")
    manifest = load(MANIFEST)
    if (
        manifest.get("state") != "main-source-compilation-declined-no-export-or-import"
        or manifest.get("execution")
        != {
            "source_copies": 2,
            "compiler_invocations": 2,
            "successful_compilations": 1,
            "failed_compilations": 1,
            "exporter_invocations": 0,
            "importer_runs": 0,
            "proof_bearing_stream_reads": 0,
            "retries_after_compilation": 0,
            "shell_preflight_failures_before_compiler": 1,
            "shell_preflight_failure": "non-login ssh PATH omitted lake; absolute pinned lake path was then used for the two compiler invocations",
        }
        or manifest.get("diagnostics", {}).get("classes") != DIAGNOSTICS
        or manifest.get("diagnostics", {}).get("proof_material_rendered") is not False
    ):
        raise BalancedBezoutResultError("manifest execution or diagnostic record changed")
    execution = {
        key: manifest["execution"][key]
        for key in [
            "source_copies",
            "compiler_invocations",
            "successful_compilations",
            "failed_compilations",
            "exporter_invocations",
            "importer_runs",
            "proof_bearing_stream_reads",
            "retries_after_compilation",
            "shell_preflight_failures_before_compiler",
        ]
    }
    if result.get("execution") != execution:
        raise BalancedBezoutResultError("execution counts changed")
    if result.get("result") != {
        "accepted_private_support_recompiled": True,
        "generic_main_source_compiled": False,
        "generic_theorems_reconstructed": 0,
        "diagnostic_count": 3,
        "diagnostic_classes": DIAGNOSTICS,
        "proof_material_rendered": False,
    }:
        raise BalancedBezoutResultError("measured compilation result changed")
    expected_cleanup = {
        "exact_temporary_paths_removed": 6,
        "preexisting_status_entries_before": 3,
        "preexisting_status_entries_after": 3,
        "preexisting_baseline_unchanged": True,
    }
    if result.get("cleanup") != expected_cleanup or manifest.get("cleanup") != expected_cleanup:
        raise BalancedBezoutResultError("cleanup record changed")
    if result.get("next_boundary") != {
        "requires_new_preregistration": True,
        "source_corrections": [
            "state the quotient witness with direct Nat.mod applications so Nat.mod.eq_1 and Nat.mod.eq_2 match",
            "transport only the dividend factors across the quotient equation instead of globally rewriting n",
        ],
        "reuse_successful_private_support_compilation_as_theorem_credit": False,
    }:
        raise BalancedBezoutResultError("next source boundary changed")
    authority = {
        "generic_balanced_bezout_credit": 0,
        "target_specialization_credit": 0,
        "cancellation_credit": 0,
        "exact_fibonacci_target_submissions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }
    manifest_authority = {
        "generic_theorem_credit": 0,
        "target_specialization_credit": 0,
        "cancellation_credit": 0,
        "exact_fibonacci_target_submissions": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }
    if result.get("authority") != authority or manifest.get("authority") != manifest_authority:
        raise BalancedBezoutResultError("zero-credit authority changed")
    if (
        result.get("verification")
        != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-reconstruction-result.py"
        or result.get("limitations")
        != "This is a source-compilation decline. It establishes no quotient witness, balanced Bezout theorem, closed target specialization, cancellation theorem, Fibonacci target, receipt, evaluation result, fact transition, or ledger write."
    ):
        raise BalancedBezoutResultError("verification or limitation changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_DECLINE_OK|"
            "compilations=1/2|exports=0|imports=0|retries=0|baseline=3|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        BalancedBezoutResultError,
    ) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
