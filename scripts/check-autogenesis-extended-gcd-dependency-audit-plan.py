#!/usr/bin/env python3
"""Verify the preregistered extended-gcd direct-dependency audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-dependency-audit-plan-v1.json"
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "609241d91-extended-gcd-root-audit-v1/extended-gcd.ndjson"
)
ROOTS = [
    "Eq.trans",
    "Int.mul_zero",
    "Nat.xgcdAux_val",
    "Nat.xgcd_val",
    "_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P",
    "add_zero",
    "congr",
    "congrArg",
    "eq_self",
    "mul_one",
    "of_eq_true",
    "zero_add",
]
CORE = [
    "Nat.xgcdAux_val",
    "Nat.xgcd_val",
    "_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P",
]


class ExtendedGcdDependencyAuditPlanError(RuntimeError):
    """The roots, sealed input, budget, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdDependencyAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-extended-gcd-dependency-audit-plan"
        or plan.get("state")
        != "preregistered-before-twelve-root-sealed-stream-reread-no-reconstruction-authority"
        or plan.get("policy_version")
        != "extended-gcd-direct-dependency-audit-v1"
    ):
        raise ExtendedGcdDependencyAuditPlanError("dependency audit identity changed")
    root_result = plan["inputs"].get("root_result")
    result_path = "artifacts/autogenesis/extended-gcd-root-audit-result-v1.json"
    result_sha = "8e1622b359f9e0c1418cc139036162787c39843cbdff7229cb997bd7adceaa9f"
    if (
        root_result != {"path": result_path, "sha256": result_sha}
        or sha256(ROOT / result_path) != result_sha
    ):
        raise ExtendedGcdDependencyAuditPlanError("root result identity changed")
    if (
        plan["inputs"].get("sealed_stream")
        != {
            "path": str(STREAM),
            "sha256": "97d21c35c8b86c425ce850d2774ed8c60a07ae9a7070c21df536e4e503e400fb",
            "bytes": 2_497_293,
            "mode": "0444",
        }
        or stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 2_497_293
        or sha256(STREAM)
        != "97d21c35c8b86c425ce850d2774ed8c60a07ae9a7070c21df536e4e503e400fb"
    ):
        raise ExtendedGcdDependencyAuditPlanError("sealed stream identity changed")
    if plan.get("fixed_roots") != ROOTS or plan.get("candidate_coefficient_core") != CORE:
        raise ExtendedGcdDependencyAuditPlanError("fixed dependency roots changed")
    measurement = plan.get("fixed_measurement", {})
    if measurement != {
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a",
        "root_order_must_match_plan": True,
        "proof_terms_types_or_values_may_be_rendered": False,
        "all_roots_must_resolve_as_theorems": True,
    } or sha256(ROOT / measurement["tool_path"]) != measurement["tool_sha256"]:
        raise ExtendedGcdDependencyAuditPlanError("fixed measurement changed")
    if plan.get("decision_rule") != {
        "all_candidate_core_empty_next": "preregister an explicit extended-gcd reconstruction from the measured direct interface",
        "candidate_core_assumption_bearing_next": "preregister an audit of exactly the novel direct dependencies of the bearing candidate roots",
        "authorize_either_successor_in_this_increment": False,
    }:
        raise ExtendedGcdDependencyAuditPlanError("successor decision rule changed")
    if plan.get("budget") != {
        "max_exporter_invocations": 0,
        "max_batch_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_reconstruction_source_compilations": 0,
        "max_new_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise ExtendedGcdDependencyAuditPlanError("audit budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "theorem_types_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "reconstruction_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ExtendedGcdDependencyAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/extended-gcd-dependency-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-extended-gcd-dependency-audit-plan.py"
        or plan.get("limitations")
        != "This pass classifies the twelve direct theorem dependencies already present in the sealed stream. It proves and credits no extended-gcd, Bezout, cancellation, or Fibonacci theorem."
    ):
        raise ExtendedGcdDependencyAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_DEPENDENCY_AUDIT_PLAN_OK|roots=12|"
            "exports=0|batch_imports=0/1|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdDependencyAuditPlanError,
    ) as error:
        print(f"autogenesis-extended-gcd-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
