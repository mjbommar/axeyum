#!/usr/bin/env python3
"""Verify the exact nine-root balanced-Bezout dependency audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-dependency-audit-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/balanced-bezout-euclidean-update-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
MANIFEST = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/5a2d0d397-balanced-bezout-euclidean-update-v1/manifest.json")
STREAM = MANIFEST.parent / "balanced-bezout-update.ndjson"
BINARY = ROOT / "target/debug/examples/theorem_footprint_batch_audit"
RESULT_SHA256 = "68b8f696d52a4e077f3774ab467b47e7acd7e4ffad87fc2e6d36d846a7241a61"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
MANIFEST_SHA256 = "20c86d1f3bf95b69cb2484e847393f126680f9453406713a0c080e1a8208126c"
STREAM_SHA256 = "85e133b5f0acee922cbbd0a6597bc9824ce8907e4326d76c4a195ac97ad1f44c"
BINARY_SHA256 = "d91507f272aafd6c816d640e42b68aceb3144e3245fe6ebfb4f9dfb14c38e954"
ROOTS = ["Eq.symm", "Eq.trans", "Nat.add_assoc", "Nat.left_distrib", "Nat.mul_assoc", "Nat.right_distrib", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateFourthThenSwapV1", "_private.AxeyumAutogenesisBalancedBezoutEuclideanUpdateV1.0.Axeyum.Autogenesis.rotateLastFiveV1", "congrArg"]


class BalancedBezoutDependencyAuditPlanError(RuntimeError):
    """The exact input, nine-root population, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BalancedBezoutDependencyAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-balanced-bezout-euclidean-update-dependency-audit-plan", "preregistered-exact-nine-root-single-read-no-theorem-credit"):
        raise BalancedBezoutDependencyAuditPlanError("plan identity changed")
    if sha256(RESULT) != RESULT_SHA256 or plan.get("inputs", {}).get("declined_update_result", {}).get("sha256") != RESULT_SHA256:
        raise BalancedBezoutDependencyAuditPlanError("declined result identity changed")
    if sha256(TOOL) != TOOL_SHA256 or plan.get("tool", {}).get("source_sha256") != TOOL_SHA256:
        raise BalancedBezoutDependencyAuditPlanError("audit tool source changed")
    if sha256(BINARY) != BINARY_SHA256 or plan.get("tool", {}).get("binary_sha256") != BINARY_SHA256:
        raise BalancedBezoutDependencyAuditPlanError("audit binary changed")
    if sha256(MANIFEST) != MANIFEST_SHA256 or sha256(STREAM) != STREAM_SHA256 or stat.S_IMODE(MANIFEST.parent.stat().st_mode) != 0o555:
        raise BalancedBezoutDependencyAuditPlanError("sealed evidence input changed")
    if plan.get("ordered_roots") != ROOTS or len(set(ROOTS)) != 9:
        raise BalancedBezoutDependencyAuditPlanError("ordered nine-root population changed")
    budget = {"max_compiler_invocations": 0, "max_exporter_invocations": 0, "max_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_new_theorem_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise BalancedBezoutDependencyAuditPlanError("execution budget changed")
    if plan.get("tool", {}).get("renders_proof_terms_types_or_values") is not False or plan.get("execution", {}).get("input_stream_may_not_be_copied_or_rendered") is not True or plan.get("execution", {}).get("source_compilation_or_export_authorized") is not False:
        raise BalancedBezoutDependencyAuditPlanError("non-rendering boundary changed")
    authority = plan.get("authority", {})
    if authority.get("dependency_classification_credit") != 1:
        raise BalancedBezoutDependencyAuditPlanError("classification authority changed")
    for key in ("euclidean_update_credit", "generic_balanced_bezout_credit", "target_specialization_credit", "cancellation_credit", "fact_status_changes", "evaluation_credit", "ledger_writes"):
        if authority.get(key) != 0:
            raise BalancedBezoutDependencyAuditPlanError(f"{key} must remain zero")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_BALANCED_BEZOUT_DEPENDENCY_AUDIT_PLAN_OK|roots=9|imports<=1|stream_reads<=1|rendered=0|theorem_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, BalancedBezoutDependencyAuditPlanError) as error:
        print(f"autogenesis-balanced-bezout-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
