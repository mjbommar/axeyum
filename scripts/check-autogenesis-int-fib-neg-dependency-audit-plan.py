#!/usr/bin/env python3
"""Verify the exact Int.fib_neg dependency-audit preregistration."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-plan-v1.json"
ROOT_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-result-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1")
STREAM = PACK / "int-fib-neg.ndjson"
MANIFEST = PACK / "manifest.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"


class IntFibNegDependencyAuditPlanError(RuntimeError):
    """The exact dependency population, evidence, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegDependencyAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (1, "axeyum-autogenesis-int-fib-neg-dependency-audit-plan", "preregistered-before-single-nonrendering-reread-no-reconstruction-authority", "int-fib-neg-dependency-audit-v1"):
        raise IntFibNegDependencyAuditPlanError("dependency audit identity changed")
    if plan.get("inputs", {}).get("root_result") != {"path": "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-result-v1.json", "sha256": "b500a897382de74e1718de52b5a2b965eef64a935e3186219a6d73aab1a7125d"} or sha256(ROOT_RESULT) != "b500a897382de74e1718de52b5a2b965eef64a935e3186219a6d73aab1a7125d":
        raise IntFibNegDependencyAuditPlanError("root result identity changed")
    expected_manifest = {"path": str(MANIFEST), "sha256": "c1ba7157b8f644bbfda48d4db4b4e528eb2705bd7600f0f033304d678f48f3fd"}
    expected_stream = {"path": str(STREAM), "bytes": 14_596_588, "sha256": "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e", "mode": "0444", "textual_read_allowed": False}
    if plan["inputs"].get("pack_manifest") != expected_manifest or sha256(MANIFEST) != expected_manifest["sha256"] or plan["inputs"].get("proof_bearing_stream") != expected_stream or STREAM.stat().st_size != expected_stream["bytes"] or stat.S_IMODE(STREAM.stat().st_mode) != 0o444 or sha256(STREAM) != expected_stream["sha256"]:
        raise IntFibNegDependencyAuditPlanError("sealed input identity changed")
    dependencies = load(ROOT_RESULT)["row"]["direct_theorem_dependencies"]
    if plan.get("ordered_roots") != dependencies or len(dependencies) != 26 or len(set(dependencies)) != 26:
        raise IntFibNegDependencyAuditPlanError("exact dependency population changed")
    if plan.get("fixed_measurement") != {"tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs", "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a", "tool_interface": "theorem_footprint_batch_audit <sealed-stream> <ordered-roots...>", "proof_terms_types_or_values_may_be_rendered": False, "every_root_must_resolve_as_theorem": True} or sha256(TOOL) != "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a":
        raise IntFibNegDependencyAuditPlanError("fixed measurement changed")
    if plan.get("decision_rule") != {"clean_core_next": "preregister the smallest Int.fib_neg reconstruction using only empty-footprint dependencies and explicit target-owned replacements", "contaminated_core_next": "preregister a bounded descent only for assumption-bearing mathematical roots required by the smallest reconstruction", "authorize_either_successor_in_this_increment": False}:
        raise IntFibNegDependencyAuditPlanError("successor decision rule changed")
    if plan.get("budget") != {"max_exporter_invocations": 0, "max_batch_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_reconstruction_source_compilations": 0, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_executor_invocations": 0}:
        raise IntFibNegDependencyAuditPlanError("audit budget changed")
    if plan.get("authority") != {"proof_bodies_readable_by_model": False, "theorem_types_readable_by_model": False, "theorem_values_readable_by_model": False, "reconstruction_allowed": False, "support_theorem_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise IntFibNegDependencyAuditPlanError("audit authority changed")
    if plan.get("output") != "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-int-fib-neg-dependency-audit-plan.py":
        raise IntFibNegDependencyAuditPlanError("output or verification changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_DEPENDENCY_AUDIT_PLAN_OK|roots=26|batch_imports=0/1|reconstructions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegDependencyAuditPlanError) as error:
        print(f"autogenesis-int-fib-neg-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
