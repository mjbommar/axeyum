#!/usr/bin/env python3
"""Verify the exact Int.fib_neg_natCast dependency-audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-natcast-dependency-audit-plan-v1.json"
PARENT_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-result-v1.json"
PARENT_AUDIT = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-dependency-audit-v1/audit.json")
STREAM = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1/int-fib-neg.ndjson")
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"


class IntFibNegNatcastDependencyAuditPlanError(RuntimeError):
    """The exact child frontier, sealed evidence, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegNatcastDependencyAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (1, "axeyum-autogenesis-int-fib-neg-natcast-dependency-audit-plan", "preregistered-before-single-nonrendering-reread-no-reconstruction-authority", "int-fib-neg-natcast-dependency-audit-v1"):
        raise IntFibNegNatcastDependencyAuditPlanError("audit identity changed")
    if plan.get("inputs", {}).get("parent_result") != {"path": "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-result-v1.json", "sha256": "51207e379248e6af00095be478fe0963f157113bf2df757aa2a26c4804aeac9a"} or sha256(PARENT_RESULT) != "51207e379248e6af00095be478fe0963f157113bf2df757aa2a26c4804aeac9a" or plan["inputs"].get("parent_audit") != {"path": str(PARENT_AUDIT), "sha256": "1b39ac55f6993a7a740c7dc88ae50a4d70cd798cfeff9944a077f06837173832"} or sha256(PARENT_AUDIT) != "1b39ac55f6993a7a740c7dc88ae50a4d70cd798cfeff9944a077f06837173832":
        raise IntFibNegNatcastDependencyAuditPlanError("parent evidence changed")
    expected_stream = {"path": str(STREAM), "bytes": 14_596_588, "sha256": "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e", "mode": "0444", "textual_read_allowed": False}
    if plan["inputs"].get("proof_bearing_stream") != expected_stream or STREAM.stat().st_size != expected_stream["bytes"] or stat.S_IMODE(STREAM.stat().st_mode) != 0o444 or sha256(STREAM) != expected_stream["sha256"]:
        raise IntFibNegNatcastDependencyAuditPlanError("sealed stream changed")
    parent_rows = {row["name"]: row for row in load(PARENT_AUDIT)["rows"]}
    dependencies = parent_rows["Int.fib_neg_natCast"]["direct_theorem_dependencies"]
    if plan.get("parent_root") != "Int.fib_neg_natCast" or plan.get("ordered_roots") != dependencies or len(dependencies) != 36 or len(set(dependencies)) != 36:
        raise IntFibNegNatcastDependencyAuditPlanError("exact child frontier changed")
    if plan.get("fixed_measurement") != {"tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs", "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a", "tool_interface": "theorem_footprint_batch_audit <sealed-stream> <ordered-roots...>", "proof_terms_types_or_values_may_be_rendered": False, "every_root_must_resolve_as_theorem": True} or sha256(TOOL) != "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a":
        raise IntFibNegNatcastDependencyAuditPlanError("measurement changed")
    if plan.get("decision_rule") != {"next": "select the smallest parity-sign recurrence proof over empty-footprint roots and preregister explicit replacements for only indispensable contaminated roots", "authorize_successor_in_this_increment": False}:
        raise IntFibNegNatcastDependencyAuditPlanError("successor decision changed")
    if plan.get("budget") != {"max_exporter_invocations": 0, "max_batch_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_reconstruction_source_compilations": 0, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_executor_invocations": 0}:
        raise IntFibNegNatcastDependencyAuditPlanError("audit budget changed")
    if plan.get("authority") != {"proof_bodies_readable_by_model": False, "theorem_types_readable_by_model": False, "theorem_values_readable_by_model": False, "reconstruction_allowed": False, "support_theorem_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise IntFibNegNatcastDependencyAuditPlanError("audit authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_NATCAST_DEPENDENCY_AUDIT_PLAN_OK|roots=36|batch_imports=0/1|reconstructions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegNatcastDependencyAuditPlanError) as error:
        print(f"autogenesis-int-fib-neg-natcast-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
