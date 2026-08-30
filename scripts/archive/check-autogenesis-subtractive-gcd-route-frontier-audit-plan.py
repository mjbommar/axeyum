#!/usr/bin/env python3
"""Verify the six-root subtractive gcd route-frontier audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-plan-v1.json"
DEPENDENCY = ROOT / "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json"
SUBTRACTION = ROOT / "artifacts/autogenesis/euclidean-joint-div-mod-dependency-footprint-audit-result-v1.json"
REPLACEMENT = ROOT / "artifacts/autogenesis/euclidean-joint-div-mod-local-subtraction-replacement-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1/gcd-roots.ndjson"
)
DEPENDENCY_SHA256 = "384066c42b6fc1599c869a15ca5da21716cdb508113bc8855763072b95e33092"
SUBTRACTION_SHA256 = "9a27f06239e54fdd4979901c377f8f4675f6ff580d043244360d144aee7b29de"
REPLACEMENT_SHA256 = "3c181eb4c14a37cdb0046c915e3bf04e96f7c6f48f2688448a7a61a871c2dfb1"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
STREAM_SHA256 = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b"


class SubtractiveGcdRouteFrontierAuditPlanError(RuntimeError):
    """The historic binding, derived roots, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdRouteFrontierAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-subtractive-gcd-route-frontier-audit-plan"
        or plan.get("state")
        != "preregistered-before-six-root-sealed-stream-reread-no-replacement-authority"
        or plan.get("policy_version") != "subtractive-gcd-route-frontier-audit-v1"
    ):
        raise SubtractiveGcdRouteFrontierAuditPlanError("route audit identity changed")
    dependency = load(DEPENDENCY)
    subtraction = load(SUBTRACTION)
    replacement = load(REPLACEMENT)
    if (
        sha256(DEPENDENCY) != DEPENDENCY_SHA256
        or sha256(SUBTRACTION) != SUBTRACTION_SHA256
        or sha256(REPLACEMENT) != REPLACEMENT_SHA256
    ):
        raise SubtractiveGcdRouteFrontierAuditPlanError("historical input identity changed")
    subtraction_row = next(
        row for row in subtraction["rows"] if row["name"] == "Nat.sub_add_cancel"
    )
    if (
        subtraction_row["declaration_sha256"]
        != "756d178b67958fe684cb9e64c8d0b40ff557a375ed14ba122c070bfa7b3616a5"
        or subtraction_row["axiom_footprint"] != ["propext"]
        or replacement["knowledge_delta"]["removed_assumption_bearing_dependency"]
        != "Nat.sub_add_cancel"
        or replacement["theorem"]["accepted_private_support"] is not True
        or replacement["theorem"]["axiom_footprint"] != []
    ):
        raise SubtractiveGcdRouteFrontierAuditPlanError("subtraction binding changed")
    frontier = dependency["route_relevant_novel_dependency_frontier"]
    roots = [name for name in frontier if name != "Nat.sub_add_cancel"]
    if len(frontier) != 7 or len(roots) != 6 or plan.get("fixed_roots") != roots:
        raise SubtractiveGcdRouteFrontierAuditPlanError("fixed derived roots changed")
    if (
        stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 1_152_342
        or sha256(STREAM) != STREAM_SHA256
        or sha256(TOOL) != TOOL_SHA256
    ):
        raise SubtractiveGcdRouteFrontierAuditPlanError("sealed resource changed")
    if plan.get("inputs") != {
        "dependency_result": {
            "path": "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json",
            "sha256": DEPENDENCY_SHA256,
        },
        "subtraction_measurement": {
            "path": "artifacts/autogenesis/euclidean-joint-div-mod-dependency-footprint-audit-result-v1.json",
            "sha256": SUBTRACTION_SHA256,
            "name": "Nat.sub_add_cancel",
            "declaration_sha256": "756d178b67958fe684cb9e64c8d0b40ff557a375ed14ba122c070bfa7b3616a5",
            "axiom_footprint": ["propext"],
        },
        "subtraction_replacement": {
            "path": "artifacts/autogenesis/euclidean-joint-div-mod-local-subtraction-replacement-result-v1.json",
            "sha256": REPLACEMENT_SHA256,
            "replacement": "local primitive-recursive subtraction restoration",
            "accepted_private_support": True,
            "axiom_footprint": [],
        },
        "sealed_stream": {
            "path": str(STREAM),
            "sha256": STREAM_SHA256,
            "bytes": 1_152_342,
            "mode": "0444",
        },
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("plan inputs changed")
    if plan.get("derivation") != {
        "source": "dependency_result.route_relevant_novel_dependency_frontier minus already measured Nat.sub_add_cancel",
        "source_population": 7,
        "historically_bound_population": 1,
        "fixed_population": 6,
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("derivation contract changed")
    if plan.get("fixed_measurement") != {
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": TOOL_SHA256,
        "root_order_must_match_plan": True,
        "proof_terms_types_or_values_may_be_rendered": False,
        "all_roots_must_resolve_as_theorems": True,
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("measurement contract changed")
    if plan.get("decision_rule") != {
        "authorize_reconstruction_in_this_increment": False,
        "private_gcd_equation_empty_advances_computational_base": True,
        "assumption_bearing_divisibility_roots_require_further_measurement_or_local_replacement": True,
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("decision rule changed")
    if plan.get("budget") != {
        "max_exporter_invocations": 0,
        "max_batch_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_replacement_source_compilations": 0,
        "max_new_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("audit budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "theorem_types_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "replacement_proof_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise SubtractiveGcdRouteFrontierAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-subtractive-gcd-route-frontier-audit-plan.py"
        or plan.get("limitations")
        != "This pass classifies six new route carriers and reuses an already measured subtraction replacement. It proves no gcd equation, Bezout theorem, cancellation theorem, or Fibonacci target."
    ):
        raise SubtractiveGcdRouteFrontierAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_ROUTE_FRONTIER_AUDIT_PLAN_OK|"
            "roots=6|subtraction_replacement=bound|exports=0|imports=0/1|"
            "replacements=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        StopIteration,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdRouteFrontierAuditPlanError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-route-frontier-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
