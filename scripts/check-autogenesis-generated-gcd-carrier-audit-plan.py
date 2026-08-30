#!/usr/bin/env python3
"""Verify the single generated gcd carrier audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/generated-gcd-carrier-audit-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1/gcd-roots.ndjson"
)
RESULT_SHA256 = "bb53a104cfe76b46d3fed31b521682c6721389fd98c8812d3f1855cb71dabe3b"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"
STREAM_SHA256 = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b"


class GeneratedGcdCarrierAuditPlanError(RuntimeError):
    """The generated root, sealed input, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise GeneratedGcdCarrierAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind") != "axeyum-autogenesis-generated-gcd-carrier-audit-plan"
        or plan.get("state")
        != "preregistered-before-single-carrier-sealed-stream-reread-no-reconstruction-authority"
        or plan.get("policy_version") != "generated-gcd-carrier-audit-v1"
    ):
        raise GeneratedGcdCarrierAuditPlanError("carrier audit identity changed")
    result = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise GeneratedGcdCarrierAuditPlanError("route result identity changed")
    expected_root = result["generated_gcd_carrier"]["name"]
    if (
        result["generated_gcd_carrier"]["direct_dependency_audit_pending"] is not True
        or plan.get("fixed_roots") != [expected_root]
    ):
        raise GeneratedGcdCarrierAuditPlanError("fixed generated root changed")
    if (
        stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 1_152_342
        or sha256(STREAM) != STREAM_SHA256
        or sha256(TOOL) != TOOL_SHA256
    ):
        raise GeneratedGcdCarrierAuditPlanError("sealed resource changed")
    if plan.get("inputs") != {
        "route_result": {
            "path": "artifacts/autogenesis/subtractive-gcd-route-frontier-audit-result-v1.json",
            "sha256": RESULT_SHA256,
        },
        "sealed_stream": {
            "path": str(STREAM),
            "sha256": STREAM_SHA256,
            "bytes": 1_152_342,
            "mode": "0444",
        },
    }:
        raise GeneratedGcdCarrierAuditPlanError("plan inputs changed")
    if plan.get("fixed_measurement") != {
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": TOOL_SHA256,
        "root_order_must_match_plan": True,
        "proof_terms_types_or_values_may_be_rendered": False,
        "all_roots_must_resolve_as_theorems": True,
    }:
        raise GeneratedGcdCarrierAuditPlanError("measurement contract changed")
    if plan.get("decision_rule") != {
        "authorize_reconstruction_in_this_increment": False,
        "generic_well_founded_carrier_allows_later_primitive_reconstruction_plan": True,
        "broader_assumption_closure_prefers_target_owned_gcd_bridge": True,
    }:
        raise GeneratedGcdCarrierAuditPlanError("decision rule changed")
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
        raise GeneratedGcdCarrierAuditPlanError("audit budget changed")
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
        raise GeneratedGcdCarrierAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/generated-gcd-carrier-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-generated-gcd-carrier-audit-plan.py"
        or plan.get("limitations")
        != "This pass classifies one generated theorem and its direct dependencies. It neither reconstructs an equation nor proves a gcd, Bezout, cancellation, or Fibonacci theorem."
    ):
        raise GeneratedGcdCarrierAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_GENERATED_GCD_CARRIER_AUDIT_PLAN_OK|roots=1|"
            "exports=0|imports=0/1|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        GeneratedGcdCarrierAuditPlanError,
    ) as error:
        print(f"autogenesis-generated-gcd-carrier-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
