#!/usr/bin/env python3
"""Verify the one-layer subtractive gcd dependency audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-dependency-audit-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/subtractive-gcd-root-audit-result-v1.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "38e40236f-subtractive-gcd-root-audit-v1"
)
MANIFEST = PACK / "manifest.json"
STREAM = PACK / "gcd-roots.ndjson"
RESULT_SHA256 = "c4c2d52cc52f34d168b8894be33ae0074975e9a86685a4774dce6771514d1471"
MANIFEST_SHA256 = "6b03e14eccbbbdf9dbb76750f0f60ba8c045237ba355eea04f436f66cfd39aa0"
STREAM_SHA256 = "ff9916e0d74f1a69f7fee33c3b973cd771e6786715b8ea86699da0a8124ae65b"
TOOL_SHA256 = "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a"


class SubtractiveGcdDependencyAuditPlanError(RuntimeError):
    """The derived population, sealed input, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdDependencyAuditPlanError(f"{path} is not an object")
    return value


def derived_roots(result: dict[str, Any]) -> list[str]:
    measured = {row["name"] for row in result["rows"]}
    union = result["direct_dependency_union"]
    roots = [name for name in union if name not in measured]
    if len(union) != 17 or len(set(union) & measured) != 3 or len(roots) != 14:
        raise SubtractiveGcdDependencyAuditPlanError("dependency derivation changed")
    return roots


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-subtractive-gcd-dependency-audit-plan"
        or plan.get("state")
        != "preregistered-before-sealed-stream-reread-no-replacement-authority"
        or plan.get("policy_version")
        != "subtractive-gcd-direct-dependency-audit-v1"
    ):
        raise SubtractiveGcdDependencyAuditPlanError("dependency audit identity changed")
    result = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256 or plan.get("fixed_roots") != derived_roots(result):
        raise SubtractiveGcdDependencyAuditPlanError("fixed derived roots changed")
    if plan.get("inputs") != {
        "root_audit_result": {
            "path": "artifacts/autogenesis/subtractive-gcd-root-audit-result-v1.json",
            "sha256": RESULT_SHA256,
        },
        "sealed_pack": {
            "path": str(MANIFEST),
            "sha256": MANIFEST_SHA256,
            "mode": "0444",
        },
        "sealed_stream": {
            "path": str(STREAM),
            "sha256": STREAM_SHA256,
            "bytes": 1_152_342,
            "mode": "0444",
        },
    }:
        raise SubtractiveGcdDependencyAuditPlanError("sealed input identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(STREAM.stat().st_mode) != 0o444
        or STREAM.stat().st_size != 1_152_342
        or sha256(STREAM) != STREAM_SHA256
        or sha256(TOOL) != TOOL_SHA256
    ):
        raise SubtractiveGcdDependencyAuditPlanError("sealed resource changed")
    if plan.get("derivation") != {
        "source": "root_audit_result.direct_dependency_union minus root_audit_result.rows names",
        "source_union_population": 17,
        "already_measured_population": 3,
        "fixed_population": 14,
    }:
        raise SubtractiveGcdDependencyAuditPlanError("dependency derivation contract changed")
    if plan.get("fixed_measurement") != {
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": TOOL_SHA256,
        "root_order_must_match_plan": True,
        "proof_terms_types_or_values_may_be_rendered": False,
        "all_roots_must_resolve_as_theorems": True,
    }:
        raise SubtractiveGcdDependencyAuditPlanError("batch measurement changed")
    if plan.get("decision_rule") != {
        "authorize_reconstruction_in_this_increment": False,
        "next_plan_may_reconstruct_only_measured_assumption_carriers": True,
        "prefer_private_gcd_equation_and_general_subtraction_equations_if_empty": True,
    }:
        raise SubtractiveGcdDependencyAuditPlanError("successor rule changed")
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
        raise SubtractiveGcdDependencyAuditPlanError("audit budget changed")
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
        raise SubtractiveGcdDependencyAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-subtractive-gcd-dependency-audit-plan.py"
        or plan.get("limitations")
        != "This pass classifies one dependency layer already present in the sealed stream. It proves no gcd equation, Bezout theorem, cancellation theorem, or Fibonacci target."
    ):
        raise SubtractiveGcdDependencyAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_DEPENDENCY_AUDIT_PLAN_OK|"
            "roots=14|exports=0|batch_imports=0/1|replacements=0|"
            "theorem_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdDependencyAuditPlanError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
