#!/usr/bin/env python3
"""Verify the preregistered novel extended-gcd dependency audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-novel-dependency-audit-plan-v1.json"
STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "609241d91-extended-gcd-root-audit-v1/extended-gcd.ndjson"
)
ROOTS = [
    "Nat.xgcd.eq_1",
    "Nat.xgcdAux_fst",
    "Int.add_mul",
    "Int.emod_def",
    "Int.mul_sub",
    "Nat.gcd.induction",
    "Nat.xgcdAux_rec",
    "add_comm",
    "add_sub_assoc",
    "forall_congr",
    "imp_self._simp_1",
    "implies_congr",
    "implies_true",
    "mul_assoc",
    "mul_comm",
    "sub_add_eq_add_sub",
    "sub_sub",
]


class ExtendedGcdNovelDependencyAuditPlanError(RuntimeError):
    """The novel roots, reused evidence, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdNovelDependencyAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-extended-gcd-novel-dependency-audit-plan"
        or plan.get("state")
        != "preregistered-before-seventeen-root-sealed-stream-reread-no-reconstruction-authority"
        or plan.get("policy_version") != "extended-gcd-novel-dependency-audit-v1"
    ):
        raise ExtendedGcdNovelDependencyAuditPlanError("novel audit identity changed")
    for key, path, digest in [
        (
            "dependency_result",
            "artifacts/autogenesis/extended-gcd-dependency-audit-result-v1.json",
            "461eb6066ed5bf8ebd3c07d160c9597d2a4554a7b461fb915666a1c8e2f21459",
        ),
        (
            "established_eq_symm_result",
            "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json",
            "384066c42b6fc1599c869a15ca5da21716cdb508113bc8855763072b95e33092",
        ),
    ]:
        row = plan["inputs"].get(key, {})
        if row.get("path") != path or row.get("sha256") != digest or sha256(ROOT / path) != digest:
            raise ExtendedGcdNovelDependencyAuditPlanError(f"{key} identity changed")
    reused = plan["inputs"]["established_eq_symm_result"]
    if reused != {
        "path": "artifacts/autogenesis/subtractive-gcd-dependency-audit-result-v1.json",
        "sha256": "384066c42b6fc1599c869a15ca5da21716cdb508113bc8855763072b95e33092",
        "declaration_sha256": "fb271ec2ea3431e3c34737664fb7b6e308edb40ce00c7f038724eb0e4a08245f",
        "axiom_footprint": [],
    }:
        raise ExtendedGcdNovelDependencyAuditPlanError("Eq.symm reuse contract changed")
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
        raise ExtendedGcdNovelDependencyAuditPlanError("sealed stream identity changed")
    if plan.get("fixed_roots") != ROOTS or "Eq.symm" in plan["fixed_roots"]:
        raise ExtendedGcdNovelDependencyAuditPlanError("fixed novel roots changed")
    measurement = plan.get("fixed_measurement", {})
    if measurement != {
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a",
        "root_order_must_match_plan": True,
        "proof_terms_types_or_values_may_be_rendered": False,
        "all_roots_must_resolve_as_theorems": True,
    } or sha256(ROOT / measurement["tool_path"]) != measurement["tool_sha256"]:
        raise ExtendedGcdNovelDependencyAuditPlanError("fixed measurement changed")
    if plan.get("decision_rule") != {
        "classify_every_unmeasured_direct_dependency": True,
        "reuse_eq_symm_without_rereading_it": True,
        "next_route_selected_only_from_kernel_footprints": True,
        "authorize_reconstruction_in_this_increment": False,
    }:
        raise ExtendedGcdNovelDependencyAuditPlanError("decision rule changed")
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
        raise ExtendedGcdNovelDependencyAuditPlanError("audit budget changed")
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
        raise ExtendedGcdNovelDependencyAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/extended-gcd-novel-dependency-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-extended-gcd-novel-dependency-audit-plan.py"
        or plan.get("limitations")
        != "This pass classifies seventeen previously unmeasured direct dependencies and reuses one identity-matched Eq.symm result. It proves and credits no theorem."
    ):
        raise ExtendedGcdNovelDependencyAuditPlanError(
            "output or limitation boundary changed"
        )
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_NOVEL_DEPENDENCY_AUDIT_PLAN_OK|"
            "roots=17|reused=1|exports=0|batch_imports=0/1|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdNovelDependencyAuditPlanError,
    ) as error:
        print(f"autogenesis-extended-gcd-novel-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
