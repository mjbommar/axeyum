#!/usr/bin/env python3
"""Verify the bounded-induction dependency-footprint audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-bounded-induction-dependency-audit-plan-v1.json"
)
POPULATION = [
    "And.left",
    "And.right",
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div_eq",
    "Nat.le_of_lt_succ",
    "Nat.le_of_succ_le_succ",
    "Nat.le_or_eq_of_le_succ",
    "Nat.le_refl",
    "Nat.lt_of_lt_of_le",
    "Nat.mod_eq",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_succ_le_zero",
    "Nat.sub_lt",
    "Nat.succ_sub_succ_eq_sub",
    "congr",
    "congrArg",
    "congrFun'",
    "if_neg",
    "if_pos",
]


class BoundedAuditPlanError(RuntimeError):
    """The audit population, immutable input, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BoundedAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-euclidean-bounded-induction-dependency-audit-plan"
        or plan.get("state")
        != "preregistered-before-one-importer-audit-no-proof-authority"
        or plan.get("policy_version")
        != "euclidean-bounded-induction-direct-dependency-audit-v1"
    ):
        raise BoundedAuditPlanError("bounded dependency audit identity changed")
    inputs = plan["inputs"]
    decline = inputs["decline_result"]
    if (
        decline.get("sha256")
        != "2c7d1a812042c9df6c14b854647d4ad7586c39f51e91d35d2ea5260dbba91b68"
        or sha256(ROOT / decline["path"]) != decline["sha256"]
    ):
        raise BoundedAuditPlanError("bounded-induction decline identity changed")
    for key, expected in {
        "evidence_manifest": (
            "e8c273c1550eeffbe1fd775a667a75c18539140880ab8c15f344d3a22df39054",
            None,
        ),
        "proof_bearing_stream": (
            "d71692e97b7bae7ab43043ed4490a79b2134650b4bfe4d8e20220693fe033844",
            715764,
        ),
    }.items():
        row = inputs[key]
        path = pathlib.Path(row["path"])
        if (
            row.get("sha256") != expected[0]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or sha256(path) != expected[0]
            or (expected[1] is not None and path.stat().st_size != expected[1])
        ):
            raise BoundedAuditPlanError(f"{key} changed or is mutable")
    if inputs["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise BoundedAuditPlanError("proof-bearing stream became model-readable")
    if plan.get("fixed_population") != POPULATION:
        raise BoundedAuditPlanError("fixed dependency population changed")
    measurement = plan["fixed_measurement"]
    if (
        measurement.get("tool_path")
        != "crates/axeyum-lean-import/examples/euclidean_bounded_dependency_footprint_audit.rs"
        or measurement.get("per_declaration_fields")
        != ["name", "declaration_sha256", "axiom_footprint", "direct_theorem_dependencies"]
        or measurement.get("classes")
        != ["empty-footprint", "propext-bearing", "other-assumption-bearing"]
        or measurement.get("proof_terms_or_values_may_be_rendered") is not False
        or measurement.get("all_population_names_must_resolve_as_theorems") is not True
        or measurement.get("aggregate_must_equal_per_declaration_rows") is not True
    ):
        raise BoundedAuditPlanError("fixed measurement changed")
    if plan["known_before_audit"] != {
        "target_footprint": ["propext"],
        "generated_recursion_dependencies": [],
        "exact_carrier_population": "unknown",
    }:
        raise BoundedAuditPlanError("pre-audit knowledge changed")
    if plan["budget"] != {
        "max_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_revised_proof_compilations": 0,
        "max_new_authored_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise BoundedAuditPlanError("audit budget changed")
    if plan["authority"] != {
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "revised_euclidean_proof_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise BoundedAuditPlanError("audit authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_BOUNDED_DEPENDENCY_AUDIT_PLAN_OK|"
            "population=22|importer_runs=0/1|revised_proofs=0|"
            "target_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        BoundedAuditPlanError,
    ) as error:
        print(f"autogenesis-euclidean-bounded-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
