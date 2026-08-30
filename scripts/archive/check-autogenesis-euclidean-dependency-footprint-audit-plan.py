#!/usr/bin/env python3
"""Verify the preregistered Euclidean dependency-footprint audit."""

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
    "euclidean-joint-div-mod-dependency-footprint-audit-plan-v1.json"
)
POPULATION = [
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div.go.eq_1",
    "Nat.div_rec_fuel_lemma",
    "Nat.modCore.go.eq_1",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_lt_zero",
    "Nat.sub_add_cancel",
    "congr",
    "congrArg",
    "congrFun'",
    "dif_neg",
    "dif_pos",
]


class AuditPlanError(RuntimeError):
    """The audit population, budget, input, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-euclidean-dependency-footprint-audit-plan"
        or plan.get("state") != "preregistered-before-importer-audit-no-proof-authority"
        or plan.get("policy_version") != "euclidean-first-decline-direct-dependency-audit-v1"
    ):
        raise AuditPlanError("audit plan identity changed")
    inputs = plan["inputs"]
    decline = inputs["decline_result"]
    if (
        decline.get("sha256")
        != "70bcd809a42774c75956c7f9cf0a89db0f847a2d03be3fb309fcd8084e8798ce"
        or sha256(ROOT / decline["path"]) != decline["sha256"]
    ):
        raise AuditPlanError("decline result identity changed")
    for key, expected in {
        "evidence_manifest": (
            "f4dfdeec6ec422bf63748e4a6629d128d3b8487d82da9fb2df92d8db96312601",
            None,
        ),
        "proof_bearing_stream": (
            "b4793d50d2ef0d69786d28d044012f74d5f5f2279bf5d5a55e39acf0ffb1af7a",
            460363,
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
            raise AuditPlanError(f"{key} changed or is mutable")
    if inputs["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise AuditPlanError("proof-bearing stream became model-readable")
    if plan.get("fixed_population") != POPULATION:
        raise AuditPlanError("fixed dependency population changed")
    measurement = plan["fixed_measurement"]
    if (
        measurement.get("per_declaration_fields")
        != ["name", "declaration_sha256", "axiom_footprint", "direct_theorem_dependencies"]
        or measurement.get("classes")
        != ["empty-footprint", "propext-bearing", "other-assumption-bearing"]
        or measurement.get("proof_terms_or_values_may_be_rendered") is not False
        or measurement.get("all_population_names_must_resolve_as_theorems") is not True
        or measurement.get("aggregate_must_equal_per_declaration_rows") is not True
    ):
        raise AuditPlanError("fixed measurement changed")
    if plan["budget"] != {
        "max_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_revised_proof_compilations": 0,
        "max_new_authored_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise AuditPlanError("audit budget changed")
    if plan["authority"] != {
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "revised_euclidean_proof_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise AuditPlanError("audit authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_DEPENDENCY_AUDIT_PLAN_OK|population=15|"
            "importer_runs=0/1|revised_proofs=0|target_submissions=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, AuditPlanError) as error:
        print(f"autogenesis-euclidean-dependency-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
