#!/usr/bin/env python3
"""Verify the public Euclidean equation carrier audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/euclidean-public-equation-carrier-audit-plan-v1.json"
PARENT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-bounded-induction-dependency-audit-result-v1.json"
)
POPULATION = [
    "Eq.symm",
    "Eq.trans",
    "Nat.div.go.eq_1",
    "Nat.div_rec_fuel_lemma",
    "Nat.lt_succ_self",
    "Nat.modCore_eq",
    "Nat.modCore_eq_mod",
    "_private.Init.Data.Nat.Div.Basic.0.Nat.div.go.fuel_congr",
    "and_false",
    "and_self",
    "congr",
    "congrArg",
    "congrFun'",
    "dif_neg",
    "dif_pos",
    "eq_false",
    "eq_self",
    "eq_true",
    "false_and",
    "ite_cond_eq_false",
    "ite_cond_eq_true",
    "ite_congr",
    "of_eq_true",
]


class EquationCarrierAuditPlanError(RuntimeError):
    """The child population, immutable input, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise EquationCarrierAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-euclidean-public-equation-carrier-audit-plan"
        or plan.get("state")
        != "preregistered-before-one-importer-audit-no-replacement-authority"
        or plan.get("policy_version")
        != "euclidean-public-equation-direct-closure-audit-v1"
    ):
        raise EquationCarrierAuditPlanError("equation carrier audit identity changed")
    if sha256(PARENT) != "bd839c84c4ec29d2a6a3a0615e14e8c6c32e42d7a949bf9a37930167695e3c07":
        raise EquationCarrierAuditPlanError("parent audit identity changed")
    parent = load(PARENT)
    rows = {row["name"]: row for row in parent["rows"]}
    derived = sorted(
        set(rows["Nat.div_eq"]["direct_theorem_dependencies"])
        | set(rows["Nat.mod_eq"]["direct_theorem_dependencies"])
    )
    if derived != POPULATION or plan.get("fixed_population") != derived:
        raise EquationCarrierAuditPlanError("direct child population changed")
    inputs = plan["inputs"]
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
            raise EquationCarrierAuditPlanError(f"{key} changed or is mutable")
    if inputs["proof_bearing_stream"].get("textual_read_allowed") is not False:
        raise EquationCarrierAuditPlanError("proof-bearing stream became model-readable")
    measurement = plan["fixed_measurement"]
    if (
        measurement.get("tool_path")
        != "crates/axeyum-lean-import/examples/euclidean_public_equation_carrier_audit.rs"
        or measurement.get("population_relation")
        != "sorted set union of the two parent carriers' direct theorem dependencies"
        or measurement.get("proof_terms_or_values_may_be_rendered") is not False
        or measurement.get("all_population_names_must_resolve_as_theorems") is not True
        or measurement.get("aggregate_must_equal_per_declaration_rows") is not True
    ):
        raise EquationCarrierAuditPlanError("fixed measurement changed")
    if plan["budget"] != {
        "max_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_replacement_source_compilations": 0,
        "max_new_authored_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise EquationCarrierAuditPlanError("audit budget changed")
    if plan["authority"] != {
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "public_equation_replacement_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise EquationCarrierAuditPlanError("audit authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_EQUATION_CARRIER_AUDIT_PLAN_OK|"
            "parents=2|population=23|importer_runs=0/1|replacements=0|"
            "target_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        EquationCarrierAuditPlanError,
    ) as error:
        print(f"autogenesis-euclidean-equation-carrier-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
