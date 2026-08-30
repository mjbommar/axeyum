#!/usr/bin/env python3
"""Validate the corrected residual-first Int.gcd_fib construction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V1 = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v1.json"
V2 = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v2.json"


class PlanError(RuntimeError):
    """The corrected construction boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(V2.read_text())
    residual = plan["residual"]
    specialization = plan["exact_specialization"]
    execution = plan["execution"]
    acceptance = plan["acceptance"]
    authority = plan["authority"]
    predecessor = plan["predecessor"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-gcd-fib-construction-plan-v2"
        or plan.get("state")
        != "preregistered-before-residual-source-construction-or-proof-stream-read"
        or predecessor.get("path") != V1.relative_to(ROOT).as_posix()
        or predecessor.get("sha256") != sha256(V1)
        or residual.get("name")
        != "Axeyum.Autogenesis.intFibNatAbsResidualV1"
        or len(residual.get("explicit_theorem_parameters", [])) != 2
        or specialization.get("output_name")
        != "Axeyum.Autogenesis.intFibNatAbsV1"
    ):
        raise PlanError("plan lineage, residual, or specialization changed")
    inputs = specialization.get("inputs")
    if (
        not isinstance(inputs, list)
        or [item.get("name") for item in inputs]
        != ["Int.fib_neg", "Int.natAbs_neg"]
        or sha256(pathlib.Path(inputs[0]["capsule_path"]))
        != inputs[0].get("capsule_sha256")
        or inputs[1].get("required_axiom_footprint") != []
    ):
        raise PlanError("exact specialization inputs changed")
    if (
        execution
        != {
            "max_lean_compiler_invocations": 1,
            "max_exporter_invocations": 2,
            "max_residual_imports": 2,
            "max_specialization_submissions": 1,
            "max_fresh_exact_imports": 2,
            "max_retries": 0,
            "int_gcd_fib_submissions": 0,
            "ledger_writes": 0,
        }
        or acceptance.get("residual_axiom_footprint") != []
        or acceptance.get("residual_direct_theorem_dependencies") != []
        or acceptance.get("exact_axiom_footprint") != []
        or acceptance.get("proof_bodies_inspected") is not False
        or authority.get("official_target_proof_body_allowed") is not False
        or authority.get("official_int_fib_neg_proof_body_allowed") is not False
        or authority.get("same_name_declaration_transport_allowed") is not False
        or authority.get("fact_status_changes") != 0
        or authority.get("ledger_writes") != 0
    ):
        raise PlanError("execution, acceptance, or authority changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan-v2: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan-v2: PASS: "
        "residual=intFibNatAbsResidualV1|parameters=2|specializations=1|"
        "target_submissions=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
