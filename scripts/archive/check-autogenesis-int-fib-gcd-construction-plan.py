#!/usr/bin/env python3
"""Validate the exact Int.fib_gcd construction boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-construction-plan-v1.json"


class PlanError(RuntimeError):
    """The preregistered construction boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-gcd-construction-plan-v1"
        or plan.get("state")
        != "preregistered-before-source-construction-or-proof-stream-read"
    ):
        raise PlanError("plan identity changed")

    facts = plan["facts"]
    for role, fact_id, status in (
        ("premise", "F:ml430-int-gcd-fib-73bdafc2", "proved"),
        ("target", "F:ml430-int-fib-gcd-3a8bfdec", "open"),
    ):
        spec = facts[role]
        path = ROOT / spec["path"]
        fact = json.loads(path.read_text())
        if (
            spec.get("fact_id") != fact_id
            or spec.get("required_status") != status
            or fact.get("id") != fact_id
            or fact.get("epistemic_status") != status
            or sha256(path) != spec.get("sha256")
        ):
            raise PlanError(f"{role} fact authority changed")

    premise = facts["premise"]
    premise_fact = json.loads((ROOT / premise["path"]).read_text())
    if premise.get("operation_id") not in {
        item.get("checker_operation", {}).get("id")
        for item in premise_fact.get("evidence", [])
    }:
        raise PlanError("premise operation evidence is absent")

    input_spec = plan["input"]
    input_path = pathlib.Path(input_spec["path"])
    if (
        input_spec.get("root") != "Int.gcd_fib"
        or input_spec.get("declaration_sha256")
        != "44660dc7f15cda1b469f99e349f4b874afca9dbca24bcfc5c847ca226ccc357f"
        or input_spec.get("required_support")
        != {
            "name": "Int.fib_natCast",
            "declaration_sha256": "73b8742709bbb1b91780f41ff4a475b5b3f0b1c2981999c868b53fc38334bea3",
        }
        or input_path.stat().st_size != input_spec.get("bytes")
        or sha256(input_path) != input_spec.get("sha256")
    ):
        raise PlanError("sealed input identity changed")

    target = plan["target"]
    execution = plan["execution"]
    acceptance = plan["acceptance"]
    authority = plan["authority"]
    if (
        target.get("name") != "Int.fib_gcd"
        or target.get("expected_direct_theorem_dependencies")
        != ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]
        or execution
        != {
            "max_complete_invocations": 1,
            "max_input_stream_reads": 1,
            "max_target_theorem_submissions": 1,
            "max_target_exports": 1,
            "required_fresh_imports": 2,
            "max_retries": 0,
            "max_ledger_writes": 0,
        }
        or acceptance.get("target_axiom_footprint") != []
        or acceptance.get("exact_dependency_set") is not True
        or acceptance.get("fresh_imports") != 2
        or acceptance.get("proof_terms_types_or_values_rendered") != 0
        or authority.get("official_target_proof_body_allowed") is not False
        or authority.get("same_name_declaration_transport_allowed") is not False
        or authority.get("fact_status_changes") != 0
        or authority.get("ledger_writes") != 0
    ):
        raise PlanError("construction, execution, or trust boundary changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-gcd-construction-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-gcd-construction-plan: PASS: "
        "premise=Int.gcd_fib|target=Int.fib_gcd|dependencies=4|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
