#!/usr/bin/env python3
"""Validate the first exact Int.gcd_fib construction boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v1.json"


class PlanError(RuntimeError):
    """The preregistered construction boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    target = plan["target"]
    target_path = ROOT / target["fact_path"]
    target_fact = json.loads(target_path.read_text())
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-gcd-fib-construction-plan-v1"
        or plan.get("state")
        != "preregistered-before-source-construction-or-proof-stream-read"
        or target.get("fact_id") != "F:ml430-int-gcd-fib-73bdafc2"
        or target.get("name") != "Int.gcd_fib"
        or target.get("required_status") != "open"
        or target_fact.get("epistemic_status") != "open"
        or sha256(target_path) != target.get("fact_sha256")
    ):
        raise PlanError("target identity or open status changed")

    expected = {
        "F:ml430-int-fib-neg-b4021d37": (
            "authoritative-mathlib-int-fib-neg-kernel-capsule-v1",
            "d787dc502dff901cab0cab22bf8fd11578bf6e1632892651b1bf67b3d786d257",
        ),
        "F:ml430-nat-fib-gcd-d1d98407": (
            "authoritative-mathlib-nat-fib-gcd-kernel-capsule-v1",
            "8ac3c35874540a10e5fa393c65f3ad313a6cf6a06303cec68fec3ec45d0f04cd",
        ),
    }
    premises = plan.get("settled_premises")
    if not isinstance(premises, list) or len(premises) != 2:
        raise PlanError("expected exactly two settled premises")
    for premise in premises:
        fact_id = premise.get("fact_id")
        if fact_id not in expected:
            raise PlanError(f"unexpected premise {fact_id}")
        fact_path = ROOT / "artifacts" / "facts" / f"{fact_id.replace(':', '-')}.json"
        fact = json.loads(fact_path.read_text())
        operation, capsule_sha = expected[fact_id]
        evidence_operations = {
            item.get("checker_operation", {}).get("id")
            for item in fact.get("evidence", [])
        }
        capsule_path = pathlib.Path(premise["capsule_path"])
        if (
            fact.get("epistemic_status") != "proved"
            or sha256(fact_path) != premise.get("fact_sha256")
            or premise.get("operation_id") != operation
            or operation not in evidence_operations
            or premise.get("capsule_sha256") != capsule_sha
            or sha256(capsule_path) != capsule_sha
        ):
            raise PlanError(f"settled premise authority changed for {fact_id}")

    construction = plan["construction"]
    acceptance = plan["acceptance"]
    authority = plan["authority"]
    if (
        construction.get("first_bridge_name")
        != "Axeyum.Autogenesis.intFibNatAbsV1"
        or construction.get("first_bridge_statement")
        != "∀ (m : ℤ), (Int.fib m).natAbs = Nat.fib m.natAbs"
        or construction.get("max_lean_compiler_invocations") != 1
        or construction.get("max_exporter_invocations") != 2
        or construction.get("max_proof_stream_reads") != 2
        or construction.get("max_retries") != 0
        or construction.get("target_theorem_submissions") != 0
        or construction.get("ledger_writes") != 0
        or acceptance.get("bridge_axiom_footprint") != []
        or acceptance.get("proof_bodies_inspected") is not False
        or authority.get("official_target_proof_body_allowed") is not False
        or authority.get("same_name_declaration_transport_allowed") is not False
        or authority.get("fact_status_changes") != 0
        or authority.get("ledger_writes") != 0
    ):
        raise PlanError("construction budget, acceptance, or authority changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan: PASS: "
        "target=Int.gcd_fib|bridge=IntFibNatAbsV1|premises=2|"
        "target_submissions=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
