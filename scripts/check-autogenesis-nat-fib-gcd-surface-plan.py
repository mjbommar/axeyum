#!/usr/bin/env python3
"""Validate the proof-free Nat.fib_gcd surface-audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-surface-plan-v1.json"


class PlanError(RuntimeError):
    """The frozen audit scope or authority changed."""


def byte_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    target = plan.get("target") or {}
    inputs = plan.get("accepted_inputs")
    audit = plan.get("audit") or {}
    budget = plan.get("budget") or {}
    acceptance = plan.get("acceptance") or {}
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-nat-fib-gcd-surface-plan-v1"
        or plan.get("state")
        != "preregistered-proof-free-surface-audit-before-driver-change-or-stream-read"
        or target.get("fact_id") != "F:ml430-nat-fib-gcd-d1d98407"
        or target.get("name") != "Nat.fib_gcd"
        or target.get("statement")
        != "∀ (m n : ℕ), Nat.fib (m.gcd n) = (Nat.fib m).gcd (Nat.fib n)"
        or target.get("direct_unlocks")
        != ["F:ml430-int-gcd-fib-73bdafc2", "F:ml430-nat-fib-dvd-f80f3de1"]
    ):
        raise PlanError("target identity or strategic fanout changed")
    fact_path = ROOT / "artifacts/facts/F-ml430-nat-fib-gcd-d1d98407.json"
    if byte_digest(fact_path) != target.get("fact_file_sha256"):
        raise PlanError("target fact bytes changed before the audit")
    if not isinstance(inputs, list) or [row.get("theorem") for row in inputs] != [
        "Nat.gcd_greatest",
        "Nat.gcd_fib_add_self",
    ]:
        raise PlanError("accepted root set changed")
    for row in inputs:
        manifest = ROOT / row["admission_manifest"]
        capsule = pathlib.Path(row["capsule"])
        if (
            byte_digest(manifest) != row.get("admission_manifest_sha256")
            or byte_digest(capsule) != row.get("capsule_sha256")
            or capsule.stat().st_mode & 0o222
            or capsule.parent.stat().st_mode & 0o222
        ):
            raise PlanError(f"accepted input identity or immutability changed: {row['theorem']}")
    if (
        audit.get("operation")
        != "compose-two-root-selected-capsules-and-report-named-surface-v1"
        or len(audit.get("candidate_names") or []) != 12
        or audit.get("required_observations", [])[-1:] != [
            "zero target theorem submissions"
        ]
        or budget
        != {
            "driver_builds": 1,
            "complete_audits": 1,
            "capsule_reads": 2,
            "fresh_imports": 2,
            "proof_search_invocations": 0,
            "helper_theorem_submissions": 0,
            "target_theorem_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
        or acceptance
        != {
            "both_admitted_roots_present": True,
            "all_present_theorems_have_empty_axiom_footprints": True,
            "output_is_non_authoritative_diagnostic_only": True,
            "target_credit": 0,
        }
    ):
        raise PlanError("audit budget or non-authority boundary changed")
    return plan


def main() -> int:
    try:
        plan = validate()
    except (OSError, ValueError, KeyError, TypeError, PlanError) as error:
        print(f"autogenesis-nat-fib-gcd-surface-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_FIB_GCD_SURFACE_PLAN_OK|"
        f"target={plan['target']['name']}|roots=2|candidates=12|"
        "audits=0/1|submissions=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
