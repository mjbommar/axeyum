#!/usr/bin/env python3
"""Validate the two-run Nat.fib_gcd construction V3 authority."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-nat-fib-gcd-construction-plan-v3.json"


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict:
    plan = json.loads(PLAN.read_text())
    authority = plan["authority"]
    for row in authority.values():
        if sha(ROOT / row["path"]) != row["sha256"]:
            raise RuntimeError("construction authority identity changed")
    inputs = plan["inputs"]
    if (
        plan.get("state")
        != "preregistered-two-run-construction-after-complete-proof-type-check"
        or authority["implementation"].get("permitted_source_edits") != 0
        or [row["root"] for row in inputs] != ["Nat.gcd_greatest", "Nat.gcd_fib_add_self"]
        or any(sha(pathlib.Path(row["capsule"])) != row["sha256"] for row in inputs)
        or plan.get("submissions_per_run")
        != ["Axeyum.Autogenesis.fibGcdQuotientIterationV1", "Nat.fib_gcd"]
        or plan.get("budget") != {
            "complete_invocations": 2,
            "capsule_reads": 4,
            "fresh_output_imports": 4,
            "helper_theorem_submissions": 2,
            "target_theorem_submissions": 2,
            "exports": 2,
            "retries": 0,
            "ledger_writes": 0,
        }
        or plan.get("acceptance") != {
            "all_theorem_axiom_footprints": [],
            "outputs_byte_identical": True,
            "target_evidence_byte_identical": True,
            "fact_status_changes": 0,
        }
    ):
        raise RuntimeError("construction inputs, budget, or acceptance changed")
    return plan


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"autogenesis-nat-fib-gcd-construction-plan-v3: FAIL: {error}", file=sys.stderr)
        return 1
    print("AUTOGENESIS_NAT_FIB_GCD_CONSTRUCTION_PLAN_V3_OK|runs=0/2|helper=0/2|target=0/2")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
