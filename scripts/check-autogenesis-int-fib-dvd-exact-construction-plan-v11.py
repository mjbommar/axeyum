#!/usr/bin/env python3
"""Validate the exact five-repair Int.fib_dvd driver plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-plan-v11.json"


class PlanError(RuntimeError):
    """The bounded driver repair changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-construction-plan-v11"
        or plan.get("state")
        != "preregistered-five-driver-build-repairs-before-code-change"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or plan.get("implementation")
        != "crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
        or len(plan.get("repairs", [])) != 5
        or plan.get("proof_change_forbidden") is not True
        or execution
        != {
            "max_driver_builds": 1,
            "max_complete_invocations": 0,
            "max_input_stream_reads": 0,
            "max_target_theorem_submissions": 0,
            "max_target_exports": 0,
            "max_fresh_target_imports": 0,
            "max_retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, exact repair list, proof freeze, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-plan-v11: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-construction-plan-v11: PASS: "
        "repairs=5|builds=0/1|inputs=0|targets=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
