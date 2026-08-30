#!/usr/bin/env python3
"""Validate the direct Int Dvd hypothesis construction repair."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-plan-v14.json"


class PlanError(RuntimeError):
    """The direct hypothesis repair changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    correction = plan["correction"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-construction-plan-v14"
        or plan.get("state")
        != "preregistered-direct-int-dvd-hypothesis-before-code-change"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or correction.get("implementation")
        != "crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
        or correction.get("proof_chain_change") != "none after introduction of h"
        or correction.get("expected_new_theorem_dependencies") != []
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
        raise PlanError("predecessor, exact correction, or zero-execution budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-plan-v14: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-construction-plan-v14: PASS: "
        "builds=0/1|inputs=0|targets=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
