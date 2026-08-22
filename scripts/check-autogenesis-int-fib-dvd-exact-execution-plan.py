#!/usr/bin/env python3
"""Validate the one-run exact Int.fib_dvd execution plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-plan-v12.json"


class PlanError(RuntimeError):
    """The exact execution boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    implementation = plan["implementation"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-execution-plan-v12"
        or plan.get("state")
        != "preregistered-one-complete-execution-before-capsule-read"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or len(plan.get("inputs", [])) != 4
        or pathlib.Path(plan["output"]).exists()
        or execution
        != {
            "max_driver_builds": 0,
            "max_complete_invocations": 1,
            "max_input_stream_reads": 4,
            "max_composition_operations": 3,
            "max_composition_replays": 3,
            "max_target_theorem_submissions": 1,
            "max_target_exports": 1,
            "max_fresh_target_imports": 2,
            "max_retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, implementation, inputs, output, or execution budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-execution-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-execution-plan: PASS: "
        "runs=0/1|inputs=0/4|targets=0/1|imports=0/2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
