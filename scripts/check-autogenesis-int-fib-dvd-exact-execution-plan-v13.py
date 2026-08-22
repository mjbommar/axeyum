#!/usr/bin/env python3
"""Validate the cargo-run exact Int.fib_dvd execution plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-plan-v13.json"


class PlanError(RuntimeError):
    """The cargo-run execution boundary changed."""


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
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-execution-plan-v13"
        or plan.get("state") != "preregistered-one-cargo-run-build-and-execution"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or implementation.get("change_from_v12") != "none"
        or pathlib.Path(plan["output"]).exists()
        or execution.get("max_driver_builds") != 1
        or execution.get("max_complete_invocations") != 1
        or execution.get("max_input_stream_reads") != 4
        or execution.get("max_target_theorem_submissions") != 1
        or execution.get("max_fresh_target_imports") != 2
        or execution.get("max_retries") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise PlanError("predecessor, unchanged driver, output, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-execution-plan-v13: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-execution-plan-v13: PASS: "
        "builds=0/1|runs=0/1|inputs=0/4|targets=0/1|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
