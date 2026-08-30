#!/usr/bin/env python3
"""Validate the exact Int.fib_dvd composition plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-plan-v10.json"


class PlanError(RuntimeError):
    """The exact Int.fib_dvd construction boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    inputs = plan["inputs"]
    target = plan["target"]
    execution = plan["execution"]
    expected_hashes = [
        "1ec10d475fb3c77fea3353036e2a09f70abf88f03402a2912407c71b26e3b7e4",
        "52acbd5a51f2163ab5b712483c582adb916ab198567c2b0b6c3678f7316d86d7",
        "09ebd925b3af67009b1806fd157a25b195e046124065778ec6eaf754f5ecfc04",
        "66faaafc0b7a34267d22427cd968fe3649e31cae3dcf9b87c56ab3db83004bc6",
    ]
    expected_dependencies = [
        "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
        "Axeyum.Autogenesis.intFibNatAbsV1",
        "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
        "Axeyum.Autogenesis.intNatAbsMulDirectV1",
        "Eq.symm",
        "Nat.fib_dvd",
    ]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-construction-plan-v10"
        or plan.get("state")
        != "preregistered-four-capsule-exact-composition-before-driver-code"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or [item.get("sha256") for item in inputs] != expected_hashes
        or target.get("name") != "Int.fib_dvd"
        or target.get("implementation")
        != "crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
        or target.get("expected_direct_theorem_dependencies") != expected_dependencies
        or pathlib.Path(plan["output"]).exists()
        or execution
        != {
            "max_driver_builds": 1,
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
        raise PlanError("predecessor, inputs, target contract, output, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-construction-plan: PASS: "
        "inputs=4|builds=0/1|targets=0/1|imports=0/2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
