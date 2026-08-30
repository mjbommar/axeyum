#!/usr/bin/env python3
"""Validate the dependent Eq.rec motive repair."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-eq-rec-motive-plan-v20.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    correction = plan["correction"]
    execution = plan["execution"]
    if (
        plan.get("state") != "preregistered-dependent-eq-rec-motive-before-code-change"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or correction.get("new_motive") != "fun b (_ : left = b) => P b"
        or correction.get("apply_to") != ["second equality transport", "first equality transport"]
        or correction.get("expected_new_theorem_dependencies") != []
        or execution.get("max_driver_builds") != 1
        or execution.get("max_complete_invocations") != 0
        or execution.get("max_input_stream_reads") != 0
        or execution.get("max_target_theorem_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise RuntimeError("predecessor, dependent motive correction, or zero-execution budget changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-eq-rec-motive-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-eq-rec-motive-plan: PASS: motives=2|builds=0/1|inputs=0|targets=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
