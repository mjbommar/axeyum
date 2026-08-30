#!/usr/bin/env python3
"""Validate binder-closed Int.fib_dvd link diagnostics."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-link-diagnostics-plan-v18.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    execution = plan["execution"]
    if (
        plan.get("state") != "preregistered-five-closed-link-checks-before-instrumentation"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or len(plan.get("checks", [])) != 5
        or plan.get("proof_change_forbidden") is not True
        or execution
        != {
            "max_driver_builds": 1,
            "max_complete_invocations": 0,
            "max_input_stream_reads": 0,
            "max_target_theorem_submissions": 0,
            "max_retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise RuntimeError("predecessor, five-link diagnostic boundary, or budget changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-link-diagnostics-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-link-diagnostics-plan: PASS: links=5|builds=0/1|inputs=0|targets=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
