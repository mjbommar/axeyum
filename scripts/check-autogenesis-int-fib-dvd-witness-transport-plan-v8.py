#!/usr/bin/env python3
"""Validate the two-branch Int witness sign repair plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-plan-v8.json"


class PlanError(RuntimeError):
    """The opposite-sign repair boundary changed."""


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
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-plan-v8"
        or plan.get("state")
        != "preregistered-two-opposite-sign-witness-repair-before-source-change"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or correction.get("preserve")
        != [
            "the complete forward theorem",
            "the ofNat.ofNat reverse branch",
            "the negSucc.negSucc reverse branch",
        ]
        or correction.get("new_theorem_dependencies") != []
        or execution
        != {
            "max_source_rewrites": 1,
            "max_compile_invocations": 1,
            "max_exporter_invocations": 0,
            "max_importer_runs": 0,
            "max_retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, preserved branches, correction, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-plan-v8: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-plan-v8: PASS: "
        "rewrites=0/1|compiles=0/1|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
