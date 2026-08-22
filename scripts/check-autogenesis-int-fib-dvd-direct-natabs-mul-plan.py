#!/usr/bin/env python3
"""Validate the direct natAbs multiplication construction boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-direct-natabs-mul-plan-v3.json"


class PlanError(RuntimeError):
    """The direct constructor boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    target = plan["target"]
    execution = plan["execution"]
    expected_forbidden = [
        "Int.natAbs_mul",
        "Int.natAbs_dvd_natAbs",
        "Int.dvd_natAbs_self",
        "Int.dvd_trans",
        "Int.ofNat_dvd_left",
        "propext",
    ]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-direct-natabs-mul-plan-v3"
        or plan.get("state")
        != "preregistered-direct-constructor-proof-before-source-or-compile"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or predecessor.get("rejected_roots") != 4
        or target.get("name") != "Axeyum.Autogenesis.intNatAbsMulDirectV1"
        or target.get("source")
        != "artifacts/autogenesis/sources/int-natabs-mul-direct-v1.lean"
        or target.get("forbidden_dependencies") != expected_forbidden
        or execution
        != {
            "max_source_writes": 1,
            "max_compile_invocations": 1,
            "max_exporter_invocations": 0,
            "max_importer_runs": 0,
            "max_retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, source, forbidden set, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-direct-natabs-mul-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-direct-natabs-mul-plan: PASS: "
        "source_writes=0/1|compiles=0/1|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
