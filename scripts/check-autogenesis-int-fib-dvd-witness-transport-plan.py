#!/usr/bin/env python3
"""Validate the direct Int/Nat divisibility witness transport plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-plan-v7.json"


class PlanError(RuntimeError):
    """The witness transport boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    source = plan["source"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-plan-v7"
        or plan.get("state")
        != "preregistered-two-direction-existential-transport-before-source"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or source.get("path")
        != "artifacts/autogenesis/sources/int-dvd-natabs-witness-transport-v1.lean"
        or source["forward"].get("name")
        != "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1"
        or source["reverse"].get("name")
        != "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1"
        or plan.get("forbidden_dependencies")
        != [
            "Int.natAbs_dvd_natAbs",
            "Int.dvd_natAbs_self",
            "Int.dvd_trans",
            "Int.ofNat_dvd_left",
            "Int.natAbs_mul",
            "propext",
        ]
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
        raise PlanError("predecessor, theorem boundary, forbidden set, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-plan: PASS: "
        "source_writes=0/1|compiles=0/1|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
