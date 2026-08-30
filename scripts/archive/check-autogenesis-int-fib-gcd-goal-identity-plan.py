#!/usr/bin/env python3
"""Validate the hash-only Int.fib_gcd identity-audit authority."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-goal-identity-plan-v1.json"


class PlanError(RuntimeError):
    """The goal-identity authority changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    fact_path = ROOT / plan["fact"]["path"]
    fact = json.loads(fact_path.read_text())
    source = pathlib.Path(plan["input"]["path"])
    tool = ROOT / plan["tool"]["path"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind") != "axeyum-autogenesis-int-fib-gcd-goal-identity-plan"
        or plan.get("state") != "preregistered-before-single-nonrendering-capsule-read"
        or sha256(ROOT / plan["predecessor"]["path"])
        != plan["predecessor"].get("sha256")
        or sha256(fact_path) != plan["fact"].get("sha256")
        or fact.get("id") != "F:ml430-int-fib-gcd-3a8bfdec"
        or fact.get("epistemic_status") != "open"
        or source.stat().st_size != plan["input"].get("bytes")
        or stat.S_IMODE(source.stat().st_mode) != 0o444
        or stat.S_IMODE(source.parent.stat().st_mode) != 0o555
        or sha256(source) != plan["input"].get("sha256")
        or sha256(tool) != plan["tool"].get("sha256")
        or plan["acceptance"]
        != {
            "name": "Int.fib_gcd",
            "declaration_sha256": "d269d9ef0763dd923c7825c77c0a3a3dd05ebbe4fbad4d84f3ce93482386a0bf",
            "axiom_footprint": [],
            "direct_theorem_dependency_count": 4,
        }
        or plan["execution"]
        != {
            "max_importer_runs": 1,
            "max_stream_reads": 1,
            "max_retries": 0,
            "rendered_proof_terms": 0,
            "rendered_theorem_types": 0,
            "rendered_theorem_values": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("goal identity authority changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-gcd-goal-identity-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-gcd-goal-identity-plan: PASS: "
        "reads=0/1|rendered=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
