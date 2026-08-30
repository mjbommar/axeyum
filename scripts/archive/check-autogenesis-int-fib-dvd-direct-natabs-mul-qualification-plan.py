#!/usr/bin/env python3
"""Validate hash-only qualification of direct natAbs multiplication."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-direct-natabs-mul-qualification-plan-v6.json"


class PlanError(RuntimeError):
    """The hash-only qualification boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    evidence = plan["fixed_evidence"]
    execution = plan["execution"]
    expected_dependencies = [
        "Eq.symm",
        "_private.AxeyumIntNatAbsMulDirectV1.0.Axeyum.Autogenesis.intNatAbsNegOfNatDirectV1",
    ]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-direct-natabs-mul-qualification-plan-v6"
        or plan.get("state")
        != "preregistered-hash-only-closure-qualification-before-sealing"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or evidence.get("root_sha256") != evidence.get("replay_sha256")
        or evidence.get("axiom_footprint") != []
        or evidence.get("direct_theorem_dependencies") != expected_dependencies
        or plan["qualification"].get("write_manifest_and_seal_fixed_bytes") is not True
        or execution
        != {
            "max_stream_hash_reads": 2,
            "max_audit_report_reads": 0,
            "max_exporter_invocations": 0,
            "max_importer_runs": 0,
            "max_manifest_writes": 1,
            "max_retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, fixed evidence, or no-rerun budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-direct-natabs-mul-qualification-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-direct-natabs-mul-qualification-plan: PASS: "
        "hash_reads=0/2|exports=0|imports=0|manifests=0/1|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
