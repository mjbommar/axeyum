#!/usr/bin/env python3
"""Validate deterministic export of direct Int divisibility transports."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-witness-transport-export-plan-v9.json"


class PlanError(RuntimeError):
    """The transport export boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    source = plan["source"]
    staging = plan["staging"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-witness-transport-export-plan-v9"
        or plan.get("state") != "preregistered-before-two-root-export-and-audit"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or sha256(ROOT / source["path"]) != source.get("sha256")
        or source.get("roots")
        != [
            "Axeyum.Autogenesis.intNatAbsDvdForwardResidualV1",
            "Axeyum.Autogenesis.intDvdOfNatAbsDvdDirectV1",
        ]
        or staging.get("all_three_paths_must_not_preexist") is not True
        or staging.get("all_three_paths_removed_after_export") is not True
        or plan["output"].get("pack_must_not_preexist") is not True
        or execution
        != {
            "max_staging_source_writes": 1,
            "max_module_compiles": 1,
            "max_exporter_invocations": 2,
            "max_root_stream_writes": 2,
            "max_importer_runs": 2,
            "max_retries": 0,
            "target_fib_dvd_submissions": 0,
            "ledger_writes": 0,
        }
    ):
        raise PlanError("predecessor, source roots, staging contract, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-witness-transport-export-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-witness-transport-export-plan: PASS: "
        "compiles=0/1|exports=0/2|imports=0/2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
