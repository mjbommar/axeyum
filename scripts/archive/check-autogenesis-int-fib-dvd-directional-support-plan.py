#!/usr/bin/env python3
"""Validate the narrowed directional support acquisition for Int.fib_dvd."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-directional-support-plan-v2.json"


class PlanError(RuntimeError):
    """The narrowed support boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    support = plan["support"]
    execution = plan["execution"]
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-directional-support-plan-v2"
        or plan.get("state")
        != "preregistered-after-biconditional-rejection-before-directional-root-export"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or predecessor.get("rejected_axiom_footprint") != ["propext"]
        or support.get("module") != "Init.Data.Int.DivMod.Lemmas"
        or support.get("roots")
        != [
            "Int.dvd_natAbs_self",
            "Int.dvd_trans",
            "Int.natAbs_mul",
            "Int.ofNat_dvd_left",
        ]
        or support.get("forbidden_root") != "Int.natAbs_dvd_natAbs"
        or support.get("target_proof_body_allowed") is not False
        or plan["command"].get("output_must_not_preexist") is not True
        or execution.get("max_exporter_invocations") != 1
        or execution.get("max_root_stream_writes") != 1
        or execution.get("max_importer_runs") != 2
        or execution.get("max_retries") != 0
        or execution.get("target_theorem_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise PlanError("predecessor, roots, output, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-directional-support-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-directional-support-plan: PASS: "
        "roots=4|exporters=0/1|imports=0/2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
