#!/usr/bin/env python3
"""Validate the bounded core support export for Int.fib_dvd."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-support-export-plan-v1.json"


class PlanError(RuntimeError):
    """The support acquisition boundary changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    target = plan["target"]
    environment = plan["fixed_environment"]
    support = plan["support"]
    execution = plan["execution"]
    fact_path = ROOT / target["fact_path"]
    fact = json.loads(fact_path.read_text())
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-support-export-plan-v1"
        or plan.get("state")
        != "preregistered-before-official-root-export-or-proof-stream-read"
        or target.get("fact_id") != "F:ml430-int-fib-dvd-ffb3c5c1"
        or fact.get("epistemic_status") != "open"
        or sha256(fact_path) != target.get("fact_sha256")
        or environment.get("hostname") != "server5"
        or environment.get("mathlib_commit")
        != "c5ea00351c28e24afc9f0f84379aa41082b1188f"
        or environment.get("lean_version") != "4.30.0"
        or environment.get("lean4export_binary_sha256")
        != "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
        or support.get("module") != "Init.Data.Int.DivMod.Bootstrap"
        or support.get("root") != "Int.natAbs_dvd_natAbs"
        or support.get("target_proof_body_allowed") is not False
        or plan["command"].get("output_must_not_preexist") is not True
        or execution.get("max_exporter_invocations") != 1
        or execution.get("max_root_stream_writes") != 1
        or execution.get("max_importer_runs") != 2
        or execution.get("max_retries") != 0
        or execution.get("rendered_proof_terms") != 0
        or execution.get("rendered_theorem_types") != 0
        or execution.get("rendered_theorem_values") != 0
        or execution.get("target_theorem_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise PlanError("support identity, environment, output, or budget changed")


def main() -> int:
    try:
        validate()
    except (PlanError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-support-export-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-support-export-plan: PASS: "
        "exporters=0/1|imports=0/2|rendered=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
