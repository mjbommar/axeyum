#!/usr/bin/env python3
"""Validate one binder-closed Int.fib_dvd diagnostic run."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-link-diagnostics-execution-plan-v19.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    implementation = ROOT / "crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
    execution = plan["execution"]
    if (
        plan.get("state") != "preregistered-one-five-link-diagnostic-run"
        or sha256(ROOT / predecessor["path"]) != predecessor.get("sha256")
        or sha256(implementation) != plan.get("implementation_sha256")
        or pathlib.Path(plan["output"]).exists()
        or execution.get("max_complete_invocations") != 1
        or execution.get("max_input_stream_reads") != 4
        or execution.get("max_link_checks") != 5
        or execution.get("max_target_theorem_submissions") != 1
        or execution.get("max_retries") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise RuntimeError("predecessor, instrumented driver, output, or budget changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-link-diagnostics-execution-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-link-diagnostics-execution-plan: PASS: runs=0/1|links=0/5|targets=0/1")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
