#!/usr/bin/env python3
"""Validate the pre-execution Int.fib_dvd driver decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-result-v10.json"


class ResultError(RuntimeError):
    """The driver decline evidence changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    implementation = result["implementation"]
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-construction-result-v10"
        or result.get("state") != "declined-at-driver-typecheck-before-proof-stream-read"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or diagnostic.get("stage") != "cargo-clippy-driver-build"
        or diagnostic.get("exit_status") != 101
        or len(diagnostic.get("errors", [])) != 5
        or execution
        != {
            "driver_builds": 1,
            "complete_invocations": 0,
            "input_stream_reads": 0,
            "composition_operations": 0,
            "target_theorem_submissions": 0,
            "target_exports": 0,
            "fresh_target_imports": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("implementation identity, build diagnostics, or zero-execution budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-construction-result: PASS: "
        "builds=1|inputs=0|targets=0|exports=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
