#!/usr/bin/env python3
"""Validate the pre-launch exact Int.fib_dvd execution decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-result-v12.json"


class ResultError(RuntimeError):
    """The pre-launch decline changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-execution-result-v12"
        or result.get("state")
        != "declined-before-driver-launch-at-absent-example-executable"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or diagnostic.get("exit_status") != 127
        or diagnostic.get("output_remains_absent") is not True
        or pathlib.Path(
            "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson"
        ).exists()
        or execution
        != {
            "driver_process_launches": 0,
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
        raise ResultError("pre-launch status, absent output, or zero-execution counters changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-execution-result: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-execution-result: PASS: "
        "launches=0|inputs=0|targets=0|output=absent|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
