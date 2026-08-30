#!/usr/bin/env python3
"""Validate the localized free-variable Int.fib_dvd decline."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-result-v13.json"


class ResultError(RuntimeError):
    """The localized execution decline changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    implementation = result["implementation"]
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    output = pathlib.Path(
        "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson"
    )
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-execution-result-v13"
        or result.get("state")
        != "declined-after-compositions-at-free-variable-hypothesis-inference"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or diagnostic.get("class") != "UnboundFVar"
        or diagnostic.get("output_remains_absent") is not True
        or output.exists()
        or execution
        != {
            "driver_builds": 1,
            "complete_invocations": 1,
            "input_stream_reads": 4,
            "composition_operations": 3,
            "composition_replays": 3,
            "target_theorem_submissions": 0,
            "target_exports": 0,
            "fresh_target_imports": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("implementation, localized stage, counters, or absent output changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-execution-result-v13: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-execution-result-v13: PASS: "
        "inputs=4|compositions=3|targets=0|output=absent|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
