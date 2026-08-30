#!/usr/bin/env python3
"""Validate the direct Int Dvd hypothesis repair result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-result-v14.json"


class ResultError(RuntimeError):
    """The direct hypothesis repair result changed."""


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    implementation = result["implementation"]
    execution = result["execution"]
    source = (ROOT / implementation["path"]).read_text()
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-mathlib-int-fib-dvd-exact-construction-result-v14"
        or result.get("state") != "direct-int-dvd-hypothesis-builds-clippy-clean"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or "function_domain" in source
        or 'dvd(kernel, int_ty, "Int.instDvd", m, n)' not in source
        or execution
        != {
            "driver_builds": 1,
            "focused_clippy_exit_status": 0,
            "complete_invocations": 0,
            "input_stream_reads": 0,
            "target_theorem_submissions": 0,
            "target_exports": 0,
            "fresh_target_imports": 0,
            "retries": 0,
            "ledger_writes": 0,
        }
    ):
        raise ResultError("implementation, direct hypothesis construction, or zero-execution budget changed")


def main() -> int:
    try:
        validate()
    except (ResultError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-result-v14: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-fib-dvd-exact-construction-result-v14: PASS: "
        "clippy=0|direct_int_dvd=true|inputs=0|targets=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
