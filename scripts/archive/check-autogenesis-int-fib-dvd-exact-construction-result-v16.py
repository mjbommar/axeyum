#!/usr/bin/env python3
"""Validate direct construction of the Int.fib_dvd result type."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-construction-result-v16.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    implementation = result["implementation"]
    execution = result["execution"]
    source = (ROOT / implementation["path"]).read_text()
    if (
        result.get("state") != "direct-target-proposition-builds-clippy-clean"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or "completed target proof inference failed" in source
        or 'dvd(kernel, int_ty, "Int.instDvd", fib_m, fib_n)' not in source
        or execution.get("focused_clippy_exit_status") != 0
        or execution.get("complete_invocations") != 0
        or execution.get("input_stream_reads") != 0
        or execution.get("target_theorem_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise RuntimeError("implementation, direct result type, or zero-execution budget changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-construction-result-v16: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-exact-construction-result-v16: PASS: clippy=0|direct_result=true|inputs=0|targets=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
