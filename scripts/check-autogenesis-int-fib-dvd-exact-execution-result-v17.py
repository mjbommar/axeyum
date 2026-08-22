#!/usr/bin/env python3
"""Validate the fail-closed Int.fib_dvd kernel submission result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-exact-execution-result-v17.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    implementation = result["implementation"]
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    output = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson")
    if (
        result.get("state") != "declined-at-kernel-target-type-mismatch"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(ROOT / implementation["path"]) != implementation.get("sha256")
        or diagnostic.get("class") != "TypeMismatch"
        or output.exists()
        or execution.get("input_stream_reads") != 4
        or execution.get("composition_operations") != 3
        or execution.get("target_theorem_submissions") != 1
        or execution.get("accepted_target_theorems") != 0
        or execution.get("target_exports") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise RuntimeError("kernel decline, counters, or absent output changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-exact-execution-result-v17: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-exact-execution-result-v17: PASS: submissions=1|accepted=0|output=absent|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
