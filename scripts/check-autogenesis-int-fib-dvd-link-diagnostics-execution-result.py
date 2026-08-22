#!/usr/bin/env python3
"""Validate localization of the Eq.rec motive arity defect."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-link-diagnostics-execution-result-v19.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    diagnostic = result["diagnostic"]
    execution = result["execution"]
    implementation = ROOT / "crates/axeyum-lean-import/examples/int_fib_dvd_exact.rs"
    if (
        result.get("state") != "first-two-links-pass-third-eq-rec-motive-arity-fails"
        or sha256(ROOT / result["plan"]["path"]) != result["plan"].get("sha256")
        or sha256(implementation) != result.get("implementation_sha256")
        or diagnostic.get("passed_links") != ["forward witness proof", "natural Fibonacci divisibility"]
        or diagnostic.get("first_failed_link") != "second equality transport"
        or pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-dvd-exact-v1/root.ndjson").exists()
        or execution.get("link_checks_attempted") != 3
        or execution.get("link_checks_passed") != 2
        or execution.get("target_theorem_submissions") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise RuntimeError("localized link failure, implementation, counters, or output changed")


def main() -> int:
    try:
        validate()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-link-diagnostics-execution-result: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-fib-dvd-link-diagnostics-execution-result: PASS: passed=2|failed=link3|targets=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
