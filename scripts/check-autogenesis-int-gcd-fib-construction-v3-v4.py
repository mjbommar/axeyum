#!/usr/bin/env python3
"""Validate the empty V3 path result and bounded V4 retry."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V3_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v3.json"
V3_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v3.json"
V4_PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v4.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(V3_RESULT.read_text())
    retry = json.loads(V4_PLAN.read_text())
    source = pathlib.Path(retry["input"]["path"])
    if (
        result.get("state") != "no-durable-report-no-diagnostic-credit"
        or result["plan"].get("sha256") != sha256(V3_PLAN)
        or result["execution"]
        != {
            "importer_invocations": 1,
            "proof_bearing_stream_reads": 1,
            "completed_audit_documents": 0,
            "stdout_bytes_observed": 0,
            "retries": 0,
            "theorem_submissions": 0,
            "ledger_writes": 0,
        }
        or result["authority"].get("diagnostic_credit") != 0
        or retry.get("state")
        != "preregistered-before-single-bounded-blocker-path-read"
        or retry["parent_result"].get("sha256") != sha256(V3_RESULT)
        or source.stat().st_size != retry["input"].get("bytes")
        or stat.S_IMODE(source.stat().st_mode) != 0o444
        or sha256(source) != retry["input"].get("sha256")
        or retry["projection"].get("max_carriers_per_blocker") != 5
        or retry["projection"].get("proof_terms_types_or_values_rendered") != 0
        or retry["budget"]
        != {
            "max_importer_runs": 1,
            "max_proof_bearing_stream_reads": 1,
            "max_retries": 0,
            "max_theorem_submissions": 0,
            "max_ledger_writes": 0,
        }
        or retry["authority"].get("definition_bodies_readable_by_model") is not False
        or retry["authority"].get("ledger_writes") != 0
    ):
        raise ValueError("V3 zero-credit result or V4 bounded retry changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v3-v4: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-v3-v4: PASS: "
        "v3_reports=0|v3_credit=0|v4_reads=1|v4_nearest=5|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
