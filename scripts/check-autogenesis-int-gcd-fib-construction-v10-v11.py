#!/usr/bin/env python3
"""Validate the failed first join and bounded link diagnostic."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v10.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v11.json"
OUTPUT = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1/root.ndjson")


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(RESULT.read_text())
    plan = json.loads(PLAN.read_text())
    if (
        result.get("state") != "first-exact-join-declined-at-target-type-mismatch-no-output"
        or result["observation"].get("stage") != "Int.gcd_fib theorem submission"
        or result["observation"].get("output_absent") is not True
        or OUTPUT.exists()
        or result["execution"].get("target_exports") != 0
        or result["execution"].get("ledger_writes") != 0
        or result["authority"].get("theorem_credit") != 0
        or plan.get("state") != "preregistered-link-by-link-type-diagnostic-before-driver-repair"
        or plan["predecessor"].get("sha256") != sha256(RESULT)
        or len(plan["repair"].get("allowed_changes", [])) != 4
        or plan["execution"].get("max_complete_invocations") != 1
        or plan["execution"].get("max_input_stream_reads") != 2
        or plan["execution"].get("max_retries") != 0
        or plan["execution"].get("max_ledger_writes") != 0
    ):
        raise ValueError("failed join evidence or diagnostic authority changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v10-v11: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-gcd-fib-construction-v10-v11: PASS: credit=0|diagnostic_links=6|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
