#!/usr/bin/env python3
"""Validate the blocker-auditor repair boundary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/int-gcd-fib-blocker-auditor-repair-plan-v1.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v4.json"
TOOL = ROOT / "crates/axeyum-lean-import/examples/declaration_blocker_path_batch_audit.rs"
RESULT_ARTIFACT = ROOT / "artifacts/autogenesis/int-gcd-fib-blocker-auditor-repair-result-v1.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    parent = json.loads(RESULT.read_text())
    if (
        parent.get("state")
        != "computation-completed-without-durable-report-no-diagnostic-credit"
        or parent["execution"].get("completed_audit_documents") != 0
        or parent["authority"].get("diagnostic_credit") != 0
        or plan.get("state") != "preregistered-before-tool-edit-no-proof-stream-read"
        or plan["parent_result"].get("sha256") != sha256(RESULT)
        or plan["tool"].get("before_sha256")
        != "cdf582bc9226aa2dd31bcfa172042f14ba6af582f99eb93ee61ca39904852d6a"
        or plan.get("authorized_changes")
        != [
            "memoize each candidate declaration closure once across all blockers",
            "accept an optional explicit output path and write the complete JSON report there",
            "retain stdout behavior when no output path is supplied",
            "fail before overwrite when the explicit output already exists",
        ]
        or len(plan.get("required_controls", [])) != 4
        or plan.get("budget")
        != {
            "proof_bearing_stream_reads": 0,
            "theorem_submissions": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0,
        }
    ):
        raise ValueError("repair lineage, scope, controls, or authority changed")
    if RESULT_ARTIFACT.exists():
        result = json.loads(RESULT_ARTIFACT.read_text())
        if (
            result.get("state")
            != "memoized-durable-output-interface-implemented-and-focused-green"
            or result["plan"].get("sha256") != sha256(PLAN)
            or result["tool"].get("before_sha256") != plan["tool"].get("before_sha256")
            or result["tool"].get("after_sha256") != sha256(TOOL)
            or result["validation"].get("focused_tests") != 3
            or result["validation"].get("focused_test_failures") != 0
            or result["validation"].get("proof_bearing_stream_reads") != 0
            or result["authority"].get("ledger_writes") != 0
        ):
            raise ValueError("implemented repair evidence changed")
    elif sha256(TOOL) != plan["tool"].get("before_sha256"):
        raise ValueError("tool changed before a repair result was recorded")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-blocker-auditor-repair-plan: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-blocker-auditor-repair-plan: PASS: "
        "memoize=1|durable_output=1|controls=4|stream_reads=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
