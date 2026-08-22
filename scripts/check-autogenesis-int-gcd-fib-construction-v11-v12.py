#!/usr/bin/env python3
"""Validate the open-term diagnostic decline and its closed-term repair."""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v11.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v12.json"
OUTPUT = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1/root.ndjson")


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    try:
        result = json.loads(RESULT.read_text())
        plan = json.loads(PLAN.read_text())
        valid = (
            result.get("state") == "diagnostic-declined-on-open-term-inference-no-target-submission"
            and result["observation"].get("stage") == "p0 diagnostic inference"
            and result["authority"].get("diagnostic_credit") == 0
            and result["execution"].get("target_theorem_submissions") == 0
            and not OUTPUT.exists()
            and plan.get("state") == "preregistered-closed-link-diagnostic-before-code-repair"
            and plan["predecessor"].get("sha256") == sha256(RESULT)
            and plan["repair"].get("proof_chain_changes") == 0
            and plan["execution"].get("max_complete_invocations") == 1
            and plan["execution"].get("max_retries") == 0
            and plan["execution"].get("max_ledger_writes") == 0
        )
        if not valid:
            raise ValueError("closed-link diagnostic authority changed")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v11-v12: FAIL: {error}", file=sys.stderr)
        return 1
    print("autogenesis-int-gcd-fib-construction-v11-v12: PASS: diagnostic_credit=0|repair=close_terms|ledger_writes=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
