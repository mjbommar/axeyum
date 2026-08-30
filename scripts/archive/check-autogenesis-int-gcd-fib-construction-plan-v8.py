#!/usr/bin/env python3
"""Validate the two-read exact support inventory for Fibonacci natAbs."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v8.json"
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v7.json"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    if (
        plan.get("state") != "preregistered-before-two-support-identity-reads"
        or plan["residual_result"].get("sha256") != sha256(RESULT)
        or [item.get("name") for item in plan["already_bound_supports"]]
        != ["Int.fib_natCast", "Axeyum.IntFib.modCases"]
        or len(plan.get("reads", [])) != 2
        or [root for item in plan["reads"] for root in item.get("roots", [])]
        != [
            "Axeyum.Autogenesis.intFibNegativeEvenV1",
            "Axeyum.Autogenesis.intFibNegativeOddV1",
            "Int.natAbs_neg",
        ]
        or any(
            sha256(pathlib.Path(item["path"])) != item.get("sha256")
            or pathlib.Path(item["path"]).stat().st_size != item.get("bytes")
            for item in plan["reads"]
        )
        or plan["constructed_support"].get("method")
        != "Eq.refl after kernel conversion"
        or plan["constructed_support"].get("submissions_authorized_in_this_increment") != 0
        or plan["execution"]
        != {
            "tool": "theorem_footprint_batch_audit",
            "max_importer_runs": 2,
            "max_proof_bearing_stream_reads": 2,
            "max_retries": 0,
            "max_theorem_submissions": 0,
            "max_ledger_writes": 0,
        }
        or plan["acceptance"].get("all_three_measured_roots_axiom_footprint") != []
        or any(plan["acceptance"].get(key) != 0 for key in (
            "rendered_proof_terms", "rendered_theorem_types", "rendered_theorem_values"
        ))
    ):
        raise ValueError("support inventory identity, budget, or authority changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan-v8: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan-v8: PASS: "
        "bound=2|measured=3|reads=2|submissions=0|rendered=0|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
