#!/usr/bin/env python3
"""Validate support identities and the exact Fibonacci natAbs composition plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
V8 = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v8.json"
V9 = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v9.json"
DRIVER = ROOT / "crates/axeyum-lean-import/examples/int_fib_natabs_exact.rs"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    result = json.loads(V8.read_text())
    plan = json.loads(V9.read_text())
    names = [row.get("name") for row in result["measured_roots"]]
    if (
        result.get("state") != "exact-support-identities-qualified-no-specialization"
        or names
        != [
            "Axeyum.Autogenesis.intFibNegativeEvenV1",
            "Axeyum.Autogenesis.intFibNegativeOddV1",
            "Int.natAbs_neg",
        ]
        or any(row.get("axiom_footprint") != [] for row in result["measured_roots"])
        or result["execution"].get("importer_runs") != 2
        or result["execution"].get("theorem_submissions") != 0
        or result["authority"].get("ledger_writes") != 0
        or plan.get("state")
        != "preregistered-before-exact-natabs-composition-driver"
        or plan["support_inventory"].get("sha256") != sha256(V8)
        or len(plan.get("inputs", [])) != 5
        or any(sha256(pathlib.Path(row["path"])) != row.get("sha256") for row in plan["inputs"])
        or plan["driver"].get("must_not_exist_before_plan") is not True
        or plan["driver"].get("output_must_not_preexist") is not True
        or plan["target"].get("name") != "Axeyum.Autogenesis.intFibNatAbsV1"
        or len(plan["target"].get("expected_direct_theorem_dependencies", [])) != 7
        or plan["execution"].get("max_complete_invocations") != 1
        or plan["execution"].get("max_input_stream_reads") != 5
        or plan["execution"].get("max_composition_operations") != 4
        or plan["execution"].get("max_support_theorem_submissions") != 1
        or plan["execution"].get("max_target_specializations") != 1
        or plan["execution"].get("max_retries") != 0
        or plan["execution"].get("max_ledger_writes") != 0
        or plan["acceptance"].get("target_axiom_footprint") != []
        or plan["acceptance"].get("proof_terms_types_or_values_rendered") != 0
    ):
        raise ValueError("support inventory or exact composition authority changed")
    if not DRIVER.exists() and plan["driver"].get("must_not_exist_before_plan") is not True:
        raise ValueError("driver absence contract changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-v8-v9: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-v8-v9: PASS: "
        "supports=7|streams=5|compositions=4|support_submissions=1|"
        "target_specializations=1|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
