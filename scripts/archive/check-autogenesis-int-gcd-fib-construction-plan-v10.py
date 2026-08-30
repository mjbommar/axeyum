#!/usr/bin/env python3
"""Validate exact Int.gcd_fib construction authority."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-plan-v10.json"
DRIVER = ROOT / "crates/axeyum-lean-import/examples/int_gcd_fib_exact.rs"


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = ROOT / plan["predecessor"]["path"]
    premise = ROOT / plan["facts"]["premise"]["path"]
    target = ROOT / plan["facts"]["target"]["path"]
    premise_fact = json.loads(premise.read_text())
    target_fact = json.loads(target.read_text())
    if (
        plan.get("state") != "preregistered-before-exact-int-gcd-fib-driver"
        or sha256(predecessor) != plan["predecessor"].get("sha256")
        or sha256(premise) != plan["facts"]["premise"].get("sha256")
        or sha256(target) != plan["facts"]["target"].get("sha256")
        or premise_fact.get("epistemic_status") != "proved"
        or target_fact.get("epistemic_status") != "open"
        or len(plan.get("inputs", [])) != 2
        or any(sha256(pathlib.Path(row["path"])) != row.get("sha256") for row in plan["inputs"])
        or plan["int_gcd"].get("definition_name") != "Int.gcd"
        or plan["int_gcd"].get("equation_name") != "Int.gcd_def"
        or plan["target"].get("name") != "Int.gcd_fib"
        or len(plan["target"].get("expected_direct_theorem_dependencies", [])) != 6
        or plan["driver"].get("must_not_exist_before_plan") is not True
        or plan["driver"].get("output_must_not_preexist") is not True
        or plan["execution"].get("max_complete_invocations") != 1
        or plan["execution"].get("max_input_stream_reads") != 2
        or plan["execution"].get("max_composition_operations") != 1
        or plan["execution"].get("max_definition_submissions") != 1
        or plan["execution"].get("max_support_theorem_submissions") != 1
        or plan["execution"].get("max_target_theorem_submissions") != 1
        or plan["execution"].get("max_retries") != 0
        or plan["execution"].get("max_ledger_writes") != 0
        or plan["acceptance"].get("target_axiom_footprint") != []
        or plan["acceptance"].get("proof_terms_types_or_values_rendered") != 0
    ):
        raise ValueError("exact Int.gcd_fib construction authority changed")
    if DRIVER.exists() and plan["driver"].get("must_not_exist_before_plan") is not True:
        raise ValueError("driver sequencing contract changed")


def main() -> int:
    try:
        validate()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-plan-v10: FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "autogenesis-int-gcd-fib-construction-plan-v10: PASS: "
        "target=Int.gcd_fib|streams=2|compositions=1|definitions=1|"
        "supports=1|target_submissions=1|fresh_imports=2|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
