#!/usr/bin/env python3
"""Fail closed over the official-gcd balanced-Bezout exact-reuse plan."""

import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PLAN = Path(os.environ.get("AXEYUM_EXACT_REUSE_PLAN", ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-exact-reuse-plan-v1.json"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main() -> None:
    plan = json.loads(PLAN.read_text())
    predecessor = plan["predecessor"]
    predecessor_path = ROOT / predecessor["path"]
    require(predecessor_path.is_file(), "predecessor is missing")
    require(hashlib.sha256(predecessor_path.read_bytes()).hexdigest() == predecessor["sha256"], "predecessor identity changed")
    require(plan["state"] == "preregistered-exact-Nat-mod-lt-reuse-before-code-or-stream-access", "state changed")
    acceptance = plan["acceptance"]
    require(acceptance["fresh_complete_invocations"] == 2, "need two invocations")
    require(acceptance["outputs_must_be_byte_identical"] is True, "replay equality is not required")
    require(acceptance["all_input_streams_must_be_axiom_free"] is True, "axiom-free inputs are not required")
    require(acceptance["Nat_mod_lt_source_and_target_declaration_sha256_must_match"] is True, "exact Nat.mod_lt identity is not required")
    require(acceptance["Nat_mod_lt_checked_compatibility_must_be_kernel_type_shape"] is True, "checked Nat.mod_lt compatibility is not required")
    require(acceptance["composed_roots"] == ["Axeyum.Autogenesis.modLtSucc", "Axeyum.Autogenesis.nat_gcd_zero_left", "Axeyum.Autogenesis.nat_gcd_succ"], "composition roots changed")
    require(acceptance["composition_operations_per_invocation"] == 3, "composition count changed")
    require(acceptance["specialization_operations_per_invocation"] == 3, "specialization count changed")
    require(acceptance["every_composition_and_specialization_must_replay"] is True, "replay is not required")
    require(acceptance["closed_balanced_bezout_axiom_footprint"] == [], "closed theorem may reach axioms")
    require("Nat.mod_lt" not in acceptance["composed_roots"], "Nat.mod_lt must be reused, not composed")
    budget = plan["budget"]
    require(budget == {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 10, "max_composition_operations": 6, "max_specialization_operations": 6, "max_new_closed_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}, "budget changed")
    require(all(value == 0 for value in plan["authority"].values()), "plan grants authority before execution")
    require(plan["implementation"]["proof_terms_types_or_values_may_be_rendered"] is False, "proof material may be rendered")
    print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_EXACT_REUSE_PLAN_OK|runs=2|reuse=Nat.mod_lt|compositions=6|specializations=6|authority=0")


if __name__ == "__main__":
    main()
