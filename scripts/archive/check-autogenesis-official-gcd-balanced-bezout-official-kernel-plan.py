#!/usr/bin/env python3
"""Verify the official-kernel balanced-Bezout composition plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-plan-v1.json"
RESULT_INPUTS = {
    "zero_left": (ROOT / "artifacts/autogenesis/official-gcd-zero-left-root-export-result-v1.json", "a6bed60ca9d85ca49313a3db1968ee1d50917f201449cfb6e523be74216f8af1"),
    "successor": (ROOT / "artifacts/autogenesis/official-gcd-succ-root-export-result-v1.json", "d4b2491e58cae2cfedc8f86e674ecf3d62d4b644f5ed3bb8950d7f64f46c5e6e"),
    "generic_balanced_bezout": (ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-clean-result-v1.json", "dd483ff460fb1ae7ef8038ef6eb214cd931d6a60bbb83e8330bd9c90a3b1290d"),
}
INPUTS = {
    "target_base": {"path": "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson", "sha256": "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd", "role": "official Mathlib representation and Nat.mod_lt"},
    "mod_lt_adapter": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/f94489c74-lean430-nat-gcd-succ-bridge-v1/nat-gcd-bridge.ndjson", "sha256": "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db", "root": "Axeyum.Autogenesis.modLtSucc"},
    "zero_left": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/0a73f8458-official-gcd-zero-left-root-v1/official-gcd-zero-left-root.ndjson", "sha256": "824399899916c72329f201c0ea8c1b0fe25315ea013c4f392586668f67f606a0", "root": "Axeyum.Autogenesis.nat_gcd_zero_left", "result_sha256": "a6bed60ca9d85ca49313a3db1968ee1d50917f201449cfb6e523be74216f8af1"},
    "successor": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/dfcff00d1-official-gcd-succ-root-v1/official-gcd-succ-root.ndjson", "sha256": "2af40b2c7d89a0959bbe3018da60841ea1dc933ae2f40112ae84d95feab6044c", "root": "Axeyum.Autogenesis.nat_gcd_succ", "result_sha256": "d4b2491e58cae2cfedc8f86e674ecf3d62d4b644f5ed3bb8950d7f64f46c5e6e"},
    "generic_balanced_bezout": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/13038b3ff-official-gcd-balanced-bezout-clean-v1/official-gcd-balanced-bezout-clean.ndjson", "sha256": "c106a1e03a329535042f17f6a9d3cf408361e4b4691b5ea6bac4d1a71186bb56", "root": "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1", "result_sha256": "dd483ff460fb1ae7ef8038ef6eb214cd931d6a60bbb83e8330bd9c90a3b1290d"},
}


class OfficialGcdBalancedBezoutOfficialKernelPlanError(RuntimeError):
    """The input, method, budget, acceptance, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-official-kernel-plan", "preregistered-official-kernel-leaf-composition-no-closed-credit"):
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("plan identity changed")
    for _, (path, digest) in RESULT_INPUTS.items():
        if sha256(path) != digest:
            raise OfficialGcdBalancedBezoutOfficialKernelPlanError("accepted result identity changed")
    if plan.get("inputs") != INPUTS:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("input contract changed")
    implementation = plan.get("implementation", {})
    if implementation.get("path") != "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs" or implementation.get("proof_terms_types_or_values_may_be_rendered") is not False or len(implementation.get("method", [])) != 6:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("implementation boundary changed")
    acceptance = {"fresh_complete_invocations": 2, "outputs_must_be_byte_identical": True, "all_input_streams_must_be_axiom_free": True, "every_composition_and_specialization_must_replay": True, "fresh_mod_bound_axiom_footprint": [], "fresh_closed_successor_axiom_footprint": [], "closed_balanced_bezout_axiom_footprint": [], "required_closed_direct_dependencies": ["Axeyum.Autogenesis.nat_gcd_zero_left", "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1", "Axeyum.Autogenesis.officialNatGcdSuccClosedV1"], "forbidden_dependencies": ["Nat.gcd_zero_left", "Nat.gcd_succ", "WellFounded.Nat.fix_eq", "funext", "propext"], "argument_declaration_identities_must_match_accepted_results": True}
    if plan.get("acceptance") != acceptance:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("acceptance contract changed")
    budget = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 10, "max_composition_operations": 8, "max_specialization_operations": 6, "max_new_closed_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("budget changed")
    if plan.get("execution") != {"evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/9ec4bcfa1-official-gcd-balanced-bezout-official-kernel-v1", "retain_exact_executed_rust_source": True}:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("execution boundary changed")
    authority = {"inherited_official_gcd_zero_left_credit": 1, "inherited_official_gcd_succ_credit": 1, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if plan.get("authority") != authority:
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("authority changed")
    if plan.get("output") != "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-official-kernel-plan.py":
        raise OfficialGcdBalancedBezoutOfficialKernelPlanError("result or verification path changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_OFFICIAL_KERNEL_PLAN_OK|inputs=5|invocations=2|specializations=6|closed_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutOfficialKernelPlanError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-official-kernel-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
