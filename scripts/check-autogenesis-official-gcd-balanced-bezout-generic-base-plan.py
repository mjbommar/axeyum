#!/usr/bin/env python3
"""Verify the reverse-direction generic-kernel-base composition plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-generic-base-plan-v1.json"
PREDECESSOR = ROOT / "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-result-v1.json"
PREDECESSOR_SHA256 = "11a51a0e0f65668146683b2d837eaf3637262189f18a5df0ffd64730672652a9"
INPUTS = {
    "generic_base": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/13038b3ff-official-gcd-balanced-bezout-clean-v1/official-gcd-balanced-bezout-clean.ndjson", "sha256": "c106a1e03a329535042f17f6a9d3cf408361e4b4691b5ea6bac4d1a71186bb56", "root": "Axeyum.Autogenesis.officialGcdBalancedBezoutCleanV1"},
    "mod_lt_source": {"path": "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r082.ndjson", "sha256": "6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd", "root": "Nat.mod_lt"},
    "mod_lt_adapter": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/f94489c74-lean430-nat-gcd-succ-bridge-v1/nat-gcd-bridge.ndjson", "sha256": "6e99d4ae83b3916f8ee36c541bac18fc91b9f922252ca0af1cf658578b4e20db", "root": "Axeyum.Autogenesis.modLtSucc"},
    "zero_left": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/0a73f8458-official-gcd-zero-left-root-v1/official-gcd-zero-left-root.ndjson", "sha256": "824399899916c72329f201c0ea8c1b0fe25315ea013c4f392586668f67f606a0", "root": "Axeyum.Autogenesis.nat_gcd_zero_left", "declaration_sha256": "e4f6c7e3971f5751bd1e889e9bfc28b7035d9f47204f7aafa5efc06b97cf3555"},
    "successor": {"path": "/nas3/data/axeyum/autogenesis/reference-packs/dfcff00d1-official-gcd-succ-root-v1/official-gcd-succ-root.ndjson", "sha256": "2af40b2c7d89a0959bbe3018da60841ea1dc933ae2f40112ae84d95feab6044c", "root": "Axeyum.Autogenesis.nat_gcd_succ", "declaration_sha256": "1a9cf6e4ef4dc54a298214571515e7682a6265d9db7008b7cf1f8b3c38d11f16"},
}


class OfficialGcdBalancedBezoutGenericBasePlanError(RuntimeError):
    """The predecessor, direction, inputs, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise OfficialGcdBalancedBezoutGenericBasePlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state")) != (1, "axeyum-autogenesis-official-gcd-balanced-bezout-generic-base-plan", "preregistered-reverse-composition-generic-kernel-base-no-closed-credit"):
        raise OfficialGcdBalancedBezoutGenericBasePlanError("plan identity changed")
    predecessor = {"path": "artifacts/autogenesis/official-gcd-balanced-bezout-official-kernel-result-v1.json", "sha256": PREDECESSOR_SHA256, "failure": "UnsupportedMissingDeclaration Acc recursive-inductive"}
    if sha256(PREDECESSOR) != PREDECESSOR_SHA256 or plan.get("predecessor") != predecessor:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("predecessor changed")
    if plan.get("inputs") != INPUTS:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("inputs changed")
    implementation = plan.get("implementation", {})
    if implementation != {"path": "crates/axeyum-lean-import/examples/official_gcd_balanced_bezout_composition.rs", "required_change": "use the imported generic-balanced-Bezout kernel as the target base; compose Nat.mod_lt, modLtSucc, zero-left, and successor into it; do not compose the generic theorem", "proof_terms_types_or_values_may_be_rendered": False}:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("implementation boundary changed")
    acceptance = plan.get("acceptance", {})
    if acceptance.get("fresh_complete_invocations") != 2 or acceptance.get("composition_base") != "generic-balanced-bezout-kernel" or acceptance.get("composed_roots") != ["Nat.mod_lt", "Axeyum.Autogenesis.modLtSucc", "Axeyum.Autogenesis.nat_gcd_zero_left", "Axeyum.Autogenesis.nat_gcd_succ"] or acceptance.get("generic_composition_operations") != 0 or acceptance.get("closed_balanced_bezout_axiom_footprint") != [] or acceptance.get("forbidden_dependencies") != ["Nat.gcd_zero_left", "Nat.gcd_succ", "WellFounded.Nat.fix_eq", "funext", "propext"]:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("acceptance contract changed")
    budget = {"max_binary_builds": 1, "max_complete_invocations": 2, "max_input_stream_reads": 10, "max_composition_operations": 8, "max_specialization_operations": 6, "max_new_closed_theorem_submissions": 2, "max_retries": 0, "max_exact_fibonacci_target_submissions": 0, "max_executor_invocations": 0}
    if plan.get("budget") != budget:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("budget changed")
    if plan.get("execution") != {"evidence_pack": "/nas3/data/axeyum/autogenesis/reference-packs/47343f64f-official-gcd-balanced-bezout-generic-base-v1", "retain_exact_executed_rust_source": True}:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("execution boundary changed")
    authority = {"inherited_official_gcd_zero_left_credit": 1, "inherited_official_gcd_succ_credit": 1, "closed_gcd_balanced_bezout_credit": 0, "cancellation_credit": 0, "target_specialization_credit": 0, "exact_fibonacci_target_submissions": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}
    if plan.get("authority") != authority:
        raise OfficialGcdBalancedBezoutGenericBasePlanError("authority changed")
    if plan.get("output") != "artifacts/autogenesis/official-gcd-balanced-bezout-generic-base-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-official-gcd-balanced-bezout-generic-base-plan.py":
        raise OfficialGcdBalancedBezoutGenericBasePlanError("result or verification path changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_GCD_BALANCED_BEZOUT_GENERIC_BASE_PLAN_OK|inputs=5|compositions=8|specializations=6|closed_credit=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, OfficialGcdBalancedBezoutGenericBasePlanError) as error:
        print(f"autogenesis-official-gcd-balanced-bezout-generic-base-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
