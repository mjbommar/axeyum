#!/usr/bin/env python3
"""Generate the proof-free public Euclidean recursion plan."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/euclidean-public-recursion-plan-v1.json"
DECLINE = ROOT / "artifacts/autogenesis/euclidean-public-div-add-mod-lift-decline-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)

DECLINE_SHA256 = "06f9250a3491e27106c447eb06bdd2f0292f454e3499fc2da0308f90463bda0f"
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
NAMES = [
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div_add_mod",
    "Nat.div_eq",
    "Nat.le_of_succ_le_succ",
    "Nat.lt_of_lt_of_le",
    "Nat.mod_eq",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_succ_le_zero",
    "Nat.sub_lt",
    "Nat.succ_sub_succ_eq_sub",
]


class PublicRecursionPlanError(RuntimeError):
    """The recursive route, statement population, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def selected_statements() -> list[dict[str, Any]]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise PublicRecursionPlanError("statement inventory changed or is mutable")
    selected: dict[str, dict[str, Any]] = {}
    with INVENTORY.open() as source:
        for line_number, line in enumerate(source, 1):
            row = json.loads(line)
            name = row.get("name")
            if name not in NAMES:
                continue
            if name in selected:
                raise PublicRecursionPlanError(f"duplicate statement {name} at row {line_number}")
            selected[name] = {
                "name": name,
                "module": row["module"],
                "type": row["type"],
                "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
                "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
                "source_row_sha256": hashlib.sha256(
                    json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
                ).hexdigest(),
            }
    missing = sorted(set(NAMES) - set(selected))
    if missing:
        raise PublicRecursionPlanError(f"missing statements: {', '.join(missing)}")
    if selected["Nat.div_add_mod"]["type"] != "∀ (m n : ℕ), n * (m / n) + m % n = m":
        raise PublicRecursionPlanError("public target statement changed")
    return [selected[name] for name in NAMES]


def build() -> dict[str, Any]:
    if sha256(DECLINE) != DECLINE_SHA256:
        raise PublicRecursionPlanError("transparent-wrapper decline changed")
    statements = selected_statements()
    target = next(row for row in statements if row["name"] == "Nat.div_add_mod")
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-euclidean-public-recursion-plan",
        "state": "preregistered-before-recursive-source-or-kernel-submission",
        "policy_version": "euclidean-public-synchronized-recursion-v1",
        "inputs": {
            "transparent_wrapper_decline": {
                "path": str(DECLINE.relative_to(ROOT)),
                "sha256": DECLINE_SHA256,
                "kernel_theorem_submissions": 0,
            },
            "statement_inventory": {
                "path": str(INVENTORY),
                "sha256": INVENTORY_SHA256,
                "mode": "0444",
            },
            "allowed_statements": statements,
        },
        "target": {
            "source_name": "Nat.div_add_mod",
            "authored_name": "Axeyum.Autogenesis.divAddModPublicRecursion",
            "statement": target["type"],
            "type_sha256": target["type_sha256"],
            "type_repr_sha256": target["type_repr_sha256"],
            "required_type_relation": "exact-lean-expression-representation",
            "required_axiom_footprint": [],
            "fresh_reconstructions": 2,
            "second_run_requires_first_run_acceptance": True,
        },
        "fixed_recursion": {
            "source_path": "scripts/lean/autogenesis_div_add_mod_public_recursion.lean",
            "decreasing_argument": "dividend",
            "synchronized_equations": ["Nat.div_eq", "Nat.mod_eq"],
            "recursive_argument": "dividend - divisor",
            "decrease_evidence": ["Nat.sub_lt", "Nat.lt_of_lt_of_le"],
            "subtraction_restoration": "local primitive-recursive proof using Nat.succ_sub_succ_eq_sub",
            "base_branch": "the false public-equation branch, closed by local n*0=0 and 0+n=n proofs",
            "transparent_wrapper_lift_reuse_allowed": False,
            "official_nat_div_add_mod_proof_allowed": False,
            "private_div_go_invariant_dependency_allowed": False,
            "additional_statement_names_allowed": 0,
            "proof_search_allowed": False,
            "upstream_proof_bodies_allowed": False,
        },
        "gates": {
            "public_equations_must_be_rewritten_together": True,
            "recursive_call_must_use_registered_decrease": True,
            "authored_type_must_match_official_target": True,
            "first_footprint_must_be_empty_before_second_run": True,
            "both_declaration_identities_must_match": True,
            "direct_dependencies_must_be_enumerated": True,
        },
        "budget": {
            "max_revised_source_paths": 1,
            "max_public_support_theorem_declarations": 1,
            "max_kernel_theorem_submissions": 2,
            "max_exact_fibonacci_target_submissions": 0,
            "max_executor_invocations": 0,
            "max_retries_after_kernel_decline": 0,
        },
        "authority": {
            "balanced_bezout_reconstruction_allowed": False,
            "coprime_cancellation_reconstruction_allowed": False,
            "proof_bodies_readable_by_model": False,
            "theorem_values_readable_by_model": False,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "verification": "python3 scripts/gen-autogenesis-euclidean-public-recursion-plan.py --check",
        "limitations": (
            "The plan replaces the failed wrapper route with a public recursive proof. "
            "It does not authorize downstream Bezout, cancellation, or target work."
        ),
    }


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate(value: dict[str, Any]) -> None:
    if value != build():
        raise PublicRecursionPlanError("public recursion plan differs from generated contract")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        value = build()
        expected = render(value)
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != expected:
                raise PublicRecursionPlanError(f"{OUTPUT.relative_to(ROOT)} is stale")
            print(
                "AUTOGENESIS_EUCLIDEAN_PUBLIC_RECURSION_PLAN_OK|statements=12|"
                "submissions=0/2|fibonacci_submissions=0|evaluation=0|ledger_writes=0"
            )
        else:
            OUTPUT.write_text(expected)
            print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        PublicRecursionPlanError,
    ) as error:
        print(f"autogenesis-euclidean-public-recursion-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
