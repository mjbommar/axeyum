#!/usr/bin/env python3
"""Generate the proof-free public Euclidean wrapper-lift plan."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-public-div-add-mod-lift-plan-v1.json"
)
PRIVATE_RESULT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-joint-div-mod-local-subtraction-replacement-result-v1.json"
)
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)

PRIVATE_RESULT_SHA256 = "3c181eb4c14a37cdb0046c915e3bf04e96f7c6f48f2688448a7a61a871c2dfb1"
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
NAMES = [
    "Nat.div_add_mod",
    "Nat.div_zero",
    "Nat.lt_succ_self",
    "Nat.modCore_eq_mod",
    "Nat.mod_zero",
    "Nat.zero_add",
    "Nat.zero_lt_succ",
    "Nat.zero_mul",
]


class PublicLiftPlanError(RuntimeError):
    """The public target, statement set, lift route, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_row(row: dict[str, Any]) -> str:
    return json.dumps(row, sort_keys=True, separators=(",", ":"))


def selected_statements() -> list[dict[str, Any]]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise PublicLiftPlanError("statement inventory changed or is mutable")
    selected: dict[str, dict[str, Any]] = {}
    with INVENTORY.open() as source:
        for line_number, line in enumerate(source, 1):
            row = json.loads(line)
            name = row.get("name")
            if name not in NAMES:
                continue
            if name in selected:
                raise PublicLiftPlanError(f"duplicate statement {name} at row {line_number}")
            if not all(isinstance(row.get(key), str) for key in ["module", "type", "type_repr"]):
                raise PublicLiftPlanError(f"incomplete statement {name}")
            selected[name] = {
                "name": name,
                "module": row["module"],
                "type": row["type"],
                "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
                "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
                "source_row_sha256": hashlib.sha256(canonical_row(row).encode()).hexdigest(),
            }
    missing = sorted(set(NAMES) - set(selected))
    if missing:
        raise PublicLiftPlanError(f"missing statements: {', '.join(missing)}")
    target = selected["Nat.div_add_mod"]
    if target["type"] != "∀ (m n : ℕ), n * (m / n) + m % n = m":
        raise PublicLiftPlanError("public target statement changed")
    return [selected[name] for name in NAMES]


def build() -> dict[str, Any]:
    if sha256(PRIVATE_RESULT) != PRIVATE_RESULT_SHA256:
        raise PublicLiftPlanError("private joint invariant result changed")
    statements = selected_statements()
    target = statements[0]
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-euclidean-public-div-add-mod-lift-plan",
        "state": "preregistered-before-public-source-or-kernel-submission",
        "policy_version": "euclidean-public-div-add-mod-lift-v1",
        "inputs": {
            "private_joint_invariant": {
                "path": str(PRIVATE_RESULT.relative_to(ROOT)),
                "sha256": PRIVATE_RESULT_SHA256,
                "theorem_name": "Axeyum.Autogenesis.divModGoReconstruct",
                "declaration_sha256": "f8d6592cd39d5f249acf0f695b1d77bd255dc9f630e3a588a0044fe62d3360a4",
                "axiom_footprint": [],
                "fresh_reconstructions": 2,
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
            "authored_name": "Axeyum.Autogenesis.divAddModReconstruct",
            "statement": target["type"],
            "type_sha256": target["type_sha256"],
            "type_repr_sha256": target["type_repr_sha256"],
            "required_type_relation": "canonical-alpha-expression-identical",
            "required_axiom_footprint": [],
            "fresh_reconstructions": 2,
            "second_run_requires_first_run_acceptance": True,
        },
        "fixed_lift": {
            "source_path": "scripts/lean/autogenesis_div_add_mod_reconstruct.lean",
            "case_split": "divisor zero versus successor",
            "zero_divisor_route": [
                "Nat.div_zero",
                "Nat.mod_zero",
                "Nat.zero_mul",
                "Nat.zero_add",
            ],
            "positive_divisor_route": [
                "Nat.zero_lt_succ",
                "Nat.lt_succ_self",
                "Nat.modCore_eq_mod",
                "transparent Nat.div and Nat.modCore definitions",
                "Axeyum.Autogenesis.divModGoReconstruct",
            ],
            "official_nat_div_add_mod_proof_allowed": False,
            "additional_statement_names_allowed": 0,
            "proof_search_allowed": False,
            "upstream_proof_bodies_allowed": False,
        },
        "gates": {
            "private_invariant_before_public_lift": True,
            "authored_type_must_match_official_target": True,
            "first_footprint_must_be_empty_before_second_run": True,
            "both_declaration_identities_must_match": True,
            "direct_dependencies_must_be_enumerated": True,
            "failed_or_partial_stream_must_not_publish_as_support": True,
        },
        "budget": {
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
        "verification": "python3 scripts/gen-autogenesis-euclidean-public-lift-plan.py --check",
        "limitations": (
            "Even two accepted public-equation reconstructions do not establish balanced "
            "Bezout, coprime cancellation, the Fibonacci target, or ledger credit."
        ),
    }


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate(value: dict[str, Any]) -> None:
    if value != build():
        raise PublicLiftPlanError("public lift plan differs from generated contract")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        value = build()
        expected = render(value)
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != expected:
                raise PublicLiftPlanError(f"{OUTPUT.relative_to(ROOT)} is stale")
            print(
                "AUTOGENESIS_EUCLIDEAN_PUBLIC_LIFT_PLAN_OK|statements=8|"
                "public_submissions=0/2|fibonacci_submissions=0|evaluation=0|ledger_writes=0"
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
        PublicLiftPlanError,
    ) as error:
        print(f"autogenesis-euclidean-public-lift-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
