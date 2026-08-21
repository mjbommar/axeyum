#!/usr/bin/env python3
"""Verify the subtractive gcd foundation root audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/subtractive-gcd-root-audit-plan-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
NAMES = [
    "Nat.gcd_one_left",
    "Nat.gcd_one_right",
    "Nat.gcd_self",
    "Nat.gcd_sub_self_left",
    "Nat.gcd_sub_self_right",
    "Nat.gcd_zero_left",
    "Nat.gcd_zero_right",
]


class SubtractiveGcdAuditPlanError(RuntimeError):
    """The gcd roots, batch audit contract, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SubtractiveGcdAuditPlanError(f"{path} is not an object")
    return value


def inventory_roots() -> list[dict[str, Any]]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY)
        != "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
    ):
        raise SubtractiveGcdAuditPlanError("statement inventory changed or is mutable")
    selected: dict[str, dict[str, Any]] = {}
    with INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            name = row.get("name")
            if name not in NAMES:
                continue
            selected[name] = {
                "module": row["module"],
                "name": name,
                "source_row_sha256": hashlib.sha256(
                    json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
                ).hexdigest(),
                "type": row["type"],
                "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
            }
    if set(selected) != set(NAMES):
        raise SubtractiveGcdAuditPlanError("one or more fixed roots are absent")
    return [selected[name] for name in NAMES]


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind") != "axeyum-autogenesis-subtractive-gcd-root-audit-plan"
        or plan.get("state")
        != "preregistered-before-root-export-or-batch-import-no-bezout-authority"
        or plan.get("policy_version") != "subtractive-gcd-foundation-root-audit-v1"
    ):
        raise SubtractiveGcdAuditPlanError("subtractive gcd audit identity changed")
    if plan.get("fixed_roots") != inventory_roots():
        raise SubtractiveGcdAuditPlanError("fixed proof-free gcd roots changed")
    for key, path, expected in [
        (
            "declined_target_shortcut",
            "artifacts/autogenesis/coprime-target-cancellation-root-audit-result-v1.json",
            "40bdb03cc7319228187e94d9316537a662b017113cf30ab1ed29463dd09a96e5",
        ),
        (
            "public_equation_carrier_audit",
            "artifacts/autogenesis/euclidean-public-equation-carrier-audit-result-v1.json",
            "544bde51a25e42f309ef7fecd1dae521527cf4efd2b1b01dccca9c0f07556edd",
        ),
    ]:
        row = plan["inputs"][key]
        if row != {"path": path, "sha256": expected} or sha256(ROOT / path) != expected:
            raise SubtractiveGcdAuditPlanError(f"{key} identity changed")
    if plan["inputs"].get("statement_inventory") != {
        "path": str(INVENTORY),
        "sha256": "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc",
        "mode": "0444",
    }:
        raise SubtractiveGcdAuditPlanError("statement inventory identity changed")
    measurement = plan["fixed_measurement"]
    if (
        measurement.get("export_module") != "Init"
        or measurement.get("tool_path")
        != "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
        or measurement.get("tool_interface")
        != "theorem_footprint_batch_audit <stream> <root>..."
        or measurement.get("root_order_must_match_plan") is not True
        or measurement.get("proof_terms_or_values_may_be_rendered") is not False
        or measurement.get("all_roots_must_resolve_as_theorems") is not True
        or measurement.get("all_roots_must_have_empty_footprints_for_successor_bezout")
        is not True
    ):
        raise SubtractiveGcdAuditPlanError("fixed batch measurement changed")
    if plan["budget"] != {
        "max_exporter_invocations": 1,
        "max_batch_importer_runs": 1,
        "max_retries": 0,
        "max_bezout_source_compilations": 0,
        "max_new_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise SubtractiveGcdAuditPlanError("audit budget changed")
    if plan["authority"] != {
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "subtractive_bezout_proof_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise SubtractiveGcdAuditPlanError("audit authority changed")
    if plan.get("proposed_successor") != {
        "construction": "primitive induction on a + c using gcd-preserving subtraction and balanced natural coefficients",
        "division_or_modulo_dependencies_allowed": False,
        "successor_bezout_authorized_after_audit": False,
    }:
        raise SubtractiveGcdAuditPlanError("successor boundary changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/subtractive-gcd-root-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-subtractive-gcd-root-audit-plan.py"
        or plan.get("limitations")
        != "The audit tests only whether the official gcd subtraction/base interface is an axiom-free foundation. It proves no Bezout or cancellation theorem."
    ):
        raise SubtractiveGcdAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_SUBTRACTIVE_GCD_ROOT_AUDIT_PLAN_OK|roots=7|"
            "exports=0/1|batch_imports=0/1|bezout_submissions=0|"
            "target_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        SubtractiveGcdAuditPlanError,
    ) as error:
        print(f"autogenesis-subtractive-gcd-root-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
