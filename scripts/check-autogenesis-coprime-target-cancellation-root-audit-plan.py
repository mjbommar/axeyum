#!/usr/bin/env python3
"""Verify the target-side coprime cancellation root audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/coprime-target-cancellation-root-audit-plan-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
NAMES = [
    "Nat.Coprime.coprime_dvd_left",
    "Nat.Coprime.dvd_of_dvd_mul_left",
    "Nat.Coprime.eq_1",
]


class CoprimeRootAuditPlanError(RuntimeError):
    """The target roots, proof-free identities, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CoprimeRootAuditPlanError(f"{path} is not an object")
    return value


def inventory_roots() -> list[dict[str, Any]]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY)
        != "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
    ):
        raise CoprimeRootAuditPlanError("statement inventory changed or is mutable")
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
                "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
            }
    if set(selected) != set(NAMES):
        raise CoprimeRootAuditPlanError("one or more fixed roots are absent")
    return [selected[name] for name in NAMES]


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind")
        != "axeyum-autogenesis-coprime-target-cancellation-root-audit-plan"
        or plan.get("state")
        != "preregistered-before-root-export-or-import-no-support-authority"
        or plan.get("policy_version") != "target-coprime-cancellation-root-audit-v1"
    ):
        raise CoprimeRootAuditPlanError("coprime root audit identity changed")
    if plan.get("fixed_roots") != inventory_roots():
        raise CoprimeRootAuditPlanError("fixed proof-free roots changed")
    for key, expected in {
        "native_support_result": "62aaba46d9aadaa378c0f0efdc847030d5f801794d926d67432a626d44e2b3e2",
        "public_equation_carrier_audit": "544bde51a25e42f309ef7fecd1dae521527cf4efd2b1b01dccca9c0f07556edd",
    }.items():
        row = plan["inputs"][key]
        if row.get("sha256") != expected or sha256(ROOT / row["path"]) != expected:
            raise CoprimeRootAuditPlanError(f"{key} identity changed")
    measurement = plan["fixed_measurement"]
    if (
        measurement.get("export_module") != "Init"
        or measurement.get("tool_path")
        != "crates/axeyum-lean-import/examples/coprime_target_support_audit.rs"
        or measurement.get("proof_terms_or_values_may_be_rendered") is not False
        or measurement.get("all_roots_must_resolve_as_theorems") is not True
        or measurement.get("all_roots_must_have_empty_footprints_for_successor_proof")
        is not True
    ):
        raise CoprimeRootAuditPlanError("fixed measurement changed")
    if plan["budget"] != {
        "max_exporter_invocations": 1,
        "max_importer_runs": 1,
        "max_retries": 0,
        "max_authored_support_compilations": 0,
        "max_new_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise CoprimeRootAuditPlanError("audit budget changed")
    if plan["authority"] != {
        "proof_bodies_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "target_cancellation_proof_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise CoprimeRootAuditPlanError("audit authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_COPRIME_TARGET_ROOT_AUDIT_PLAN_OK|roots=3|"
            "exports=0/1|imports=0/1|support_submissions=0|"
            "target_submissions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        CoprimeRootAuditPlanError,
    ) as error:
        print(f"autogenesis-coprime-target-root-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
