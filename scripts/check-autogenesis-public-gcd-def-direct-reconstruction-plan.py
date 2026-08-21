#!/usr/bin/env python3
"""Verify the one-shot public gcd definition reconstruction plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/public-gcd-def-direct-reconstruction-plan-v1.json"
CARRIER = ROOT / "artifacts/autogenesis/generated-gcd-novel-dependency-audit-result-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
CARRIER_SHA256 = "30698c40a963f6d39880a366cb318bc4da60ae5907957cb9731961fda75ca107"
INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"


class PublicGcdDefDirectPlanError(RuntimeError):
    """The target, direct method, budget, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise PublicGcdDefDirectPlanError(f"{path} is not an object")
    return value


def inventory_target() -> dict[str, Any]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise PublicGcdDefDirectPlanError("statement inventory changed")
    with INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            if row.get("name") == "Nat.gcd_def":
                return {
                    "module": row["module"],
                    "name": row["name"],
                    "source_row_sha256": hashlib.sha256(
                        json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
                    ).hexdigest(),
                    "type": row["type"],
                    "type_sha256": hashlib.sha256(row["type"].encode()).hexdigest(),
                    "type_repr_sha256": hashlib.sha256(row["type_repr"].encode()).hexdigest(),
                    "authored_name": "Axeyum.Autogenesis.gcdDefDirect",
                }
    raise PublicGcdDefDirectPlanError("Nat.gcd_def is absent")


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("kind")
        != "axeyum-autogenesis-public-gcd-def-direct-reconstruction-plan"
        or plan.get("state")
        != "preregistered-before-one-source-compilation-no-public-equation-credit"
        or plan.get("policy_version") != "public-gcd-def-direct-reconstruction-v1"
    ):
        raise PublicGcdDefDirectPlanError("plan identity changed")
    if sha256(CARRIER) != CARRIER_SHA256 or plan.get("target") != inventory_target():
        raise PublicGcdDefDirectPlanError("carrier or target identity changed")
    if plan.get("inputs") != {
        "carrier_result": {
            "path": "artifacts/autogenesis/generated-gcd-novel-dependency-audit-result-v1.json",
            "sha256": CARRIER_SHA256,
        },
        "statement_inventory": {
            "path": str(INVENTORY),
            "sha256": INVENTORY_SHA256,
            "mode": "0444",
        },
    }:
        raise PublicGcdDefDirectPlanError("plan inputs changed")
    if plan.get("construction") != {
        "source_path": "scripts/lean/autogenesis_gcd_def_direct.lean",
        "method": "case split on x and definitional reduction only",
        "proof_search_allowed": False,
        "upstream_proof_bodies_read": False,
        "forbidden_dependencies": [
            "Nat.gcd_def",
            "WellFounded.Nat.fix_eq",
            "_private.Init.Data.Nat.Gcd.0.Nat.gcd.eq_def",
            "_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def",
            "Quot",
            "Quot.lift",
            "Quot.mk",
            "Quot.sound",
        ],
        "forbidden_tactics": ["aesop", "simp", "simpa", "omega", "native_decide"],
    }:
        raise PublicGcdDefDirectPlanError("construction changed")
    if plan.get("acceptance") != {
        "source_must_compile": True,
        "exported_type_must_match_target": True,
        "fresh_kernel_reconstructions_required": 2,
        "axiom_footprint_must_be_empty": True,
        "forbidden_dependencies_must_be_absent": True,
        "failed_compilation_ends_increment": True,
    }:
        raise PublicGcdDefDirectPlanError("acceptance changed")
    if plan.get("budget") != {
        "max_source_compilations": 1,
        "max_exporter_invocations": 1,
        "max_importer_runs": 2,
        "max_retries": 0,
        "max_new_theorem_submissions": 2,
        "max_exact_fibonacci_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise PublicGcdDefDirectPlanError("budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "proof_search_allowed": False,
        "public_gcd_equation_credit": 0,
        "balanced_bezout_reconstruction_allowed": False,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise PublicGcdDefDirectPlanError("authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/public-gcd-def-direct-reconstruction-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-public-gcd-def-direct-reconstruction-plan.py"
        or plan.get("limitations")
        != "The attempt tests whether the public gcd equation follows by direct definitional reduction without the isolated fix equation. Failure does not refute a target-owned gcd; success still requires two empty-footprint kernel reconstructions."
    ):
        raise PublicGcdDefDirectPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_PUBLIC_GCD_DEF_DIRECT_PLAN_OK|compilations=0/1|"
            "exports=0/1|imports=0/2|equation_credit=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        PublicGcdDefDirectPlanError,
    ) as error:
        print(f"autogenesis-public-gcd-def-direct-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
