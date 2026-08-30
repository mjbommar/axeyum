#!/usr/bin/env python3
"""Verify the preregistered extended-gcd coefficient root audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/extended-gcd-root-audit-plan-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
ROOT_NAME = "Nat.gcd_eq_gcd_ab"


class ExtendedGcdRootAuditPlanError(RuntimeError):
    """The root, fleet environment, budget, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ExtendedGcdRootAuditPlanError(f"{path} is not an object")
    return value


def inventory_root() -> dict[str, Any]:
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or sha256(INVENTORY)
        != "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
    ):
        raise ExtendedGcdRootAuditPlanError("statement inventory changed or is mutable")
    found: dict[str, Any] | None = None
    with INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            if row.get("name") == ROOT_NAME:
                found = {
                    "module": row["module"],
                    "name": ROOT_NAME,
                    "source_row_sha256": hashlib.sha256(
                        json.dumps(row, sort_keys=True, separators=(",", ":")).encode()
                    ).hexdigest(),
                    "type": row["type"],
                    "type_repr_sha256": hashlib.sha256(
                        row["type_repr"].encode()
                    ).hexdigest(),
                }
                break
    if found is None:
        raise ExtendedGcdRootAuditPlanError("fixed root is absent")
    return found


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (
        plan.get("schema_version") != 1
        or plan.get("kind") != "axeyum-autogenesis-extended-gcd-root-audit-plan"
        or plan.get("state")
        != "preregistered-before-single-root-remote-export-or-local-batch-import-no-reconstruction-authority"
        or plan.get("policy_version") != "extended-gcd-coefficient-root-audit-v1"
    ):
        raise ExtendedGcdRootAuditPlanError("extended-gcd audit identity changed")
    if plan.get("fixed_root") != inventory_root():
        raise ExtendedGcdRootAuditPlanError("fixed proof-free root changed")
    for key, path, expected in [
        (
            "public_gcd_def_decline",
            "artifacts/autogenesis/public-gcd-def-direct-reconstruction-result-v1.json",
            "fe3c2ffc68d89e64c7a179cb87e5aa1ac534bfe7de0be89566240fb6ae473f90",
        ),
        (
            "generated_gcd_dependency_audit",
            "artifacts/autogenesis/generated-gcd-novel-dependency-audit-result-v1.json",
            "30698c40a963f6d39880a366cb318bc4da60ae5907957cb9731961fda75ca107",
        ),
    ]:
        row = plan["inputs"][key]
        if row != {"path": path, "sha256": expected} or sha256(ROOT / path) != expected:
            raise ExtendedGcdRootAuditPlanError(f"{key} identity changed")
    if plan["inputs"].get("statement_inventory") != {
        "path": str(INVENTORY),
        "sha256": "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc",
        "mode": "0444",
    }:
        raise ExtendedGcdRootAuditPlanError("statement inventory identity changed")
    if plan.get("fixed_environment") != {
        "ssh_alias": "s5",
        "hostname": "server5",
        "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "mathlib_status_entries": 0,
        "lean_toolchain": "leanprover/lean4:v4.30.0",
        "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "module_olean": {
            "path": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/Mathlib/Data/Int/GCD.olean",
            "bytes": 101976,
            "sha256": "97e242adc99140b6355053247cf26c35504661f9248875f6d24886b2558a27c3",
        },
        "lean4export_checkout": "/home/mjbommar/lean-import-scale/lean4export",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_status_entries": 0,
        "lean4export_version": "3.1.0",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449",
    }:
        raise ExtendedGcdRootAuditPlanError("fixed fleet environment changed")
    measurement = plan.get("fixed_measurement", {})
    if measurement != {
        "export_command_shape": "cd <mathlib_checkout> && <lean-4.30-bin>/lake env <lean4export-binary> Mathlib.Data.Int.GCD -- Nat.gcd_eq_gcd_ab",
        "proof_bearing_stream": "/nas3/data/axeyum/autogenesis/reference-packs/609241d91-extended-gcd-root-audit-v1/extended-gcd.ndjson",
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a",
        "tool_interface": "theorem_footprint_batch_audit <stream> Nat.gcd_eq_gcd_ab",
        "proof_terms_types_or_values_may_be_rendered": False,
        "root_must_resolve_as_theorem": True,
    } or sha256(ROOT / measurement["tool_path"]) != measurement["tool_sha256"]:
        raise ExtendedGcdRootAuditPlanError("fixed measurement changed")
    if plan.get("decision_rule") != {
        "empty_footprint_next": "preregister a target-side integer coefficient adapter using gcdA and gcdB",
        "assumption_bearing_next": "preregister an audit of exactly the root's novel direct theorem dependencies",
        "authorize_either_successor_in_this_increment": False,
    }:
        raise ExtendedGcdRootAuditPlanError("successor decision rule changed")
    if plan.get("budget") != {
        "max_exporter_invocations": 1,
        "max_batch_importer_runs": 1,
        "max_proof_bearing_stream_reads": 1,
        "max_retries": 0,
        "max_reconstruction_source_compilations": 0,
        "max_new_theorem_submissions": 0,
        "max_exact_target_submissions": 0,
        "max_executor_invocations": 0,
    }:
        raise ExtendedGcdRootAuditPlanError("audit budget changed")
    if plan.get("authority") != {
        "proof_bodies_readable_by_model": False,
        "theorem_types_readable_by_model": False,
        "theorem_values_readable_by_model": False,
        "reconstruction_allowed": False,
        "support_theorem_credit": 0,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ExtendedGcdRootAuditPlanError("audit authority changed")
    if (
        plan.get("output")
        != "artifacts/autogenesis/extended-gcd-root-audit-result-v1.json"
        or plan.get("verification")
        != "python3 scripts/check-autogenesis-extended-gcd-root-audit-plan.py"
        or plan.get("limitations")
        != "This pass measures one official extended-gcd theorem. It does not reconstruct gcd, Bezout, cancellation, or Fibonacci results and grants no theorem or ledger credit."
    ):
        raise ExtendedGcdRootAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EXTENDED_GCD_ROOT_AUDIT_PLAN_OK|roots=1|"
            "exports=0/1|batch_imports=0/1|reconstructions=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        ExtendedGcdRootAuditPlanError,
    ) as error:
        print(f"autogenesis-extended-gcd-root-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
