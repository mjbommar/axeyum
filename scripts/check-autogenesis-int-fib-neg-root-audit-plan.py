#!/usr/bin/env python3
"""Verify the preregistered exact Int.fib_neg root audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-plan-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-neg-b4021d37.json"
ROOT_NAME = "Int.fib_neg"


class IntFibNegRootAuditPlanError(RuntimeError):
    """The exact root, environment, budget, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegRootAuditPlanError(f"{path} is not an object")
    return value


def inventory_root() -> dict[str, Any]:
    if stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444 or sha256(INVENTORY) != "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc":
        raise IntFibNegRootAuditPlanError("statement inventory changed or is mutable")
    with INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            if row.get("name") == ROOT_NAME:
                return {
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
    raise IntFibNegRootAuditPlanError("fixed root is absent")


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (
        1,
        "axeyum-autogenesis-int-fib-neg-root-audit-plan",
        "preregistered-before-single-root-remote-export-or-local-batch-import-no-reconstruction-authority",
        "int-fib-neg-root-audit-v1",
    ):
        raise IntFibNegRootAuditPlanError("Int.fib_neg audit identity changed")
    if plan.get("fixed_root") != inventory_root():
        raise IntFibNegRootAuditPlanError("fixed proof-free root changed")
    fact = load(FACT)
    target = plan.get("inputs", {}).get("target_fact")
    if target != {"path": "artifacts/facts/F-ml430-int-fib-neg-b4021d37.json", "id": "F:ml430-int-fib-neg-b4021d37", "required_status": "open"} or fact.get("id") != target["id"]:
        raise IntFibNegRootAuditPlanError("historical target fact identity changed")
    if plan["inputs"].get("statement_inventory") != {"path": str(INVENTORY), "sha256": "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc", "mode": "0444"}:
        raise IntFibNegRootAuditPlanError("statement inventory identity changed")
    expected_environment = {
        "ssh_alias": "s5", "hostname": "server5",
        "mathlib_checkout": "/home/mjbommar/lean-import-scale/mathlib4",
        "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "mathlib_untracked_baseline": {
            "AxeyumFibGeneric.lean": "f9d3ea9024497cf1aed34a071fe541e515fb4169738d3d369dd6bf9a7ad414be",
            "AxeyumNatFibRecurrencePointwise.lean": "b339a3d8e4ce1700d367fa5fdf0ac0e05d411cc48c49ce6f6e30b702a9b7baf5",
            "AxeyumNatGcdFixEq.lean": "939d225a168b5a94d042ceab47c4dd265a81bf149ea8cfbe08012ca5089373a7"},
        "lean_toolchain": "leanprover/lean4:v4.30.0", "lean_version": "4.30.0",
        "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
        "lake_path": "/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lake",
        "lake_sha256": "d3e1f322c08d87f0d5850132a0b0309c1edbe53d641276b344717da448c8bc8b",
        "module_olean": {"path": "/home/mjbommar/lean-import-scale/mathlib4/.lake/build/lib/lean/Mathlib/Data/Int/Fib/Basic.olean", "bytes": 33800, "sha256": "d8d7618735c7866c929ff7c7fd9df574f1b696e5c50eff300f6a6daf8cf3e3a1"},
        "lean4export_checkout": "/home/mjbommar/lean-import-scale/lean4export",
        "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "lean4export_status_entries": 0, "lean4export_version": "3.1.0",
        "lean4export_binary_sha256": "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"}
    if plan.get("fixed_environment") != expected_environment:
        raise IntFibNegRootAuditPlanError("fixed fleet environment changed")
    measurement = plan.get("fixed_measurement", {})
    if measurement != {
        "export_command_shape": "cd <mathlib_checkout> && <lean-4.30-lake> env <lean4export-binary> Mathlib.Data.Int.Fib.Basic -- Int.fib_neg",
        "proof_bearing_stream": "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1/int-fib-neg.ndjson",
        "output_must_not_preexist": True,
        "tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs",
        "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a",
        "tool_interface": "theorem_footprint_batch_audit <stream> Int.fib_neg",
        "proof_terms_types_or_values_may_be_rendered": False, "root_must_resolve_as_theorem": True,
    } or sha256(ROOT / measurement["tool_path"]) != measurement["tool_sha256"]:
        raise IntFibNegRootAuditPlanError("fixed measurement changed")
    if plan.get("decision_rule") != {"empty_footprint_next": "preregister exact Int.fib_neg capsule composition into the target kernel", "assumption_bearing_next": "preregister one nonrendering audit of exactly the novel direct theorem dependencies", "authorize_either_successor_in_this_increment": False}:
        raise IntFibNegRootAuditPlanError("successor decision rule changed")
    if plan.get("budget") != {"max_exporter_invocations": 1, "max_batch_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_reconstruction_source_compilations": 0, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_executor_invocations": 0}:
        raise IntFibNegRootAuditPlanError("audit budget changed")
    if plan.get("authority") != {"proof_bodies_readable_by_model": False, "theorem_types_readable_by_model": False, "theorem_values_readable_by_model": False, "reconstruction_allowed": False, "support_theorem_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise IntFibNegRootAuditPlanError("audit authority changed")
    if plan.get("output") != "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-result-v1.json" or plan.get("verification") != "python3 scripts/check-autogenesis-int-fib-neg-root-audit-plan.py" or plan.get("limitations") != "This pass measures one official integer Fibonacci theorem. It does not reconstruct or admit Int.fib_neg or Int.gcd_fib and grants no theorem or ledger credit.":
        raise IntFibNegRootAuditPlanError("output or limitation boundary changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_ROOT_AUDIT_PLAN_OK|roots=1|exports=0/1|batch_imports=0/1|reconstructions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegRootAuditPlanError) as error:
        print(f"autogenesis-int-fib-neg-root-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
