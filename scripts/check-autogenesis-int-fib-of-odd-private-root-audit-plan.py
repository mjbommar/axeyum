#!/usr/bin/env python3
"""Verify the private Int.fib_of_odd root audit plan."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-odd-private-root-audit-plan-v1.json"
PARENT_RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-natcast-dependency-audit-result-v1.json"
PARENT_AUDIT = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-natcast-dependency-audit-v1/audit.json")
STREAM = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1/int-fib-neg.ndjson")
TOOL = ROOT / "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs"
PRIVATE_ROOT = "_private.Mathlib.Data.Int.Fib.Basic.0.Int.fib_of_odd._proof_1_2"


class IntFibOfOddPrivateRootAuditPlanError(RuntimeError):
    """The private root, sealed evidence, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibOfOddPrivateRootAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (1, "axeyum-autogenesis-int-fib-of-odd-private-root-audit-plan", "preregistered-before-single-nonrendering-reread-no-reconstruction-authority", "int-fib-of-odd-private-root-audit-v1"):
        raise IntFibOfOddPrivateRootAuditPlanError("audit identity changed")
    if sha256(PARENT_RESULT) != "6b06b0ecfc0bb0c1bd6be931c63977a4466eb2dd71412563e2bd16853a9c83d4" or sha256(PARENT_AUDIT) != "3ab13740a7ce1c9b1bfdbe917ee9976316b0e9f953a74a21ccf74e099a6e9bb2":
        raise IntFibOfOddPrivateRootAuditPlanError("parent evidence changed")
    rows = {row["name"]: row for row in load(PARENT_AUDIT)["rows"]}
    if rows["Int.fib_of_odd"]["direct_theorem_dependencies"] != [PRIVATE_ROOT] or plan.get("fixed_root") != PRIVATE_ROOT:
        raise IntFibOfOddPrivateRootAuditPlanError("private root changed")
    expected_stream = {"path": str(STREAM), "bytes": 14_596_588, "sha256": "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e", "mode": "0444", "textual_read_allowed": False}
    if plan["inputs"].get("proof_bearing_stream") != expected_stream or STREAM.stat().st_size != expected_stream["bytes"] or stat.S_IMODE(STREAM.stat().st_mode) != 0o444 or sha256(STREAM) != expected_stream["sha256"]:
        raise IntFibOfOddPrivateRootAuditPlanError("sealed stream changed")
    if plan.get("fixed_measurement") != {"tool_path": "crates/axeyum-lean-import/examples/theorem_footprint_batch_audit.rs", "tool_sha256": "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a", "proof_terms_types_or_values_may_be_rendered": False, "root_must_resolve_as_theorem": True} or sha256(TOOL) != "38e40236fec86f1080af52bafb9394f9f1505ad161dae96e9c48979d00b1094a":
        raise IntFibOfOddPrivateRootAuditPlanError("measurement changed")
    if plan.get("budget") != {"max_exporter_invocations": 0, "max_batch_importer_runs": 1, "max_proof_bearing_stream_reads": 1, "max_retries": 0, "max_reconstruction_source_compilations": 0, "max_new_theorem_submissions": 0, "max_exact_target_submissions": 0, "max_executor_invocations": 0} or plan.get("authority", {}).get("reconstruction_allowed") is not False or plan["authority"].get("ledger_writes") != 0:
        raise IntFibOfOddPrivateRootAuditPlanError("budget or authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_OF_ODD_PRIVATE_ROOT_AUDIT_PLAN_OK|roots=1|batch_imports=0/1|reconstructions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibOfOddPrivateRootAuditPlanError) as error:
        print(f"autogenesis-int-fib-of-odd-private-root-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
