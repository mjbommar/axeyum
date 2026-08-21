#!/usr/bin/env python3
"""Verify the two-root integer Fibonacci recurrence support audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-support-audit-plan-v1.json"
DECISION = ROOT / "artifacts/autogenesis/mathlib-int-fib-of-odd-private-root-audit-result-v1.json"
STREAM = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1/int-fib-neg.ndjson")
FACTS = [ROOT / "artifacts/facts/F-ml430-int-fib-natcast-d5886be4.json", ROOT / "artifacts/facts/F-ml430-int-fib-add-two-739358dd.json"]


class IntFibRecurrenceSupportAuditPlanError(RuntimeError):
    """The open support facts, evidence, budget, or authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibRecurrenceSupportAuditPlanError(f"{path} is not an object")
    return value


def validate(plan: dict[str, Any] | None = None) -> dict[str, Any]:
    plan = load(PLAN) if plan is None else plan
    if (plan.get("schema_version"), plan.get("kind"), plan.get("state"), plan.get("policy_version")) != (1, "axeyum-autogenesis-int-fib-recurrence-support-audit-plan", "preregistered-before-single-nonrendering-reread-no-reconstruction-authority", "int-fib-recurrence-support-audit-v1"):
        raise IntFibRecurrenceSupportAuditPlanError("audit identity changed")
    if sha256(DECISION) != "fce124c65d3595a3d0a3ada24080c8804356fac184c0236a4155389d32815eb6" or plan.get("ordered_roots") != ["Int.fib_natCast", "Int.fib_add_two"]:
        raise IntFibRecurrenceSupportAuditPlanError("decision or roots changed")
    fact_values = [load(path) for path in FACTS]
    if plan.get("target_facts") != [value["id"] for value in fact_values] or any(value.get("epistemic_status") != "open" for value in fact_values):
        raise IntFibRecurrenceSupportAuditPlanError("open target facts changed")
    stream = plan.get("inputs", {}).get("proof_bearing_stream")
    if stream != {"path": str(STREAM), "bytes": 14_596_588, "sha256": "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e", "mode": "0444", "textual_read_allowed": False} or STREAM.stat().st_size != 14_596_588 or stat.S_IMODE(STREAM.stat().st_mode) != 0o444 or sha256(STREAM) != stream["sha256"]:
        raise IntFibRecurrenceSupportAuditPlanError("sealed stream changed")
    if plan.get("decision_rule") != {"next": "make Int.fib_natCast the first construction target unless both roots are already empty-footprint; never treat open ledger facts as admitted premises", "authorize_successor_in_this_increment": False}:
        raise IntFibRecurrenceSupportAuditPlanError("decision rule changed")
    if plan.get("budget", {}).get("max_batch_importer_runs") != 1 or plan["budget"].get("max_proof_bearing_stream_reads") != 1 or plan.get("authority", {}).get("reconstruction_allowed") is not False or plan["authority"].get("ledger_writes") != 0:
        raise IntFibRecurrenceSupportAuditPlanError("budget or authority changed")
    return plan


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_RECURRENCE_SUPPORT_AUDIT_PLAN_OK|roots=2|open_facts=2|batch_imports=0/1|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibRecurrenceSupportAuditPlanError) as error:
        print(f"autogenesis-int-fib-recurrence-support-audit-plan: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
