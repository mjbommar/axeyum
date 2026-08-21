#!/usr/bin/env python3
"""Verify the sealed cancellation-to-Acc path audit."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/official-cancellation-acc-path-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/official-cancellation-acc-path-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/audits/7d931d9d3-official-cancellation-acc-path-audit-v1")
PLAN_SHA = "2a2ddb119ec0c99a119fa1cbe2b584be078ff0d8d611f87439b2dea6fa4472ad"
MANIFEST_SHA = "d538ab62038d3b911d465acbb26319d47a38d356da0009602b50454cf5fb5acc"
AUDIT_SHA = "f0ab2f537e7ada7d15c65924eed759241fb657757d0675082a9eb2e22969f221"
PACKAGE = ["Acc", "Acc.intro", "Acc.rec"]


class AuditResultError(RuntimeError):
    """The sealed measurement or its zero-authority boundary changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AuditResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (result.get("schema_version"), result.get("kind"), result.get("state")) != (
        1,
        "axeyum-autogenesis-official-cancellation-acc-path-audit-result",
        "single-read-complete-canonical-acc-package-is-nearest-missing-carrier",
    ):
        raise AuditResultError("result identity changed")
    if sha256(PLAN) != PLAN_SHA or result["plan"]["sha256"] != PLAN_SHA:
        raise AuditResultError("plan identity changed")
    if sha256(PACK / "manifest.json") != MANIFEST_SHA or sha256(PACK / "result.json") != AUDIT_SHA:
        raise AuditResultError("sealed evidence identity changed")
    if stat.S_IMODE(PACK.stat().st_mode) != 0o555 or any(
        stat.S_IMODE(path.stat().st_mode) != 0o444 for path in PACK.iterdir()
    ):
        raise AuditResultError("evidence pack is not sealed")
    audit = load(PACK / "result.json")
    rows = audit["carriers_nearest_first"]
    if len(rows) != 16 or audit["root_closure_size"] != 382:
        raise AuditResultError("carrier population changed")
    if [row["name"] for row in rows[:3]] != PACKAGE:
        raise AuditResultError("nearest complete package changed")
    if any(row["target"] is not None or row["source_axiom_footprint"] for row in rows):
        raise AuditResultError("target presence or carrier footprint changed")
    if audit["execution"] != {"kernel_submissions": 0, "retries": 0, "source_reads": 1, "target_reads": 1}:
        raise AuditResultError("execution budget changed")
    if audit["rendered_material"] != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}:
        raise AuditResultError("proof material was rendered")
    if result["summary"]["nearest_complete_package"] != PACKAGE:
        raise AuditResultError("result package summary changed")
    if any(result["authority"][key] != 0 for key in ("support_credit", "target_credit", "fact_status_changes", "evaluation_credit", "ledger_writes")):
        raise AuditResultError("zero-authority boundary changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_OFFICIAL_CANCELLATION_ACC_PATH_AUDIT_RESULT_OK|carriers=16|nearest=Acc|submissions=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, AuditResultError) as error:
        print(f"official-cancellation-acc-path-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
