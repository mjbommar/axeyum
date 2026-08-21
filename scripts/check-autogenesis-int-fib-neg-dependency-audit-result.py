#!/usr/bin/env python3
"""Verify the sealed 26-root Int.fib_neg dependency classification."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-dependency-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-dependency-audit-v1")
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit.json"
RESULT_SHA256 = "51207e379248e6af00095be478fe0963f157113bf2df757aa2a26c4804aeac9a"
PLAN_SHA256 = "39294a126e921cb25cc89f97cf51cf6cd115993ec1d284b9337b53da3d2d8540"
MANIFEST_SHA256 = "8233a87e297d488fb94b0611b0127303b70fb62510463afd75b234cae81711af"
AUDIT_SHA256 = "1b39ac55f6993a7a740c7dc88ae50a4d70cd798cfeff9944a077f06837173832"


class IntFibNegDependencyAuditResultError(RuntimeError):
    """The evidence identity, classification, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegDependencyAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise IntFibNegDependencyAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise IntFibNegDependencyAuditResultError("measured dependency result changed")
    if result.get("kind") != "axeyum-autogenesis-int-fib-neg-dependency-audit-result" or result.get("state") != "integer-case-split-clean-negative-nat-core-assumption-bearing" or sha256(PLAN) != PLAN_SHA256 or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444 or sha256(MANIFEST) != MANIFEST_SHA256 or AUDIT.stat().st_size != 10_551 or stat.S_IMODE(AUDIT.stat().st_mode) != 0o444 or sha256(AUDIT) != AUDIT_SHA256:
        raise IntFibNegDependencyAuditResultError("result producer or pack changed")
    audit = load(AUDIT)
    rows = audit.get("rows", [])
    empty = [row["name"] for row in rows if row["class"] == "empty-footprint"]
    bearing = [row["name"] for row in rows if row["class"] != "empty-footprint"]
    by_name = {row["name"]: row for row in rows}
    fib_core = by_name.get("Int.fib_neg_natCast", {})
    case_split = by_name.get("Int.eq_nat_or_neg", {})
    if audit.get("summary") != {"population": 26, "class_counts": {"empty-footprint": 14, "other-assumption-bearing": 0, "propext-bearing": 12}, "all_roots_empty": False} or audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0} or result.get("summary") != {"population": 26, "empty_footprint": 14, "propext_bearing": 12, "other_assumption_bearing": 0} or result.get("empty_footprint_roots") != empty or result.get("assumption_bearing_roots") != bearing:
        raise IntFibNegDependencyAuditResultError("classification changed")
    expected_case = {"name": "Int.eq_nat_or_neg", "declaration_sha256": "357fe10e86f4a880773cbb62a8272d403b274c1b8bb130f882bea8fb8cb39d4d", "direct_theorem_dependencies": ["Int.natAbs_eq"]}
    expected_core = {"name": "Int.fib_neg_natCast", "declaration_sha256": "13062bcdedb7c2bd3058504ec8a55942704018e2297c7b20bb6935bc7d3d71ec", "direct_theorem_dependency_count": 36, "axiom_footprint": ["Classical.choice", "Lean.opaqueId", "Quot", "Quot.ind", "Quot.lift", "Quot.mk", "Quot.sound", "String.Internal.append", "propext"]}
    if case_split.get("class") != "empty-footprint" or result.get("key_frontier", {}).get("clean_integer_case_split") != expected_case or fib_core.get("class") != "propext-bearing" or len(fib_core.get("direct_theorem_dependencies", [])) != 36 or result.get("key_frontier", {}).get("assumption_bearing_negative_nat_core") != expected_core:
        raise IntFibNegDependencyAuditResultError("key mathematical frontier changed")
    if result.get("decision") != {"direct_official_composition_authorized": False, "smallest_next_root": "Int.fib_neg_natCast", "next_action": "preregister one nonrendering audit of its exact 36 direct theorem dependencies"}:
        raise IntFibNegDependencyAuditResultError("successor decision changed")
    if result.get("budget") != {"exporter_invocations": 0, "batch_importer_runs": 1, "proof_bearing_stream_reads": 1, "retries": 0, "reconstruction_source_compilations": 0, "new_theorem_submissions": 0, "exact_target_submissions": 0, "executor_invocations": 0} or result.get("authority") != {"proof_terms_rendered": 0, "theorem_types_rendered": 0, "theorem_values_rendered": 0, "support_theorem_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise IntFibNegDependencyAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_DEPENDENCY_AUDIT_RESULT_OK|roots=26|clean=14|bearing=12|next=Int.fib_neg_natCast|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegDependencyAuditResultError) as error:
        print(f"autogenesis-int-fib-neg-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
