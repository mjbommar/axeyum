#!/usr/bin/env python3
"""Verify the sealed Int.fib_neg audit and its no-credit conclusion."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-result-v1.json"
PLAN = ROOT / "artifacts/autogenesis/mathlib-int-fib-neg-root-audit-plan-v1.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-root-audit-v1")
MANIFEST = PACK / "manifest.json"
AUDIT = PACK / "audit.json"
RESULT_SHA256 = "b500a897382de74e1718de52b5a2b965eef64a935e3186219a6d73aab1a7125d"
PLAN_SHA256 = "fb67e1fdf5d56dc12c0b855406db19a1196c46513b0acf902a72b6291e39150d"
MANIFEST_SHA256 = "c1ba7157b8f644bbfda48d4db4b4e528eb2705bd7600f0f033304d678f48f3fd"
FOOTPRINT = ["Classical.choice", "Lean.opaqueId", "Quot", "Quot.ind", "Quot.lift", "Quot.mk", "Quot.sound", "String.Internal.append", "propext"]
DEPENDENCIES = ["Eq.symm", "Eq.trans", "Even.add_one._simp_1", "Even.neg_pow", "Int.eq_nat_or_neg", "Int.even_coe_nat._simp_1", "Int.fib_neg_natCast", "Nat.not_even_iff_odd._simp_1", "Odd.add_one._simp_1", "Odd.neg_one_pow", "congr", "congrArg", "congrFun'", "eq_self", "even_neg._simp_1", "if_neg", "if_pos", "implies_congr_ctx", "implies_true", "ite_congr", "left_eq_ite_iff._simp_1", "neg_mul", "neg_neg", "of_eq_true", "one_mul", "one_pow"]


class IntFibNegRootAuditResultError(RuntimeError):
    """The evidence identity, measured decline, or no-credit authority changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise IntFibNegRootAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != RESULT_SHA256:
        raise IntFibNegRootAuditResultError("tracked result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise IntFibNegRootAuditResultError("measured Int.fib_neg result changed")
    if result.get("kind") != "axeyum-autogenesis-int-fib-neg-root-audit-result" or result.get("state") != "official-int-fib-neg-is-assumption-bearing-exact-dependency-descent-required" or sha256(PLAN) != PLAN_SHA256 or stat.S_IMODE(PACK.stat().st_mode) != 0o555 or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444 or sha256(MANIFEST) != MANIFEST_SHA256:
        raise IntFibNegRootAuditResultError("result producer or pack changed")
    identities = [
        ("int-fib-neg.ndjson", 14_596_588, "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e"),
        ("export.stderr", 0, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("audit.json", 1_841, "96286135e00fcbfd3b5de03e78eab7463be294d1b40fc4a61121f7e11bff2558"),
    ]
    for name, size, digest in identities:
        path = PACK / name
        if stat.S_IMODE(path.stat().st_mode) != 0o444 or path.stat().st_size != size or sha256(path) != digest:
            raise IntFibNegRootAuditResultError(f"{name} changed")
    audit = load(AUDIT)
    if audit.get("ordered_roots") != ["Int.fib_neg"] or audit.get("rows") != [result["row"]] or audit.get("rendered_material") != {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0} or audit.get("input") != {"path": str(PACK / "int-fib-neg.ndjson"), "bytes": 14_596_588, "sha256": "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e", "stream_axioms": ["Classical.choice", "Quot.sound", "propext"]}:
        raise IntFibNegRootAuditResultError("batch measurement changed")
    row = result.get("row", {})
    if row.get("name") != "Int.fib_neg" or row.get("declaration_sha256") != "45a27bc3b444c7b3c68cd20a919d34b65c095dd06cf8a66b2b0725190a587c48" or row.get("class") != "propext-bearing" or row.get("axiom_footprint") != FOOTPRINT or row.get("direct_theorem_dependencies") != DEPENDENCIES or result.get("summary") != {"population": 1, "empty_footprint": 0, "propext_bearing": 1, "direct_theorem_dependency_count": 26, "exact_capsule_composition_authorized": False, "exact_dependency_audit_required": True}:
        raise IntFibNegRootAuditResultError("decline or dependency frontier changed")
    if result.get("budget") != {"exporter_invocations": 1, "batch_importer_runs": 1, "proof_bearing_stream_reads": 1, "retries": 0, "reconstruction_source_compilations": 0, "new_theorem_submissions": 0, "exact_target_submissions": 0, "executor_invocations": 0} or result.get("authority") != {"proof_terms_rendered": 0, "theorem_types_rendered": 0, "theorem_values_rendered": 0, "support_theorem_credit": 0, "fact_status_changes": 0, "evaluation_credit": 0, "ledger_writes": 0}:
        raise IntFibNegRootAuditResultError("no-credit authority changed")
    return result


def main() -> int:
    try:
        validate()
        print("AUTOGENESIS_INT_FIB_NEG_ROOT_AUDIT_RESULT_OK|root=Int.fib_neg|class=propext-bearing|dependencies=26|reconstructions=0|ledger_writes=0")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, IntFibNegRootAuditResultError) as error:
        print(f"autogenesis-int-fib-neg-root-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
