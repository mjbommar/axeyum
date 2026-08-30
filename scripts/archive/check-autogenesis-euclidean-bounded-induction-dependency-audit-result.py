#!/usr/bin/env python3
"""Verify the one-pass bounded-induction dependency audit result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-bounded-induction-dependency-audit-result-v1.json"
)
PLAN = ROOT / (
    "artifacts/autogenesis/"
    "euclidean-bounded-induction-dependency-audit-plan-v1.json"
)
TOOL = ROOT / (
    "crates/axeyum-lean-import/examples/"
    "euclidean_bounded_dependency_footprint_audit.rs"
)
PACK = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "3e44665e3-bounded-induction-dependency-audit-v1"
)
MANIFEST = PACK / "manifest.json"
NAMES = [
    "And.left",
    "And.right",
    "Eq.symm",
    "Nat.add_assoc",
    "Nat.add_comm",
    "Nat.div_eq",
    "Nat.le_of_lt_succ",
    "Nat.le_of_succ_le_succ",
    "Nat.le_or_eq_of_le_succ",
    "Nat.le_refl",
    "Nat.lt_of_lt_of_le",
    "Nat.mod_eq",
    "Nat.mul_add",
    "Nat.mul_one",
    "Nat.not_succ_le_zero",
    "Nat.sub_lt",
    "Nat.succ_sub_succ_eq_sub",
    "congr",
    "congrArg",
    "congrFun'",
    "if_neg",
    "if_pos",
]


class BoundedAuditResultError(RuntimeError):
    """The producing tool, exact audit result, or no-credit boundary changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise BoundedAuditResultError(f"{path} is not an object")
    return value


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    canonical = load(RESULT)
    if sha256(RESULT) != "bd839c84c4ec29d2a6a3a0615e14e8c6c32e42d7a949bf9a37930167695e3c07":
        raise BoundedAuditResultError("tracked audit result identity changed")
    result = canonical if result is None else result
    if result != canonical:
        raise BoundedAuditResultError("measured dependency audit changed")
    if (
        result.get("schema_version") != 1
        or result.get("kind")
        != "axeyum-autogenesis-euclidean-bounded-induction-dependency-audit-result"
        or result.get("state")
        != "explicit-direct-dependencies-classified-no-revised-proof-authority"
    ):
        raise BoundedAuditResultError("audit result identity changed")
    if (
        sha256(PLAN) != "942e626f47bb3995e1c8f01181713d853ca2223b1274ec66bb577c87cae01846"
        or sha256(TOOL) != "3e44665e39c231ab3d4acc42d6984e6a881e9274513ff56bb8886a2a0b75a853"
    ):
        raise BoundedAuditResultError("plan or producing tool identity changed")
    if (
        stat.S_IMODE(PACK.stat().st_mode) != 0o555
        or stat.S_IMODE(MANIFEST.stat().st_mode) != 0o444
        or sha256(MANIFEST)
        != "4d86a40127d6f0d9ee15d1b7e651eb0038ae20c69ae30efac6d12763a77c728f"
    ):
        raise BoundedAuditResultError("evidence pack identity or mode changed")
    manifest = load(MANIFEST)
    for key, expected in {
        "audit_result": (
            "audit-result.json",
            "bd839c84c4ec29d2a6a3a0615e14e8c6c32e42d7a949bf9a37930167695e3c07",
            7911,
        ),
        "audit_stderr": (
            "audit.stderr",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            0,
        ),
    }.items():
        row = manifest[key]
        path = PACK / row["path"]
        if (
            row.get("path") != expected[0]
            or row.get("sha256") != expected[1]
            or row.get("bytes") != expected[2]
            or row.get("mode") != "0444"
            or stat.S_IMODE(path.stat().st_mode) != 0o444
            or path.stat().st_size != expected[2]
            or sha256(path) != expected[1]
        ):
            raise BoundedAuditResultError(f"{key} identity or mode changed")
    rows = result["rows"]
    if [row.get("name") for row in rows] != NAMES:
        raise BoundedAuditResultError("dependency population changed")
    carriers = [row["name"] for row in rows if row.get("class") == "propext-bearing"]
    if carriers != ["Nat.div_eq", "Nat.mod_eq"]:
        raise BoundedAuditResultError("propext carrier set changed")
    if result["summary"] != {
        "class_counts": {
            "empty-footprint": 20,
            "other-assumption-bearing": 0,
            "propext-bearing": 2,
        },
        "population": 22,
    }:
        raise BoundedAuditResultError("audit aggregate changed")
    if result["authority"] != {
        "evaluation_credit": 0,
        "exact_target_submissions": 0,
        "executor_invocations": 0,
        "fact_status_changes": 0,
        "importer_runs": 1,
        "ledger_writes": 0,
        "new_authored_theorem_submissions": 0,
        "proof_bearing_stream_reads": 1,
        "proof_terms_rendered": 0,
        "retries": 0,
        "revised_proof_compilations": 0,
        "support_theorem_credit": 0,
        "theorem_values_rendered": 0,
    }:
        raise BoundedAuditResultError("no-proof authority changed")
    return result


def main() -> int:
    try:
        validate()
        print(
            "AUTOGENESIS_EUCLIDEAN_BOUNDED_DEPENDENCY_AUDIT_RESULT_OK|"
            "population=22|empty=20|propext=2|carriers=Nat.div_eq,Nat.mod_eq|"
            "importer_runs=1/1|revised_proofs=0|ledger_writes=0"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        BoundedAuditResultError,
    ) as error:
        print(f"autogenesis-euclidean-bounded-dependency-audit-result: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
