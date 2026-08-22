#!/usr/bin/env python3
"""Validate the sealed kernel capsule for the exact Int Fibonacci corollary."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-corollary-composition-result-v3.json"
IDENTITY = ROOT / "artifacts/autogenesis/mathlib-int-fib-recurrence-corollary-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-recurrence-corollary-composition-v3/int-fib-recurrence-corollary-1.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "SHA256SUMS"
EXPECTED_CAPSULE_SHA256 = "d8823373479dce23213aa004b58e9e0c8912fd413b2cb29e52195639f57a7987"
EXPECTED_PACK_MANIFEST_SHA256 = "18074e2cae1315e349e83beee8b937d853415a6eb4cb7c264f95d5ca5eefcb99"
EXPECTED_DECLARATION_SHA256 = "095a25341329591091b618d64fbc2f249ed3d33337bf06e499d0c9a10f436a93"
EXPECTED_GOAL_SHA256 = "2295addae4552672b3f69a9a489c9173deddc7e68c74cfa12429490fffc825ad"
TARGET = "Int.fib_eq_fib_add_two_sub_fib_add_one"
DEPENDENCIES = [
    "Axeyum.Autogenesis.intFibEqAddTwoSubAddOneResidualV2",
    "Int.add_neg_cancel_right",
    "Int.fib_add_two",
]


class CapsuleError(RuntimeError):
    """The sealed capsule contract is inconsistent."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict[str, Any]:
    construction = json.loads(CONSTRUCTION.read_text())
    identity = json.loads(IDENTITY.read_text())
    fact = json.loads(FACT.read_text())
    target = construction.get("target") or {}
    theorem = identity.get("theorem") or {}
    execution = construction.get("execution") or {}
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(PACK_MANIFEST) != EXPECTED_PACK_MANIFEST_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or construction.get("state")
        != "exact-target-specialized-exported-and-reimported-empty-footprint"
        or target.get("name") != TARGET
        or target.get("declaration_sha256") != EXPECTED_DECLARATION_SHA256
        or target.get("axiom_footprint") != []
        or target.get("direct_theorem_dependencies") != DEPENDENCIES
        or theorem.get("name") != TARGET
        or theorem.get("canonical_type_sha256") != EXPECTED_GOAL_SHA256
        or theorem.get("canonical_declaration_sha256")
        != EXPECTED_DECLARATION_SHA256
        or theorem.get("axiom_footprint") != []
        or theorem.get("direct_theorem_dependencies") != DEPENDENCIES
        or execution.get("complete_invocations") != 1
        or execution.get("target_submissions") != 1
        or execution.get("exports") != 1
        or execution.get("fresh_imports") != 2
        or execution.get("retries") != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if (
        fact.get("id")
        != "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d"
        or not isinstance(statement, str)
    ):
        raise CapsuleError("target fact identity changed")
    authority = {
        "fact_id": fact["id"],
        "formal_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
        "result_manifest": IDENTITY.relative_to(ROOT).as_posix(),
        "result_manifest_sha256": byte_digest(IDENTITY),
        "capsule_path": str(CAPSULE),
        "capsule_sha256": EXPECTED_CAPSULE_SHA256,
        "target_theorem": TARGET,
        "goal_sha256": EXPECTED_GOAL_SHA256,
        "declaration_sha256": EXPECTED_DECLARATION_SHA256,
        "axiom_footprint": [],
        "direct_theorem_dependencies": DEPENDENCIES,
        "fresh_imports": 2,
        "fixed_plan_reconstructions": 1,
        "target_theorem_submissions": 1,
        "search_invocations": 0,
        "ledger_writes": 0,
    }
    return {"authority": authority, "receipt_sha256": digest(authority)}


def main() -> int:
    try:
        receipt = validate()
    except (CapsuleError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"sealed-int-fib-recurrence-corollary-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-int-fib-recurrence-corollary-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0 dependencies=3"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
