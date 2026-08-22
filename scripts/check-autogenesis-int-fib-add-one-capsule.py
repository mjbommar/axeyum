#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_add_one."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-one-composition-result-v1.json"
IDENTITY = ROOT / "artifacts/autogenesis/mathlib-int-fib-add-one-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-add-one-33f1b748.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-add-one-composition-v1/int-fib-add-one.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
EXPECTED_CAPSULE_SHA256 = "81fb760e78ee25d12fa7b78f8e2d84892809a36db8a4f8d9cc63fda6be66f27c"
EXPECTED_PACK_MANIFEST_SHA256 = "968e330b4fdb88b57170e84e5650a676c9dd61a3bc79a7b87e2fed2e468d74fa"
EXPECTED_DECLARATION_SHA256 = "2ee4a2c5dbea36f73b7fea51b74d134e75630e3f860c033720a7e679cabfb5a7"
EXPECTED_GOAL_SHA256 = "b9c99a22010f3a1e749e9647604da9107259f8ed6bd3010a2520778efcff41c6"
TARGET = "Int.fib_add_one"
DEPENDENCIES = [
    "Axeyum.Autogenesis.intFibAddOneResidualV3",
    "Int.add_comm",
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
    if fact.get("id") != "F:ml430-int-fib-add-one-33f1b748" or not isinstance(
        statement, str
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
        print(f"sealed-int-fib-add-one-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-int-fib-add-one-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0 dependencies=4"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
