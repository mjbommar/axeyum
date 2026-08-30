#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_gcd."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-construction-result-v1.json"
IDENTITY = ROOT / "artifacts/autogenesis/mathlib-int-fib-gcd-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-gcd-3a8bfdec.json"
CAPSULE = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-fib-gcd-exact-v1/root.ndjson")
MANIFEST = CAPSULE.parent / "manifest.json"
CAPSULE_SHA256 = "040f269431f58c8efe69e995c65b25f64952aa9b3d8f552ab0e7faf2711967f1"
MANIFEST_SHA256 = "f2b4518872594b4eda65dcfb93d1ff2758dcc17c9e64374294aebed05d5d99e9"
DECLARATION_SHA256 = "d269d9ef0763dd923c7825c77c0a3a3dd05ebbe4fbad4d84f3ce93482386a0bf"
GOAL_SHA256 = "c073add7c75a14558f57793924f2bfaac48ff452c9382bfd77727386ba7a464d"
TARGET = "Int.fib_gcd"
DEPENDENCIES = ["Eq.symm", "Eq.trans", "Int.fib_natCast", "Int.gcd_fib"]


class CapsuleError(RuntimeError):
    """The sealed capsule identity or assurance changed."""


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
    theorem = identity["theorem"]
    execution = construction["execution"]
    if (
        byte_digest(CAPSULE) != CAPSULE_SHA256
        or byte_digest(MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or construction.get("state")
        != "exact-int-fib-gcd-constructed-exported-and-twice-reimported-empty-footprint"
        or construction["target"].get("name") != TARGET
        or construction["target"].get("declaration_sha256") != DECLARATION_SHA256
        or construction["target"].get("axiom_footprint") != []
        or construction["target"].get("direct_theorem_dependencies") != DEPENDENCIES
        or identity.get("state") != "exact-goal-identity-bound-without-rendering"
        or theorem.get("name") != TARGET
        or theorem.get("canonical_type_sha256") != GOAL_SHA256
        or theorem.get("canonical_declaration_sha256") != DECLARATION_SHA256
        or theorem.get("axiom_footprint") != []
        or theorem.get("direct_theorem_dependencies") != DEPENDENCIES
        or execution.get("complete_invocations") != 1
        or execution.get("target_theorem_submissions") != 1
        or execution.get("fresh_target_imports") != 2
        or execution.get("retries") != 0
        or execution.get("ledger_writes") != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-int-fib-gcd-3a8bfdec" or not isinstance(statement, str):
        raise CapsuleError("target fact identity changed")
    authority = {
        "fact_id": fact["id"],
        "formal_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
        "result_manifest": IDENTITY.relative_to(ROOT).as_posix(),
        "result_manifest_sha256": byte_digest(IDENTITY),
        "capsule_path": str(CAPSULE),
        "capsule_sha256": CAPSULE_SHA256,
        "target_theorem": TARGET,
        "goal_sha256": GOAL_SHA256,
        "declaration_sha256": DECLARATION_SHA256,
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
        print(f"sealed-int-fib-gcd-capsule: FAIL: {error}")
        return 1
    print(
        f"sealed-int-fib-gcd-capsule: PASS: receipt={receipt['receipt_sha256']} "
        f"target={TARGET} footprint=0 dependencies=4"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
