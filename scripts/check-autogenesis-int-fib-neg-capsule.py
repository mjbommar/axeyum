#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_neg."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/int-fib-neg-exact-composition-result-v1.json"
IDENTITY = ROOT / "artifacts/autogenesis/int-fib-neg-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-neg-b4021d37.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-exact-v1/root.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
EXPECTED_CAPSULE_SHA256 = "d787dc502dff901cab0cab22bf8fd11578bf6e1632892651b1bf67b3d786d257"
EXPECTED_PACK_MANIFEST_SHA256 = "c51c34c0804c2e208fa2269f4bb094a99f8d291828fc20ee11d5fa5c38281a35"
EXPECTED_DECLARATION_SHA256 = "55e3a3efbd6e435e5b02ce4382af74763b7be21c1a351cfc5798249f5798feb0"
EXPECTED_GOAL_SHA256 = "08d500fc21c56161f8f8368ff771541c95f7e851b61d23e04361b6a66d7defb0"
TARGET = "Int.fib_neg"
DEPENDENCIES = [
    "Axeyum.Autogenesis.intFibNegFunctionResidualV1",
    "Axeyum.Autogenesis.intFibNegNegativeBranchV1",
    "Axeyum.Autogenesis.intFibNegPositiveBranchV1",
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
    theorem = identity["theorem"]
    execution = construction["execution"]
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(PACK_MANIFEST) != EXPECTED_PACK_MANIFEST_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or construction["state"]
        != "exact-int-fib-neg-specialized-exported-and-reimported-empty-footprint"
        or construction["target"]["name"] != TARGET
        or construction["target"]["declaration_sha256"]
        != EXPECTED_DECLARATION_SHA256
        or construction["target"]["axiom_footprint"] != []
        or construction["target"]["direct_theorem_dependencies"] != DEPENDENCIES
        or theorem["name"] != TARGET
        or theorem["canonical_type_sha256"] != EXPECTED_GOAL_SHA256
        or theorem["canonical_declaration_sha256"]
        != EXPECTED_DECLARATION_SHA256
        or theorem["axiom_footprint"] != []
        or theorem["direct_theorem_dependencies"] != DEPENDENCIES
        or execution["complete_invocations"] != 1
        or execution["exact_target_submissions"] != 1
        or execution["fresh_imports"] != 2
        or execution["retries"] != 0
        or execution["ledger_writes"] != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-int-fib-neg-b4021d37" or not isinstance(
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
        print(f"sealed-int-fib-neg-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-int-fib-neg-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0 dependencies=3"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
