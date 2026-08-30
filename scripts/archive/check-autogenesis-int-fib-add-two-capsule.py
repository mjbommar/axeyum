#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_add_two."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/int-fib-add-two-exact-composition-result-v2.json"
IDENTITY = ROOT / "artifacts/autogenesis/int-fib-add-two-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-add-two-739358dd.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-add-two-exact-composition-v2/int-fib-add-two-1.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
EXPECTED_CAPSULE_SHA256 = "0fbbb4d55ed862f7feb1b8efa3bf45eed24269067b3702c727d05e45c8947219"
EXPECTED_PACK_MANIFEST_SHA256 = "61db55c78dcf18ad9c41d94f7f072e8d2619226b1a3babc21ce6513836b264fe"
EXPECTED_DECLARATION_SHA256 = "cd1612aa68107d4b35b842f4ad2798f07d15256462d49236b8d34ab852de805f"
EXPECTED_GOAL_SHA256 = "acd1e0af4faea9717102d1a977fa510295245969d95f86f64cbfcdacd33f3508"
TARGET = "Int.fib_add_two"
DEPENDENCIES = [
    "Axeyum.Autogenesis.fibAddTwo",
    "Axeyum.IntFib.castAdd",
    "Axeyum.IntFib.evenAdd",
    "Axeyum.IntFib.modCases",
    "Axeyum.IntFib.oddAdd",
    "Axeyum.IntFib.succOne",
    "Axeyum.IntFib.succZero",
    "Int.fib_add_two_residual",
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
        != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
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
        or execution["complete_invocations"] != 2
        or execution["target_submissions"] != 2
        or execution["exports"] != 2
        or execution["fresh_imports"] != 4
        or execution["outputs_byte_identical"] is not True
        or execution["receipts_byte_identical"] is not True
        or execution["retries"] != 0
        or execution["ledger_writes"] != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-int-fib-add-two-739358dd" or not isinstance(
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
        "fresh_imports": 4,
        "fixed_plan_reconstructions": 2,
        "target_theorem_submissions": 2,
        "search_invocations": 0,
        "ledger_writes": 0,
    }
    return {"authority": authority, "receipt_sha256": digest(authority)}


def main() -> int:
    try:
        receipt = validate()
    except (CapsuleError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"sealed-int-fib-add-two-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-int-fib-add-two-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0 dependencies=8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
