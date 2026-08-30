#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.fib_natCast."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-fib-clean-definition-construction-result-v1.json"
IDENTITY = ROOT / "artifacts/autogenesis/mathlib-int-fib-natcast-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-fib-natcast-d5886be4.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/int-fib-clean-definition-v1/int-fib-clean.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
CONSTRUCTION_CHECKER = ROOT / "scripts/check-autogenesis-int-fib-clean-definition-construction-result.py"
IDENTITY_CHECKER = ROOT / "scripts/check-autogenesis-int-fib-natcast-goal-identity-result.py"
EXPECTED_CAPSULE_SHA256 = "f0e34ecb1dff747938b7f1079c307af5f4e79e7a67e3bc514feee03e4f30656d"
EXPECTED_PACK_MANIFEST_SHA256 = "c012c41f66c9ab606094da1fc3ecdfbe218f12e3269f0959657ef455731dcac5"
EXPECTED_DECLARATION_SHA256 = "73b8742709bbb1b91780f41ff4a475b5b3f0b1c2981999c868b53fc38334bea3"
EXPECTED_GOAL_SHA256 = "3a173a7b65ddf0fcf8c30c4ea3511780667bfff311a531ec477515ea731c490b"
TARGET = "Int.fib_natCast"


class CapsuleError(RuntimeError):
    """The sealed capsule contract is inconsistent."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise CapsuleError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate() -> dict[str, Any]:
    construction_checker = load_module("int_fib_construction_for_capsule", CONSTRUCTION_CHECKER)
    identity_checker = load_module("int_fib_identity_for_capsule", IDENTITY_CHECKER)
    if construction_checker.main() != 0 or identity_checker.main() != 0:
        raise CapsuleError("construction or identity evidence failed")
    construction = json.loads(CONSTRUCTION.read_text())
    identity = json.loads(IDENTITY.read_text())
    fact = json.loads(FACT.read_text())
    theorem = identity["theorem"]
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(PACK_MANIFEST) != EXPECTED_PACK_MANIFEST_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or theorem["name"] != TARGET
        or theorem["canonical_type_sha256"] != EXPECTED_GOAL_SHA256
        or theorem["canonical_declaration_sha256"] != EXPECTED_DECLARATION_SHA256
        or theorem["axiom_footprint"] != []
        or theorem["direct_theorem_dependencies"] != []
        or construction["execution"]["importer_runs"] != 2
        or construction["execution"]["byte_identical_observations"] is not True
        or construction["execution"]["theorem_submissions"] != 1
        or construction["execution"]["retries"] != 0
        or construction["authority"]["ledger_writes"] != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-int-fib-natcast-d5886be4" or not isinstance(
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
        "direct_theorem_dependencies": [],
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
        print(f"sealed-int-fib-natcast-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-int-fib-natcast-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
