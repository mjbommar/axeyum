#!/usr/bin/env python3
"""Validate the fixed sealed kernel capsule for Nat.gcd_greatest."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-greatest-result-v3.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-gcd-greatest-0a04214a.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/85b9d4243-target-native-gcd-greatest-v4/target-1.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
RESULT_CHECKER = ROOT / "scripts/check-autogenesis-nat-gcd-greatest-result.py"
EXPECTED_CAPSULE_SHA256 = "c233478948b4d4aedc01c839ef9013c3feb2ddb0009d8b57699d7efb755375e6"
EXPECTED_DECLARATION_SHA256 = "b54b6ab061abba5ea42ca3b0451cd240071b4d535e77bed003d54c78115b03bc"
EXPECTED_GOAL_SHA256 = "0977f9584b62cf5c5140f32ea2d4bf726c9c42aa3cef9f98afdea5d13810af90"
EXPECTED_MANIFEST_SHA256 = "c932d1ec19c35fd0631a5595df6e1abced52d1179ea96812bf426a80c4df7f57"
TARGET = "Nat.gcd_greatest"


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
    result_checker = load_module("gcd_greatest_result_for_capsule", RESULT_CHECKER)
    try:
        result = result_checker.validate()
    except result_checker.ResultError as error:
        raise CapsuleError(f"sealed result failed: {error}") from error
    fact = json.loads(FACT.read_text())
    pack = json.loads(PACK_MANIFEST.read_text())
    theorem = result["target"]
    execution = result["execution"]
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(PACK_MANIFEST) != EXPECTED_MANIFEST_SHA256
        or pack.get("target") != theorem
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or theorem.get("name") != TARGET
        or theorem.get("goal_sha256") != EXPECTED_GOAL_SHA256
        or theorem.get("declaration_sha256") != EXPECTED_DECLARATION_SHA256
        or theorem.get("axiom_footprint") != []
        or execution.get("complete_invocations") != 2
        or execution.get("exact_target_submissions") != 2
        or execution.get("fresh_imports") != 4
        or execution.get("outputs_byte_identical") is not True
        or execution.get("receipts_byte_identical") is not True
        or execution.get("retries") != 0
        or result.get("authority", {}).get("ledger_writes") != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-nat-gcd-greatest-0a04214a" or not isinstance(
        statement, str
    ):
        raise CapsuleError("target fact identity changed")
    authority = {
        "fact_id": fact["id"],
        "formal_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
        "result_manifest": RESULT.relative_to(ROOT).as_posix(),
        "result_manifest_sha256": byte_digest(RESULT),
        "capsule_path": str(CAPSULE),
        "capsule_sha256": EXPECTED_CAPSULE_SHA256,
        "target_theorem": TARGET,
        "goal_sha256": EXPECTED_GOAL_SHA256,
        "declaration_sha256": EXPECTED_DECLARATION_SHA256,
        "axiom_footprint": [],
        "direct_theorem_dependencies": theorem["direct_theorem_dependencies"],
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
        print(f"sealed-gcd-greatest-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-gcd-greatest-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
