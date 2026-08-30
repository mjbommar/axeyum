#!/usr/bin/env python3
"""Validate the fixed sealed kernel capsule for Nat.fib_dvd."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-fib-dvd-construction-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-fib-dvd-f80f3de1.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/c2266de88-nat-fib-dvd-v1/target-1.ndjson"
)
OBSERVATION = CAPSULE.parent / "observation-1.json"
INDEX = CAPSULE.parent / "SHA256SUMS"
RESULT_CHECKER = ROOT / "scripts/check-autogenesis-nat-fib-dvd-construction-result.py"
EXPECTED_CAPSULE_SHA256 = "52acbd5a51f2163ab5b712483c582adb916ab198567c2b0b6c3678f7316d86d7"
EXPECTED_OBSERVATION_SHA256 = "073cd9ff661bbc53ef7c565fe0955c6cd41cdc43fb734b5653974207fba0a33d"
EXPECTED_INDEX_SHA256 = "96200c7132319e1f82e62cd98ab14b56b8baec31c9870fc13323751e6b38ab2a"
EXPECTED_DECLARATION_SHA256 = "eef50a6cf5d2d19c80ed894f11d14bbe3521b86982a960e381fff8076be55237"
EXPECTED_GOAL_SHA256 = "defae168bc8fade914418702407acf8fff8f35009596a30a4e468f80852779ac"
TARGET = "Nat.fib_dvd"


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
    result_checker = load_module("fib_dvd_result_for_capsule", RESULT_CHECKER)
    try:
        result = result_checker.validate()
    except RuntimeError as error:
        raise CapsuleError(f"sealed result failed: {error}") from error
    fact = json.loads(FACT.read_text())
    observation = json.loads(OBSERVATION.read_text())
    theorem = result["target"]
    observed_target = dict(theorem)
    observed_target.pop("goal_sha256")
    execution = result["execution"]
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(OBSERVATION) != EXPECTED_OBSERVATION_SHA256
        or byte_digest(INDEX) != EXPECTED_INDEX_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or observation.get("target") != observed_target
        or observation.get("target_goal_sha256") != EXPECTED_GOAL_SHA256
        or theorem.get("name") != TARGET
        or theorem.get("goal_sha256") != EXPECTED_GOAL_SHA256
        or theorem.get("declaration_sha256") != EXPECTED_DECLARATION_SHA256
        or theorem.get("axiom_footprint") != []
        or execution.get("complete_invocations") != 2
        or execution.get("target_theorem_submissions") != 2
        or execution.get("fresh_imports") != 4
        or execution.get("outputs_byte_identical") is not True
        or execution.get("observations_byte_identical") is not True
        or execution.get("retries") != 0
        or execution.get("search_invocations") != 0
        or result.get("authority", {}).get("ledger_writes") != 0
    ):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-nat-fib-dvd-f80f3de1" or not isinstance(
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
        print(f"sealed-fib-dvd-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-fib-dvd-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
