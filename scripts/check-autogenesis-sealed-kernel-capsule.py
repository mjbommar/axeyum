#!/usr/bin/env python3
"""Validate the fixed sealed kernel capsule for Nat.gcd_fib_add_self."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/nat-gcd-fib-add-self-target-native-exact-result-v3.json"
FACT = ROOT / "artifacts/facts/F-ml430-nat-gcd-fib-add-self-5a92d5e3.json"
CAPSULE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/reference-packs/dfa79618c-target-native-exact-v3/target-1.ndjson"
)
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
EXPECTED_CAPSULE_SHA256 = "279dc4db5daa6dc2f532f9876052500a7e278c54264b32ccbc9d4256907dfc24"
EXPECTED_DECLARATION_SHA256 = "2d61bf57db3bc182300f1cc1317269eb68e94b5a05a1f0ed4e501f3049303e37"
EXPECTED_GOAL_SHA256 = "0ac365e0654218862f44cc19391e699b85e495ab1b9608fc3eca79585c0e0475"
EXPECTED_MANIFEST_SHA256 = "4c631e0e126fa98d0c8cc5231ac9d06cd857028eacadb8a78897f9845f42819f"
TARGET = "Nat.gcd_fib_add_self"


class CapsuleError(RuntimeError):
    """The sealed capsule contract is inconsistent."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate() -> dict[str, Any]:
    result = json.loads(RESULT.read_text())
    fact = json.loads(FACT.read_text())
    pack = json.loads(PACK_MANIFEST.read_text())
    theorem = result.get("target") or {}
    execution = result.get("execution") or {}
    if (
        result.get("kind")
        != "axeyum-autogenesis-nat-gcd-fib-add-self-target-native-exact-result-v3"
        or result.get("state")
        != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
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
        or result.get("authority", {}).get("fact_status_changes") != 0
        or result.get("authority", {}).get("ledger_writes") != 0
    ):
        raise CapsuleError("committed exact-target result contract changed")
    if (
        byte_digest(CAPSULE) != EXPECTED_CAPSULE_SHA256
        or byte_digest(PACK_MANIFEST) != EXPECTED_MANIFEST_SHA256
        or pack.get("target", {}).get("name") != TARGET
        or pack.get("target", {}).get("declaration_sha256")
        != EXPECTED_DECLARATION_SHA256
        or pack.get("target", {}).get("axiom_footprint") != []
        or pack.get("acceptance", {}).get("fresh_imports") != 4
        or pack.get("acceptance", {}).get("all_axiom_footprints_empty") is not True
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444
        or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
    ):
        raise CapsuleError("external capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-nat-gcd-fib-add-self-5a92d5e3" or not isinstance(
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
    except (CapsuleError, OSError, ValueError, KeyError) as error:
        print(f"sealed-kernel-capsule: FAIL: {error}")
        return 1
    print(
        "sealed-kernel-capsule: PASS: "
        f"receipt={receipt['receipt_sha256']} target={TARGET} footprint=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
