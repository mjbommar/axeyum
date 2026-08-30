#!/usr/bin/env python3
"""Validate the sealed kernel capsule for exact Int.gcd_fib."""

from __future__ import annotations
import hashlib, json, pathlib, stat
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CONSTRUCTION = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v13.json"
IDENTITY = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-goal-identity-result-v1.json"
FACT = ROOT / "artifacts/facts/F-ml430-int-gcd-fib-73bdafc2.json"
CAPSULE = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1/root.ndjson")
PACK_MANIFEST = CAPSULE.parent / "manifest.json"
CAPSULE_SHA256 = "b1ce136473ead161243e7cdc053f3a8e0dab81a8e253c364171e839f22fd86f6"
MANIFEST_SHA256 = "1b68af399609794120540cd13857daaaad090148ce90299c5582e0d74186a561"
DECLARATION_SHA256 = "44660dc7f15cda1b469f99e349f4b874afca9dbca24bcfc5c847ca226ccc357f"
GOAL_SHA256 = "050ddb31135f25341d15c5a8a0802512b11a3965983c5a1a21aaabf9a7bb901b"
TARGET = "Int.gcd_fib"
DEPENDENCIES = ["Axeyum.Autogenesis.intFibNatAbsV1", "Eq.symm", "Eq.trans", "Int.gcd_def", "Nat.fib_gcd"]

class CapsuleError(RuntimeError): pass
def canonical_json(value: Any) -> str: return json.dumps(value, sort_keys=True, separators=(",", ":"))
def digest(value: Any) -> str: return hashlib.sha256(canonical_json(value).encode()).hexdigest()
def byte_digest(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()

def validate() -> dict[str, Any]:
    construction, identity, fact = json.loads(CONSTRUCTION.read_text()), json.loads(IDENTITY.read_text()), json.loads(FACT.read_text())
    theorem, execution = identity["theorem"], construction["execution"]
    if (byte_digest(CAPSULE) != CAPSULE_SHA256 or byte_digest(PACK_MANIFEST) != MANIFEST_SHA256
        or stat.S_IMODE(CAPSULE.stat().st_mode) != 0o444 or stat.S_IMODE(CAPSULE.parent.stat().st_mode) != 0o555
        or construction.get("state") != "exact-int-gcd-fib-constructed-exported-and-twice-reimported-empty-footprint"
        or construction["target"].get("name") != TARGET or construction["target"].get("declaration_sha256") != DECLARATION_SHA256
        or construction["target"].get("axiom_footprint") != [] or construction["target"].get("direct_theorem_dependencies") != DEPENDENCIES
        or identity.get("state") != "exact-goal-identity-bound-without-rendering" or theorem.get("name") != TARGET
        or theorem.get("canonical_type_sha256") != GOAL_SHA256 or theorem.get("canonical_declaration_sha256") != DECLARATION_SHA256
        or theorem.get("axiom_footprint") != [] or theorem.get("direct_theorem_dependencies") != DEPENDENCIES
        or execution.get("complete_invocations") != 1 or execution.get("target_theorem_submissions") != 1
        or execution.get("fresh_target_imports") != 2 or execution.get("retries") != 0 or execution.get("ledger_writes") != 0):
        raise CapsuleError("capsule identity, assurance, or immutability changed")
    statement = (fact.get("formal") or {}).get("statement")
    if fact.get("id") != "F:ml430-int-gcd-fib-73bdafc2" or not isinstance(statement, str): raise CapsuleError("target fact identity changed")
    authority = {"fact_id": fact["id"], "formal_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
        "result_manifest": IDENTITY.relative_to(ROOT).as_posix(), "result_manifest_sha256": byte_digest(IDENTITY),
        "capsule_path": str(CAPSULE), "capsule_sha256": CAPSULE_SHA256, "target_theorem": TARGET,
        "goal_sha256": GOAL_SHA256, "declaration_sha256": DECLARATION_SHA256, "axiom_footprint": [],
        "direct_theorem_dependencies": DEPENDENCIES, "fresh_imports": 2, "fixed_plan_reconstructions": 1,
        "target_theorem_submissions": 1, "search_invocations": 0, "ledger_writes": 0}
    return {"authority": authority, "receipt_sha256": digest(authority)}

def main() -> int:
    try: receipt = validate()
    except (CapsuleError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"sealed-int-gcd-fib-capsule: FAIL: {error}"); return 1
    print(f"sealed-int-gcd-fib-capsule: PASS: receipt={receipt['receipt_sha256']} target={TARGET} footprint=0 dependencies=5"); return 0

if __name__ == "__main__": raise SystemExit(main())
