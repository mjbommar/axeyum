#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-dvd-mul-dependency-audit-result-v1.json"

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "Nat-mul-assoc-is-direct-propext-carrier"
    assert digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
    pack = Path(result["evidence"]["pack"])
    assert digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"]
    assert digest(pack / "audit.json") == result["evidence"]["audit_sha256"]
    assert result["classification"] == {"clean_roots": ["Eq.trans", "congrArg"], "propext_root": "Nat.mul_assoc", "propext_root_declaration_sha256": "9cc915af2d8f3e3f41c767a1f5fa28dd61bc5dc97015abb764535e64d5c55295", "propext_root_direct_theorem_dependencies": []}
    assert result["authority"]["dependency_audit_credit"] == 1
    assert all(value == 0 for key, value in result["authority"].items() if key != "dependency_audit_credit")
    print("AUTOGENESIS_COPRIME_FACTOR_DVD_MUL_DEPENDENCY_AUDIT_RESULT_OK|clean=2|carrier=Nat.mul_assoc|theorem_credit=0")

if __name__ == "__main__":
    main()
