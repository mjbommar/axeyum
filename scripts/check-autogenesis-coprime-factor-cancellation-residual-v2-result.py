#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-residual-v2-result-v1.json"

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "three-residual-roots-reconstructed-twice-empty-footprint"
    assert digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
    assert digest(ROOT / result["source"]["path"]) == result["source"]["sha256"]
    pack = Path(result["evidence"]["pack"])
    assert digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"]
    assert digest(pack / "residual-v2.ndjson") == result["evidence"]["stream_sha256"]
    assert digest(pack / "audit-1.json") == result["evidence"]["audit_sha256"] == digest(pack / "audit-2.json")
    assert len(result["theorems"]) == 3 and all(row["axiom_footprint"] == [] for row in result["theorems"])
    assert result["explicit_parameters"] == ["balancedBezout", "mulAssoc", "rightDistrib", "dvdAddCancel"]
    assert result["authority"]["support_leaf_credit"] == 2 and result["authority"]["residual_cancellation_credit"] == 1
    assert all(value == 0 for key, value in result["authority"].items() if key not in {"support_leaf_credit", "residual_cancellation_credit"})
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_RESIDUAL_V2_RESULT_OK|roots=3|footprints=0|parameters=4|official=0")

if __name__ == "__main__":
    main()
