#!/usr/bin/env python3
"""Verify the residual cancellation result and its narrow credit."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-residual-result-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "residual-reconstructed-twice-dvd-mul-witness-propext"
    assert digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
    assert digest(ROOT / result["source"]["path"]) == result["source"]["sha256"]
    pack = Path(result["evidence"]["pack"])
    assert digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"]
    assert digest(pack / "residual.ndjson") == result["evidence"]["stream_sha256"]
    assert digest(pack / "audit-1.json") == result["evidence"]["audit_sha256"] == digest(pack / "audit-2.json")
    assert result["classification"]["clean_roots"] == ["Axeyum.Autogenesis.dvdAddWitnessV1"]
    assert result["classification"]["propext_roots"] == ["Axeyum.Autogenesis.dvdMulRightWitnessV1", "Axeyum.Autogenesis.coprimeFactorDivisibilityCancellationResidualV1"]
    assert result["authority"]["support_leaf_credit"] == 1
    assert all(value == 0 for key, value in result["authority"].items() if key != "support_leaf_credit")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_RESIDUAL_RESULT_OK|clean=1|propext=2|residual_credit=0")


if __name__ == "__main__":
    main()
