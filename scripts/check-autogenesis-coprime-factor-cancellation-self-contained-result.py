#!/usr/bin/env python3
"""Verify the deterministic but propext-bearing cancellation result."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-self-contained-result-v1.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value: bool, message: str) -> None:
    if not value:
        raise SystemExit(message)


def main() -> None:
    result = json.loads(RESULT.read_text())
    require(result["state"] == "reconstructed-twice-propext-bearing-no-credit", "state changed")
    require(digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"], "plan changed")
    require(digest(ROOT / result["source"]["path"]) == result["source"]["sha256"], "source changed")
    pack = Path(result["evidence"]["pack"])
    require(digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"], "manifest changed")
    require(digest(pack / "cancellation-generic.ndjson") == result["evidence"]["stream_sha256"], "stream changed")
    require(digest(pack / "audit-1.json") == result["evidence"]["audit_sha256"] and digest(pack / "audit-2.json") == result["evidence"]["audit_sha256"], "audits differ")
    theorem = result["theorem"]
    require(theorem["axiom_footprint"] == ["propext"], "measured footprint changed")
    require(theorem["fresh_reconstructions"] == 2 and theorem["audits_byte_identical"] is True, "replay changed")
    require(theorem["rendered_material"] == {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}, "proof material rendered")
    require(result["execution"]["retries"] == 0 and result["execution"]["proof_bearing_stream_reads"] == 2, "execution changed")
    require(all(value == 0 for value in result["authority"].values()), "declined theorem grants authority")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_SELF_CONTAINED_RESULT_OK|imports=2|footprint=propext|credit=0")


if __name__ == "__main__":
    main()
