#!/usr/bin/env python3
"""Verify the exact cancellation dependency classification."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-dependency-audit-result-v1.json"
EXPECTED = ["Nat.dvd_add", "Nat.dvd_add_iff_right", "Nat.dvd_mul_right_of_dvd", "Nat.mul_left_comm", "Nat.right_distrib", "eq_self"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "seventeen-roots-classified-six-propext-carriers"
    assert digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
    pack = Path(result["evidence"]["pack"])
    assert digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"]
    assert digest(pack / "audit.json") == result["evidence"]["audit_sha256"]
    assert result["execution"] == {"importer_runs": 1, "proof_bearing_stream_reads": 1, "theorem_submissions": 0, "retries": 0}
    assert result["classification"] == {"population": 17, "empty_footprint": 11, "propext_bearing": 6, "propext_roots": EXPECTED}
    assert result["rendered_material"] == {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
    assert result["authority"]["dependency_audit_credit"] == 1
    assert all(value == 0 for key, value in result["authority"].items() if key != "dependency_audit_credit")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_DEPENDENCY_AUDIT_RESULT_OK|roots=17|clean=11|propext=6|theorem_credit=0")


if __name__ == "__main__":
    main()
