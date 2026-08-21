#!/usr/bin/env python3
"""Verify the sealed target-native Nat.gcd_greatest result."""

from __future__ import annotations

import hashlib
import json
import pathlib
import stat
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-nat-gcd-greatest-result-v3.json"


class ResultError(RuntimeError):
    """The result, immutable pack, or theorem assurance changed."""


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ResultError(f"{path} is not an object")
    return value


def sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(result: dict[str, Any] | None = None) -> dict[str, Any]:
    result = load(RESULT) if result is None else result
    if (
        result.get("kind")
        != "axeyum-autogenesis-mathlib-nat-gcd-greatest-result-v3"
        or result.get("state")
        != "exact-target-reconstructed-twice-byte-identical-empty-footprint"
    ):
        raise ResultError("result identity changed")
    plan = result["plan"]
    if sha256(ROOT / plan["path"]) != plan["sha256"]:
        raise ResultError("plan identity changed")
    pack = pathlib.Path(result["evidence_pack"]["path"])
    manifest = load(pack / "manifest.json")
    target = result["target"]
    if (
        sha256(pack / "manifest.json")
        != result["evidence_pack"]["manifest_sha256"]
        or sha256(pack / "SHA256SUMS") != result["evidence_pack"]["index_sha256"]
        or stat.S_IMODE(pack.stat().st_mode) != 0o555
        or any(stat.S_IMODE(path.stat().st_mode) != 0o444 for path in pack.iterdir())
        or sha256(pack / "target-1.ndjson") != result["capsule"]["sha256"]
        or sha256(pack / "target-2.ndjson") != result["capsule"]["sha256"]
        or (pack / "target-1.ndjson").stat().st_size != result["capsule"]["bytes"]
        or manifest.get("target") != target
    ):
        raise ResultError("immutable evidence pack or target identity changed")
    if target != {
        "name": "Nat.gcd_greatest",
        "goal_sha256": "0977f9584b62cf5c5140f32ea2d4bf726c9c42aa3cef9f98afdea5d13810af90",
        "declaration_sha256": "b54b6ab061abba5ea42ca3b0451cd240071b4d535e77bed003d54c78115b03bc",
        "axiom_footprint": [],
        "direct_theorem_dependencies": [
            "Axeyum.Autogenesis.dvdAntisymmOfficialV1",
            "Axeyum.Autogenesis.dvdGcdOfficialV1",
            "Axeyum.Autogenesis.gcdDvdLeftOfficialV1",
            "Axeyum.Autogenesis.gcdDvdRightOfficialV1",
        ],
    }:
        raise ResultError("target theorem contract changed")
    if result["execution"] != {
        "driver_builds": 1,
        "complete_invocations": 2,
        "composition_receipts": 2,
        "exact_target_submissions": 2,
        "exports": 2,
        "fresh_imports": 4,
        "outputs_byte_identical": True,
        "receipts_byte_identical": True,
        "retries": 0,
        "search_invocations": 0,
    } or result["authority"] != {
        "target_credit": 1,
        "fact_status_changes": 0,
        "evaluation_credit": 0,
        "ledger_writes": 0,
    }:
        raise ResultError("execution or authority boundary changed")
    return result


def main() -> int:
    try:
        result = validate()
    except (OSError, ValueError, KeyError, TypeError, ResultError) as error:
        print(f"AUTOGENESIS_NAT_GCD_GREATEST_RESULT_ERROR|{error}", file=sys.stderr)
        return 1
    print(
        "AUTOGENESIS_NAT_GCD_GREATEST_RESULT_OK|target=Nat.gcd_greatest|"
        f"goal={result['target']['goal_sha256']}|footprint=0|"
        "invocations=2|imports=4|ledger_writes=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
