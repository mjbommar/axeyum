#!/usr/bin/env python3
"""Check the exact imported Nat.testBit_bitwise candidate audit."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/imported-testbit-bitwise-candidate-v1.json"


def validate(data: dict[str, Any], verify_external: bool) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-imported-candidate-audit":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "independently-imported-assumption-bearing-candidate":
        raise ValueError("candidate state is not fail-closed")
    authority = data.get("authority", "")
    for denied in ("no semantic contract", "no transport", "no fact-transition"):
        if denied not in authority:
            raise ValueError(f"authority does not deny {denied}")
    candidate = data.get("candidate", {})
    if candidate.get("name") != "Nat.testBit_bitwise":
        raise ValueError("wrong candidate declaration")
    for field in (
        "type_expression_sha256",
        "alpha_type_expression_sha256",
        "declaration_content_sha256",
        "direct_dependency_sha256",
    ):
        value = candidate.get(field)
        if not isinstance(value, str) or len(value) != 64:
            raise ValueError(f"candidate {field} is malformed")
    canonical_type = candidate.get("canonical_type", "")
    if "AxNat.testBit (AxNat.bitwise f x y)" not in canonical_type:
        raise ValueError("candidate canonical type lost the generic bitwise observation")
    kernel = data.get("kernel_import", {})
    if kernel.get("axiom_free") is not False:
        raise ValueError("candidate must not be represented as axiom-free")
    expected_footprint = ["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"]
    if kernel.get("axiom_footprint") != expected_footprint:
        raise ValueError("reviewed axiom footprint changed")
    if kernel.get("imported_axioms") != ["Quot.sound", "propext"]:
        raise ValueError("reviewed imported axiom set changed")
    dependencies = candidate.get("direct_theorem_dependencies")
    if not isinstance(dependencies, list) or dependencies != sorted(dependencies):
        raise ValueError("direct theorem dependencies are absent or unstable")
    if len(dependencies) != 29:
        raise ValueError("reviewed direct theorem dependency count changed")
    stream = data.get("external_stream", {})
    if verify_external:
        path = Path(stream.get("path", ""))
        raw = path.read_bytes()
        if len(raw) != stream.get("bytes"):
            raise ValueError("external stream byte count changed")
        if hashlib.sha256(raw).hexdigest() != stream.get("sha256"):
            raise ValueError("external stream digest changed")
    return {
        "direct_theorem_dependencies": len(dependencies),
        "axiom_footprint": len(expected_footprint),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--verify-external", action="store_true")
    args = parser.parse_args()
    try:
        census = validate(json.loads(args.artifact.read_text()), args.verify_external)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"IMPORTED_TESTBIT_BITWISE_CANDIDATE_ERROR|{error}")
        return 1
    print(
        "IMPORTED_TESTBIT_BITWISE_CANDIDATE_OK|"
        f"direct_theorems={census['direct_theorem_dependencies']}|"
        f"footprint={census['axiom_footprint']}|axiom_free=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
