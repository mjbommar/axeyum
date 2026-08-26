#!/usr/bin/env python3
"""Check the reusable target-owned bitwise-family capsule receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/bitwise-clean-family-capsule-v1.json"
PROJECTION = ROOT / "artifacts/autogenesis/bitwise-clean-family-projection-v1.json"


def validate(data: dict[str, Any], verify_external: bool) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-bitwise-clean-family-capsule":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "root-selected-export-reimported-axiom-free":
        raise ValueError("capsule state changed")
    authority = data.get("authority", "")
    for denial in (
        "no exact imported-operation identity",
        "no operation registration",
        "no autonomous-production credit",
        "no fact-transition",
    ):
        if denial not in authority:
            raise ValueError(f"authority does not deny {denial}")
    imported = data.get("import", {})
    if imported.get("export_format") != "3.1.0":
        raise ValueError("export format changed")
    if imported.get("lean_githash") != "axeyum-lean-kernel":
        raise ValueError("Axeyum-produced stream is misattributed to Lean")
    if imported.get("axioms") != [] or imported.get("admitted_declarations") != 116:
        raise ValueError("reimport assurance changed")
    roots = data.get("roots")
    if not isinstance(roots, list) or len(roots) != 3:
        raise ValueError("root population changed")
    expected_names = [
        "Axeyum.Autogenesis.testBitBool_bitwiseAnd",
        "Axeyum.Autogenesis.testBitBool_bitwiseOr",
        "Axeyum.Autogenesis.testBitBool_bitwiseDifference",
    ]
    for root, expected_name in zip(roots, expected_names, strict=True):
        if root.get("name") != expected_name:
            raise ValueError("root identity changed")
        if root.get("axiom_footprint") != []:
            raise ValueError("root gained assumptions")
        if root.get("direct_theorem_dependencies") != [
            "Axeyum.Autogenesis.testBitBool_bitwiseTotal"
        ]:
            raise ValueError("root bypassed the generic theorem")
        identity = root.get("declaration_identity")
        if not isinstance(identity, str) or len(identity) != 64:
            raise ValueError("root declaration identity is malformed")
    projection = json.loads(PROJECTION.read_text())
    projected = {row["clean_theorem"] for row in projection["rows"]}
    if {root["name"] for root in roots} != projected:
        raise ValueError("capsule roots disagree with clean family projection")
    stream = data.get("external_stream", {})
    if stream.get("bytes") != 243235 or stream.get("mode") != "0444":
        raise ValueError("external stream receipt changed")
    if verify_external:
        path = Path(stream.get("path", ""))
        raw = path.read_bytes()
        if len(raw) != stream["bytes"]:
            raise ValueError("external stream byte count changed")
        if hashlib.sha256(raw).hexdigest() != stream.get("sha256"):
            raise ValueError("external stream digest changed")
        if path.stat().st_mode & 0o777 != 0o444:
            raise ValueError("external stream is not read-only")
    return {
        "roots": len(roots),
        "axioms": len(imported["axioms"]),
        "admitted_declarations": imported["admitted_declarations"],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--verify-external", action="store_true")
    args = parser.parse_args()
    try:
        counts = validate(json.loads(args.artifact.read_text()), args.verify_external)
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as error:
        print(f"BITWISE_CLEAN_FAMILY_CAPSULE_ERROR|{error}")
        return 1
    print(
        "BITWISE_CLEAN_FAMILY_CAPSULE_OK|"
        f"roots={counts['roots']}|admitted={counts['admitted_declarations']}|"
        f"axioms={counts['axioms']}|external_verified={str(args.verify_external).lower()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
