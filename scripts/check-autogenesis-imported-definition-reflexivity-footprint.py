#!/usr/bin/env python3
"""Validate the imported-definition reflexivity footprint receipt."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/imported-definition-reflexivity-footprint-v1.json"
DEMAND = ROOT / "artifacts/autogenesis/bitwise-semantic-law-demand-v1.json"


def validate(data: dict[str, Any]) -> dict[str, int]:
    if data.get("kind") != "axeyum-imported-definition-reflexivity-footprint":
        raise ValueError("wrong artifact kind")
    authority = data.get("authority", "")
    for denial in ("no proof transport", "no theorem admission", "no fact-transition"):
        if denial not in authority:
            raise ValueError(f"authority does not deny {denial}")
    if data.get("lean_version") != "4.30.0" or data.get("lean_githash") != (
        "d024af099ca4bf2c86f649261ebf59565dc8c622"
    ):
        raise ValueError("source authority changed")
    if data.get("source_stream_sha256") != (
        "58c09fb4f8b3af7adacd8d0c22e945507e6ffb3920b0581c22d17afa1867d3b9"
    ):
        raise ValueError("source stream identity changed")

    demand = json.loads(DEMAND.read_text())
    operations = {row["name"]: row for row in demand["operations"]}
    controls = data.get("controls")
    if not isinstance(controls, list) or len(controls) != 2:
        raise ValueError("control population changed")
    expected = [
        ("Axeyum.Autogenesis.ImportedTestBitReflexivityProbe", "Nat.testBit"),
        ("Axeyum.Autogenesis.ImportedBitwiseReflexivityProbe", "Nat.bitwise"),
    ]
    for control, (control_name, operation_name) in zip(controls, expected, strict=True):
        if control.get("name") != control_name:
            raise ValueError("control identity changed")
        if control.get("axiom_footprint") != ["propext"]:
            raise ValueError("reflexivity footprint changed")
        if control.get("direct_theorem_dependencies") != []:
            raise ValueError("reflexivity control gained theorem dependencies")
        dependencies = control.get("direct_declaration_dependencies")
        if not isinstance(dependencies, list) or dependencies != sorted(dependencies):
            raise ValueError("control dependencies are not deterministic")
        if operation_name not in dependencies:
            raise ValueError("control no longer mentions its imported operation")
        if operations.get(operation_name, {}).get("axiom_footprint") != ["propext"]:
            raise ValueError("demand operation footprint disagrees with probe")
        rendered_type = control.get("type", "")
        if "Eq.{1}" not in rendered_type or operation_name.split(".")[-1] not in rendered_type:
            raise ValueError("control type changed")

    if "cannot have an empty declaration-reached footprint" not in data.get(
        "consequence", ""
    ):
        raise ValueError("measured consequence weakened")
    return {"controls": len(controls), "theorem_dependencies": 0, "propext_controls": 2}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    try:
        counts = validate(json.loads(args.artifact.read_text()))
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as error:
        print(f"imported-definition-reflexivity-footprint: FAIL: {error}")
        return 1
    print(
        "imported-definition-reflexivity-footprint: "
        f"PASS ({counts['controls']} controls, {counts['propext_controls']} inherit propext, "
        f"{counts['theorem_dependencies']} theorem dependencies)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
