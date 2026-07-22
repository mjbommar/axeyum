#!/usr/bin/env python3
"""Render the frozen current-product outcomes after the Stage B commit."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-official-construct-matrix-v1.json"

PRODUCT = {
    "measured_date": "2026-07-22",
    "source_revision": "22f51b4b0a94a1ae4d1c18b3f0dee6f56005edf4",
    "crate": "axeyum-lean-import",
    "example": "lean4export_import",
    "memory_max": "4G",
    "rust_jobs": 2,
    "runs_per_case": 2,
    "control_before_each_run": True,
    "control_runs": 10,
    "control": {
        "id": "direct-recursive-control",
        "all_passed": True,
        "names": 30,
        "levels": 4,
        "expressions": 130,
        "declaration_records": 5,
        "admitted_declarations": 11,
        "axioms": 0,
        "axiom_identities": 0,
        "declaration_identities": 11,
    },
    "outcomes": {
        "recursive-indexed": {
            "runs": 2,
            "repeatable": True,
            "outcome_layer": "kernel",
            "variant": "Kernel",
            "line": 148,
            "declaration": "AxeyumConstructMatrix.MiniVector",
            "source_variant": "RecursiveIndexedNotSupported",
            "code": None,
            "message": None,
            "completed_import_published": False,
        },
        "reflexive-higher-order": {
            "runs": 2,
            "repeatable": True,
            "outcome_layer": "import-policy",
            "variant": "Unsupported",
            "line": 117,
            "declaration": None,
            "source_variant": None,
            "code": "inductive-reflexive",
            "message": None,
            "completed_import_published": False,
        },
        "mutual": {
            "runs": 2,
            "repeatable": True,
            "outcome_layer": "import-policy",
            "variant": "Unsupported",
            "line": 233,
            "declaration": None,
            "source_variant": None,
            "code": "inductive-mutual",
            "message": None,
            "completed_import_published": False,
        },
        "nested": {
            "runs": 2,
            "repeatable": True,
            "outcome_layer": "format-misclassification",
            "variant": "Malformed",
            "line": 248,
            "declaration": None,
            "source_variant": None,
            "code": None,
            "message": "single-family inductive must export one recursor",
            "completed_import_published": False,
        },
        "well-founded": {
            "runs": 2,
            "repeatable": True,
            "outcome_layer": "import-policy",
            "variant": "Unsupported",
            "line": 208,
            "declaration": None,
            "source_variant": None,
            "code": "inductive-reflexive",
            "message": None,
            "completed_import_published": False,
        },
    },
}


def render() -> str:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("stage") == "product-measured":
        data["stage"] = "wire-frozen"
        data["product_measurement"] = None
        for case in data["cases"]:
            case["product_measurement"] = None
    if data.get("stage") != "wire-frozen" or data.get("stage_b") is None:
        raise ValueError("input registration must contain the committed Stage B wire freeze")
    if data.get("product_measurement") is not None:
        raise ValueError("input registration already contains unrecognized product observations")

    data["stage"] = "product-measured"
    data["product_measurement"] = PRODUCT
    for case in data["cases"]:
        case_id = case["id"]
        if case_id == "non-positive-source-negative":
            case["product_measurement"] = None
        else:
            case["product_measurement"] = case_id
    return json.dumps(data, indent=2, sort_keys=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="require committed bytes to match")
    args = parser.parse_args()
    try:
        rendered = render()
    except (OSError, ValueError) as error:
        print(f"lean construct matrix product freeze: {error}", file=sys.stderr)
        return 1
    if args.check:
        if MANIFEST.read_text(encoding="utf-8") != rendered:
            print("lean construct matrix product freeze: committed registration drift", file=sys.stderr)
            return 1
        print("lean construct matrix product freeze: committed registration matches typed outcomes")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
