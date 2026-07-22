#!/usr/bin/env python3
"""Render the Stage B construct-matrix registration from frozen official bytes."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

from prototype_lean4export_census import census_bytes  # noqa: E402


MANIFEST = ROOT / "docs" / "plan" / "lean-official-construct-matrix-v1.json"
STREAMS = (
    (
        "recursive-indexed",
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-recursive-indexed.ndjson",
        "AxeyumConstructMatrix.recursiveIndexedWitness",
        (705040, 709160),
    ),
    (
        "reflexive-higher-order",
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson",
        "AxeyumConstructMatrix.reflexiveWitness",
        (716880, 714148),
    ),
    (
        "mutual",
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson",
        "AxeyumConstructMatrix.mutualWitness",
        (716420, 716864),
    ),
    (
        "nested",
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-nested.ndjson",
        "AxeyumConstructMatrix.nestedWitness",
        (716440, 716976),
    ),
    (
        "well-founded",
        "docs/plan/fixtures/lean4export-v4.30-construct-matrix-well-founded.ndjson",
        "AxeyumConstructMatrix.wellFoundedWitness",
        (715320, 714960),
    ),
)


def render() -> str:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("product_measurement") is not None:
        raise ValueError("input registration already contains product observations")
    if data.get("stage") == "wire-frozen":
        data["stage"] = "source-frozen"
        data["stage_b"] = None
        for case in data["cases"]:
            case["stage_b_wire"] = None
    if data.get("stage") != "source-frozen" or data.get("stage_b") is not None:
        raise ValueError("input registration is neither the Stage A nor Stage B freeze")

    streams: dict[str, object] = {}
    total_bytes = 0
    for case_id, relative_path, selected_root, max_rss_kib in STREAMS:
        path = ROOT / relative_path
        inventory = census_bytes(path.read_bytes(), label=case_id)
        declaration_names = inventory["declaration_names"]
        if not isinstance(declaration_names, tuple) or not declaration_names:
            raise ValueError(f"{case_id}: independent inventory returned no declarations")
        if declaration_names[-1] != selected_root:
            raise ValueError(
                f"{case_id}: final declaration {declaration_names[-1]!r} "
                f"does not match selected root {selected_root!r}"
            )
        total_bytes += int(inventory["bytes"])
        streams[case_id] = {
            "path": relative_path,
            "selected_root": selected_root,
            "export_runs": 2,
            "byte_identical": True,
            "max_rss_kib": list(max_rss_kib),
            "retained": True,
            "inventory": inventory,
        }

    data["stage"] = "wire-frozen"
    data["stage_b"] = {
        "frozen_date": "2026-07-22",
        "independent_reader": "scripts/prototype_lean4export_reader.py",
        "independent_census": "scripts/prototype_lean4export_census.py",
        "new_stream_aggregate_bytes": total_bytes,
        "streams": streams,
    }
    for case in data["cases"]:
        case_id = case["id"]
        if case_id == "direct-recursive-control":
            case["stage_b_wire"] = "historical-direct-recursive-control"
        elif case_id == "non-positive-source-negative":
            case["stage_b_wire"] = None
        else:
            case["stage_b_wire"] = case_id
    return json.dumps(data, indent=2, sort_keys=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="require committed bytes to match")
    args = parser.parse_args()
    try:
        rendered = render()
    except (OSError, ValueError) as error:
        print(f"lean construct matrix Stage B freeze: {error}", file=sys.stderr)
        return 1
    if args.check:
        committed = MANIFEST.read_text(encoding="utf-8")
        if committed != rendered:
            print("lean construct matrix Stage B freeze: committed registration drift", file=sys.stderr)
            return 1
        print("lean construct matrix Stage B freeze: committed registration matches official bytes")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
