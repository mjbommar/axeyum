#!/usr/bin/env python3
"""Generate the pinned v4.30.0 versus v4.32.1 statement comparison."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import stat
import subprocess
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-current-stable-statement-comparison-plan-v1.json"
CANDIDATES = ROOT / "artifacts/autogenesis/mathlib-nat-int-candidates-v1.json"
INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.32.1-nat-int-statement-inventory-v1.ndjson"
)
BASELINE_INVENTORY = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
CHECKOUT = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.32.1-checkout"
)
OUTPUT = ROOT / (
    "artifacts/autogenesis/"
    "mathlib-v4.30.0-v4.32.1-selected-statement-delta-v1.json"
)

PLAN_SHA256 = "19db7a3bf8260f5bad342f3895395102214a9bdedd95ff22cc556502a7b1544a"
CANDIDATES_SHA256 = "adbb3aff520664495089312a35ac2be1fd017a4ce39e4eff6443ea067d5c0704"
INVENTORY_SHA256 = "22246f40ae5a9b7f44a914313a5a212104b541d48974df4bf439da4006e61e5e"
BASELINE_INVENTORY_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
EXPECTED_FIELDS = {"level_params", "module", "name", "type", "type_repr"}
CONSTANT = re.compile(r"Lean\.Expr\.const\s+`([^\s\[\)]+)")
CLASS_ORDER = [
    "absent-in-current-stable",
    "structurally-identical",
    "pretty-type-only-drift",
    "structural-type-drift",
    "module-only-drift",
]


class ComparisonError(RuntimeError):
    """The source, inventory, candidate set, or generated comparison changed."""


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def text_sha256(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def row_sha256(value: dict[str, Any]) -> str:
    return text_sha256(canonical(value))


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ComparisonError(f"{path} is not an object")
    return value


def verify_inputs() -> None:
    if sha256(PLAN) != PLAN_SHA256 or sha256(CANDIDATES) != CANDIDATES_SHA256:
        raise ComparisonError("tracked comparison input changed")
    if (
        stat.S_IMODE(INVENTORY.stat().st_mode) != 0o444
        or INVENTORY.stat().st_size != 39619602
        or sha256(INVENTORY) != INVENTORY_SHA256
    ):
        raise ComparisonError("current-stable inventory changed or is mutable")
    if (
        stat.S_IMODE(BASELINE_INVENTORY.stat().st_mode) != 0o444
        or sha256(BASELINE_INVENTORY) != BASELINE_INVENTORY_SHA256
    ):
        raise ComparisonError("baseline inventory changed or is mutable")
    completed = subprocess.run(
        ["git", "-C", str(CHECKOUT), "rev-parse", "HEAD"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if completed.returncode or completed.stdout.strip() != "520045ab14e26149ee970e2e617ca04b09bde5d6":
        raise ComparisonError("current-stable checkout identity changed")


def load_inventory() -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    previous = ""
    with INVENTORY.open() as source:
        for line_number, line in enumerate(source, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise ComparisonError(f"inventory row {line_number} is malformed") from error
            if not isinstance(row, dict) or set(row) != EXPECTED_FIELDS:
                raise ComparisonError(f"inventory row {line_number} has non-statement fields")
            name = row.get("name")
            if (
                not isinstance(name, str)
                or not (name.startswith("Nat.") or name.startswith("Int."))
                or name in rows
                or (previous and name < previous)
            ):
                raise ComparisonError(f"inventory row {line_number} is out of scope or order")
            if not isinstance(row.get("module"), str) or not row["module"]:
                raise ComparisonError(f"inventory row {line_number} lacks a module")
            if not isinstance(row.get("level_params"), list) or not all(
                isinstance(value, str) for value in row["level_params"]
            ):
                raise ComparisonError(f"inventory row {line_number} has bad level parameters")
            if not isinstance(row.get("type"), str) or not row["type"]:
                raise ComparisonError(f"inventory row {line_number} lacks a pretty type")
            if not isinstance(row.get("type_repr"), str) or "Lean.Expr" not in row["type_repr"]:
                raise ComparisonError(f"inventory row {line_number} lacks a structural type")
            rows[name] = row
            previous = name
    if len(rows) != 9822:
        raise ComparisonError("current-stable inventory count changed")
    return rows


def load_baseline_selected(names: set[str]) -> dict[str, dict[str, Any]]:
    selected: dict[str, dict[str, Any]] = {}
    with BASELINE_INVENTORY.open() as source:
        for line in source:
            row = json.loads(line)
            name = row.get("name")
            if name in names:
                if name in selected or set(row) != EXPECTED_FIELDS:
                    raise ComparisonError(f"baseline selected row {name} is invalid")
                selected[name] = row
    missing = sorted(names - set(selected))
    if missing:
        raise ComparisonError(f"baseline selected rows are missing: {', '.join(missing)}")
    return selected


def constant_delta(baseline_repr: str, current_repr: str) -> dict[str, list[str]]:
    baseline = Counter(CONSTANT.findall(baseline_repr))
    current = Counter(CONSTANT.findall(current_repr))
    return {
        "removed": sorted((baseline - current).elements()),
        "added": sorted((current - baseline).elements()),
    }


def classify(
    candidate: dict[str, Any],
    baseline: dict[str, Any],
    current: dict[str, Any] | None,
) -> dict[str, Any]:
    baseline_constants = sorted(set(CONSTANT.findall(baseline["type_repr"])))
    enriched_baseline = {**baseline, "type_constants": baseline_constants}
    if (
        row_sha256(enriched_baseline) != candidate["source_row_sha256"]
        or baseline["module"] != candidate["module"]
        or baseline["level_params"] != candidate["level_params"]
        or baseline["type"] != candidate["type"]
        or text_sha256(baseline["type_repr"]) != candidate["type_repr_sha256"]
        or len(baseline_constants) != candidate["shape"]["distinct_type_constants"]
    ):
        raise ComparisonError(f"baseline candidate binding changed for {candidate['name']}")
    baseline_type_sha256 = text_sha256(candidate["type"])
    base = {
        "candidate_id": candidate["candidate_id"],
        "name": candidate["name"],
        "theme": candidate["theme"],
        "baseline_module": candidate["module"],
        "baseline_type_sha256": baseline_type_sha256,
        "baseline_type_repr_sha256": candidate["type_repr_sha256"],
    }
    if current is None:
        return {**base, "class": "absent-in-current-stable", "current": None}
    current_type_sha256 = text_sha256(current["type"])
    current_type_repr_sha256 = text_sha256(current["type_repr"])
    module_same = current["module"] == candidate["module"]
    pretty_same = current_type_sha256 == baseline_type_sha256
    structural_same = current_type_repr_sha256 == candidate["type_repr_sha256"]
    if not structural_same:
        classification = "structural-type-drift"
    elif not pretty_same:
        classification = "pretty-type-only-drift"
    elif not module_same:
        classification = "module-only-drift"
    else:
        classification = "structurally-identical"
    result = {
        **base,
        "class": classification,
        "current": {
            "module": current["module"],
            "level_params": current["level_params"],
            "type_sha256": current_type_sha256,
            "type_repr_sha256": current_type_repr_sha256,
            "source_row_sha256": row_sha256(current),
        },
    }
    if classification == "structural-type-drift":
        result["constant_multiset_delta"] = constant_delta(
            baseline["type_repr"], current["type_repr"]
        )
    return result


def build_comparison() -> dict[str, Any]:
    verify_inputs()
    inventory = load_inventory()
    candidates_object = load_object(CANDIDATES)
    candidates = candidates_object.get("candidates")
    if not isinstance(candidates, list) or len(candidates) != 240:
        raise ComparisonError("selected candidate population changed")
    names = [candidate.get("name") for candidate in candidates]
    if len(set(names)) != 240 or not all(isinstance(name, str) for name in names):
        raise ComparisonError("selected candidate names are invalid")
    baseline = load_baseline_selected(set(names))
    rows = [
        classify(candidate, baseline[candidate["name"]], inventory.get(candidate["name"]))
        for candidate in candidates
    ]
    counts = Counter(row["class"] for row in rows)
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-selected-statement-version-comparison",
        "state": "current-stable-statements-classified-no-proof-credit",
        "plan": {
            "path": str(PLAN.relative_to(ROOT)),
            "sha256": PLAN_SHA256,
        },
        "baseline": {
            "mathlib_tag": "v4.30.0",
            "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            "lean_version": "4.30.0",
            "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
            "inventory_sha256": "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc",
            "inventory_records": 9729,
        },
        "comparison": {
            "mathlib_tag": "v4.32.1",
            "mathlib_commit": "520045ab14e26149ee970e2e617ca04b09bde5d6",
            "lean_version": "4.32.1",
            "lean_githash": "f054605aea4b840552cca2e725580bffd1e1b704",
            "inventory_path": str(INVENTORY),
            "inventory_sha256": INVENTORY_SHA256,
            "inventory_bytes": 39619602,
            "inventory_records": 9822,
            "inventory_mode": "0444",
        },
        "extractor": {
            "path": "scripts/lean/autogenesis_mathlib_statement_inventory.lean",
            "sha256": "78cc93de6ab3c1fed5378c757f0ebfcbee47e66ecd72c25022755a4707e2b376",
            "compatibility_patches": 0,
            "statement_extractions": 1,
        },
        "selected_input": {
            "path": str(CANDIDATES.relative_to(ROOT)),
            "sha256": CANDIDATES_SHA256,
            "records": 240,
        },
        "summary": {
            "selected": 240,
            "classified": len(rows),
            "class_counts": {name: counts.get(name, 0) for name in CLASS_ORDER},
            "inventory_record_delta": 93,
        },
        "rows": rows,
        "authority": {
            "mathlib_source_proof_bodies_read": 0,
            "theorem_values_read": 0,
            "proof_imports": 0,
            "proof_search_invocations": 0,
            "kernel_theorem_submissions": 0,
            "executor_invocations": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": (
            "Statement survival and structural type identity do not establish proof portability, "
            "kernel compatibility, or theorem credit. Axeyum remains pinned to Lean/Mathlib 4.30.0."
        ),
    }


def render(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate(value: dict[str, Any]) -> None:
    if value != build_comparison():
        raise ComparisonError("comparison differs from generated version contract")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        comparison = build_comparison()
        expected = render(comparison)
        if args.check:
            if not OUTPUT.exists() or OUTPUT.read_text() != expected:
                raise ComparisonError(f"{OUTPUT.relative_to(ROOT)} is stale")
            counts = comparison["summary"]["class_counts"]
            print(
                "AUTOGENESIS_MATHLIB_STABLE_COMPARISON_OK|selected=240|"
                f"identical={counts['structurally-identical']}|"
                f"structural_drift={counts['structural-type-drift']}|"
                f"absent={counts['absent-in-current-stable']}|proofs=0|evaluation=0|ledger_writes=0"
            )
        else:
            OUTPUT.write_text(expected)
            print(f"wrote {OUTPUT.relative_to(ROOT)}")
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, ComparisonError) as error:
        print(f"autogenesis-mathlib-stable-comparison: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
