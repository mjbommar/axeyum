#!/usr/bin/env python3
"""Generate or verify the frozen full Mathlib Nat/Int statement-survival atlas."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import stat
import sys
from collections import Counter
from typing import Any, Iterable


ROOT = pathlib.Path(__file__).resolve().parents[1]
PLAN = ROOT / "artifacts/autogenesis/mathlib-full-statement-survival-atlas-plan-v1.json"
SELECTED = ROOT / "artifacts/autogenesis/mathlib-v4.30.0-v4.32.1-selected-statement-delta-v1.json"
BASELINE = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson"
)
CURRENT = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.32.1-nat-int-statement-inventory-v1.ndjson"
)
EXTERNAL_DELTA = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-v4.32.1-nat-int-statement-delta-v1.ndjson"
)
ATLAS = ROOT / (
    "artifacts/autogenesis/"
    "mathlib-v4.30.0-v4.32.1-full-statement-survival-atlas-v1.json"
)

PLAN_SHA256 = "8c7a4db05ed7dd2898e80c44cccd13aac297ec725c536de86d2c3b98aea2582b"
SELECTED_SHA256 = "9174c2fa642a60c59bb48df5a4741103d7e98e599c13922756ba077975d0ad28"
BASELINE_SHA256 = "4285e551680abf3b0cafb11709015f04b3aef3eb05ce23af2392b12cec31aecc"
CURRENT_SHA256 = "22246f40ae5a9b7f44a914313a5a212104b541d48974df4bf439da4006e61e5e"
EXPECTED_FIELDS = {"level_params", "module", "name", "type", "type_repr"}
CONSTANT = re.compile(r"Lean\.Expr\.const\s+`([^\s\[\)]+)")
CLASS_ORDER = [
    "structurally-identical",
    "module-only-drift",
    "pretty-type-only-drift",
    "structural-type-drift",
    "removed-after-v4.30.0",
    "added-by-v4.32.1",
]


class AtlasError(RuntimeError):
    """The frozen input, atlas structure, projection, or authority changed."""


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
        raise AtlasError(f"{path} is not an object")
    return value


def verify_frozen_file(path: pathlib.Path, expected_sha256: str, records: int) -> None:
    if stat.S_IMODE(path.stat().st_mode) != 0o444 or sha256(path) != expected_sha256:
        raise AtlasError(f"{path} changed or is mutable")
    with path.open() as source:
        if sum(1 for _ in source) != records:
            raise AtlasError(f"{path} record count changed")


def verify_inputs() -> None:
    if sha256(PLAN) != PLAN_SHA256 or sha256(SELECTED) != SELECTED_SHA256:
        raise AtlasError("tracked atlas input changed")
    verify_frozen_file(BASELINE, BASELINE_SHA256, 9729)
    verify_frozen_file(CURRENT, CURRENT_SHA256, 9822)


def load_inventory(path: pathlib.Path, expected_records: int) -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    previous = ""
    with path.open() as source:
        for line_number, line in enumerate(source, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise AtlasError(f"{path} row {line_number} is malformed") from error
            if not isinstance(row, dict) or set(row) != EXPECTED_FIELDS:
                raise AtlasError(f"{path} row {line_number} has non-statement fields")
            name = row.get("name")
            if (
                not isinstance(name, str)
                or not (name.startswith("Nat.") or name.startswith("Int."))
                or name in rows
                or (previous and name < previous)
            ):
                raise AtlasError(f"{path} row {line_number} is out of scope or order")
            if not isinstance(row.get("module"), str) or not row["module"]:
                raise AtlasError(f"{path} row {line_number} lacks a module")
            if not isinstance(row.get("level_params"), list) or not all(
                isinstance(value, str) for value in row["level_params"]
            ):
                raise AtlasError(f"{path} row {line_number} has bad level parameters")
            if not isinstance(row.get("type"), str) or not row["type"]:
                raise AtlasError(f"{path} row {line_number} lacks a pretty type")
            if not isinstance(row.get("type_repr"), str) or "Lean.Expr" not in row["type_repr"]:
                raise AtlasError(f"{path} row {line_number} lacks a structural type")
            rows[name] = row
            previous = name
    if len(rows) != expected_records:
        raise AtlasError(f"{path} inventory count changed")
    return rows


def statement_identity(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "module": row["module"],
        "level_params": row["level_params"],
        "type_sha256": text_sha256(row["type"]),
        "type_repr_sha256": text_sha256(row["type_repr"]),
        "source_row_sha256": row_sha256(row),
    }


def constant_delta(baseline_repr: str, current_repr: str) -> dict[str, list[str]]:
    baseline = Counter(CONSTANT.findall(baseline_repr))
    current = Counter(CONSTANT.findall(current_repr))
    return {
        "removed": sorted((baseline - current).elements()),
        "added": sorted((current - baseline).elements()),
    }


def classify(
    name: str,
    baseline: dict[str, Any] | None,
    current: dict[str, Any] | None,
) -> dict[str, Any]:
    if baseline is None:
        assert current is not None
        return {
            "name": name,
            "domain": name.split(".", 1)[0],
            "class": "added-by-v4.32.1",
            "baseline": None,
            "current": statement_identity(current),
        }
    if current is None:
        return {
            "name": name,
            "domain": name.split(".", 1)[0],
            "class": "removed-after-v4.30.0",
            "baseline": statement_identity(baseline),
            "current": None,
        }
    baseline_identity = statement_identity(baseline)
    current_identity = statement_identity(current)
    if baseline_identity["type_repr_sha256"] != current_identity["type_repr_sha256"]:
        classification = "structural-type-drift"
    elif baseline_identity["type_sha256"] != current_identity["type_sha256"]:
        classification = "pretty-type-only-drift"
    elif baseline_identity["module"] != current_identity["module"]:
        classification = "module-only-drift"
    else:
        classification = "structurally-identical"
    result = {
        "name": name,
        "domain": name.split(".", 1)[0],
        "class": classification,
        "baseline": baseline_identity,
        "current": current_identity,
    }
    if classification == "structural-type-drift":
        result["constant_multiset_delta"] = constant_delta(
            baseline["type_repr"], current["type_repr"]
        )
    return result


def build_rows() -> list[dict[str, Any]]:
    """Perform the one authorized full structural pass."""
    verify_inputs()
    baseline = load_inventory(BASELINE, 9729)
    current = load_inventory(CURRENT, 9822)
    names = sorted(set(baseline) | set(current))
    if len(names) != 9839:
        raise AtlasError("union population changed")
    return [classify(name, baseline.get(name), current.get(name)) for name in names]


def render_ndjson(rows: Iterable[dict[str, Any]]) -> bytes:
    return ("".join(canonical(row) + "\n" for row in rows)).encode()


def load_external_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    previous = ""
    with EXTERNAL_DELTA.open() as source:
        for line_number, line in enumerate(source, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise AtlasError(f"external delta row {line_number} is malformed") from error
            if not isinstance(row, dict) or not isinstance(row.get("name"), str):
                raise AtlasError(f"external delta row {line_number} is invalid")
            if previous and row["name"] <= previous:
                raise AtlasError("external delta names are duplicated or out of order")
            rows.append(row)
            previous = row["name"]
    if len(rows) != 9839:
        raise AtlasError("external delta row count changed")
    return rows


def selected_projection(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    by_name = {row["name"]: row for row in rows}
    selected = load_object(SELECTED)
    projected: list[dict[str, Any]] = []
    for expected in selected.get("rows", []):
        full = by_name.get(expected.get("name"))
        if full is None:
            raise AtlasError("selected name is absent from the full atlas")
        measured_class = (
            "absent-in-current-stable"
            if full["class"] == "removed-after-v4.30.0"
            else full["class"]
        )
        baseline = full["baseline"]
        if baseline is None:
            raise AtlasError("selected baseline row is missing")
        projection = {
            "candidate_id": expected["candidate_id"],
            "name": expected["name"],
            "theme": expected["theme"],
            "baseline_module": baseline["module"],
            "baseline_type_sha256": baseline["type_sha256"],
            "baseline_type_repr_sha256": baseline["type_repr_sha256"],
            "class": measured_class,
        }
        if full["current"] is None:
            projection["current"] = None
        else:
            projection["current"] = full["current"]
        if "constant_multiset_delta" in full:
            projection["constant_multiset_delta"] = full["constant_multiset_delta"]
        projected.append(projection)
    if projected != selected.get("rows"):
        raise AtlasError("selected 240 projection differs from frozen comparison")
    return projected


def aggregate(rows: list[dict[str, Any]], external_sha256: str, external_bytes: int) -> dict[str, Any]:
    class_counts = Counter(row["class"] for row in rows)
    domain_counts = {
        domain: {
            classification: sum(
                row["domain"] == domain and row["class"] == classification for row in rows
            )
            for classification in CLASS_ORDER
        }
        for domain in ["Nat", "Int"]
    }
    transitions = Counter(
        (row["baseline"]["module"], row["current"]["module"])
        for row in rows
        if row["baseline"] is not None and row["current"] is not None
    )
    selected_projection(rows)
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-full-statement-survival-atlas",
        "state": "full-statement-surface-classified-no-proof-credit",
        "plan": {"path": str(PLAN.relative_to(ROOT)), "sha256": PLAN_SHA256},
        "baseline": {
            "mathlib_tag": "v4.30.0",
            "inventory_sha256": BASELINE_SHA256,
            "inventory_records": 9729,
        },
        "comparison": {
            "mathlib_tag": "v4.32.1",
            "inventory_sha256": CURRENT_SHA256,
            "inventory_records": 9822,
        },
        "external_delta": {
            "path": str(EXTERNAL_DELTA),
            "sha256": external_sha256,
            "bytes": external_bytes,
            "records": len(rows),
            "mode": "0444",
        },
        "summary": {
            "union_names": len(rows),
            "shared_names": sum(
                row["baseline"] is not None and row["current"] is not None for row in rows
            ),
            "class_counts": {
                classification: class_counts.get(classification, 0)
                for classification in CLASS_ORDER
            },
            "domain_class_counts": domain_counts,
            "module_transitions": [
                {
                    "baseline_module": baseline_module,
                    "current_module": current_module,
                    "count": count,
                }
                for (baseline_module, current_module), count in sorted(transitions.items())
            ],
            "removed_names": [
                row["name"] for row in rows if row["class"] == "removed-after-v4.30.0"
            ],
            "added_names": [
                row["name"] for row in rows if row["class"] == "added-by-v4.32.1"
            ],
            "selected_240_projection": {
                "selected_comparison_sha256": SELECTED_SHA256,
                "records": 240,
                "exact_match": True,
            },
        },
        "authority": {
            "full_structural_comparisons": 1,
            "inventory_extractions": 0,
            "mathlib_source_proof_bodies_read": 0,
            "theorem_values_read": 0,
            "proof_search_invocations": 0,
            "kernel_theorem_submissions": 0,
            "executor_invocations": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
            "retries": 0,
        },
        "limitations": (
            "The atlas measures statement-name and type metadata across two releases. It does "
            "not establish proof portability, kernel compatibility, or theorem credit."
        ),
    }


def render_atlas(value: dict[str, Any]) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate_row_shape(row: dict[str, Any]) -> None:
    required = {"name", "domain", "class", "baseline", "current"}
    if not required <= set(row) or set(row) - required - {"constant_multiset_delta"}:
        raise AtlasError(f"external delta row shape changed for {row.get('name')}")
    name = row["name"]
    if row["domain"] not in {"Nat", "Int"} or not name.startswith(row["domain"] + "."):
        raise AtlasError(f"external delta domain changed for {name}")
    if row["class"] not in CLASS_ORDER:
        raise AtlasError(f"external delta class changed for {name}")
    identity_fields = {
        "module",
        "level_params",
        "type_sha256",
        "type_repr_sha256",
        "source_row_sha256",
    }
    for side in ["baseline", "current"]:
        identity = row[side]
        if identity is None:
            continue
        if not isinstance(identity, dict) or set(identity) != identity_fields:
            raise AtlasError(f"{side} identity shape changed for {name}")
        if not isinstance(identity["module"], str) or not identity["module"]:
            raise AtlasError(f"{side} module changed for {name}")
        if not isinstance(identity["level_params"], list) or not all(
            isinstance(value, str) for value in identity["level_params"]
        ):
            raise AtlasError(f"{side} level parameters changed for {name}")
        if any(
            not isinstance(identity[field], str)
            or len(identity[field]) != 64
            or any(character not in "0123456789abcdef" for character in identity[field])
            for field in ["type_sha256", "type_repr_sha256", "source_row_sha256"]
        ):
            raise AtlasError(f"{side} digest changed for {name}")
    if row["class"] == "added-by-v4.32.1" and not (
        row["baseline"] is None and isinstance(row["current"], dict)
    ):
        raise AtlasError(f"added row boundary changed for {name}")
    if row["class"] == "removed-after-v4.30.0" and not (
        isinstance(row["baseline"], dict) and row["current"] is None
    ):
        raise AtlasError(f"removed row boundary changed for {name}")
    if row["class"] not in {"added-by-v4.32.1", "removed-after-v4.30.0"} and not (
        isinstance(row["baseline"], dict) and isinstance(row["current"], dict)
    ):
        raise AtlasError(f"shared row boundary changed for {name}")
    if (row["class"] == "structural-type-drift") != ("constant_multiset_delta" in row):
        raise AtlasError(f"constant delta boundary changed for {name}")
    if "constant_multiset_delta" in row:
        delta = row["constant_multiset_delta"]
        if (
            not isinstance(delta, dict)
            or set(delta) != {"removed", "added"}
            or not all(
                isinstance(values, list)
                and values == sorted(values)
                and all(isinstance(value, str) for value in values)
                for values in delta.values()
            )
        ):
            raise AtlasError(f"constant delta shape changed for {name}")


def validate_frozen_outputs() -> dict[str, Any]:
    verify_inputs()
    if stat.S_IMODE(EXTERNAL_DELTA.stat().st_mode) != 0o444:
        raise AtlasError("external delta is mutable")
    rows = load_external_rows()
    for row in rows:
        validate_row_shape(row)
    external_sha256 = sha256(EXTERNAL_DELTA)
    expected = aggregate(rows, external_sha256, EXTERNAL_DELTA.stat().st_size)
    if not ATLAS.exists() or load_object(ATLAS) != expected:
        raise AtlasError("tracked atlas differs from frozen external delta")
    return expected


def write_once() -> dict[str, Any]:
    if EXTERNAL_DELTA.exists() or ATLAS.exists():
        raise AtlasError("atlas output already exists; retries and overwrites are forbidden")
    rows = build_rows()
    payload = render_ndjson(rows)
    external_sha256 = hashlib.sha256(payload).hexdigest()
    atlas = aggregate(rows, external_sha256, len(payload))
    descriptor = os.open(EXTERNAL_DELTA, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        with os.fdopen(descriptor, "wb") as target:
            target.write(payload)
            target.flush()
            os.fsync(target.fileno())
    except BaseException:
        EXTERNAL_DELTA.unlink(missing_ok=True)
        raise
    os.chmod(EXTERNAL_DELTA, 0o444)
    ATLAS.write_text(render_atlas(atlas))
    return atlas


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        atlas = validate_frozen_outputs() if args.check else write_once()
        counts = atlas["summary"]["class_counts"]
        action = "verified" if args.check else "wrote"
        print(
            f"AUTOGENESIS_MATHLIB_FULL_SURVIVAL_ATLAS_OK|action={action}|union=9839|"
            f"identical={counts['structurally-identical']}|"
            f"module_only={counts['module-only-drift']}|"
            f"pretty_only={counts['pretty-type-only-drift']}|"
            f"structural={counts['structural-type-drift']}|"
            f"removed={counts['removed-after-v4.30.0']}|"
            f"added={counts['added-by-v4.32.1']}|proofs=0|evaluation=0|ledger_writes=0"
        )
        return 0
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError, AtlasError) as error:
        print(f"autogenesis-mathlib-full-survival-atlas: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
