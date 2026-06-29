#!/usr/bin/env python3
"""Validate Axeyum's foundational concept atlas seed artifact."""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "foundational-concepts.schema.json"
ATLAS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
CURRICULUM = ROOT / "docs" / "curriculum" / "curriculum.toml"
MATH_FIELDS = ROOT / "docs" / "foundational-resources" / "MATH-FIELDS.md"

KINDS = {"curriculum-node", "field", "bridge-concept", "example-family"}
DOMAINS = {"mathematics", "computer-science", "logic", "statistics"}
DECIDABILITY = {"decidable", "computable", "bounded", "numerical", "proof-horizon"}
RESOURCE_STATUS = {"seeded", "planned", "validated", "proof-horizon"}
CURRICULUM_STATUS = {"covered", "planned", "lean-horizon", "extension"}
PACK_STATUS = {"planned", "validated", "deprecated"}
PROOF_STATUS = {"planned", "checked", "replay-only", "proof-gap", "lean-horizon"}
LEAN_STATUS = {"not-required", "planned", "partial", "required", "checked"}

ROW_REQUIRED = {
    "id",
    "kind",
    "title",
    "domain",
    "field_ids",
    "curriculum_node",
    "curriculum_layer",
    "curriculum_area",
    "curriculum_status",
    "curriculum_family",
    "resource_status",
    "summary",
    "prerequisites",
    "unlocks",
    "decidability",
    "axeyum_fragments",
    "example_packs",
    "proof_routes",
    "source_refs",
    "open_gaps",
    "graduation",
}
PACK_REQUIRED = {"id", "status", "path", "notes"}
PROOF_REQUIRED = {"name", "status", "checker", "lean_status", "sources", "notes"}
GRAD_REQUIRED = {"status", "criteria"}


class ValidationError(Exception):
    pass


def fail(message: str) -> None:
    raise ValidationError(message)


def load_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except json.JSONDecodeError as error:
        fail(f"{path.relative_to(ROOT)} is invalid JSON: {error}")


def load_curriculum() -> dict[str, dict[str, Any]]:
    with CURRICULUM.open("rb") as handle:
        data = tomllib.load(handle)
    return {node["id"]: node for node in data["node"]}


def load_math_field_ids() -> set[str]:
    fields: set[str] = set()
    in_table = False
    for line in MATH_FIELDS.read_text(encoding="utf-8").splitlines():
        if line == "## Field Set":
            in_table = True
            continue
        if line == "## Priority Bands":
            break
        if in_table and line.startswith("| `"):
            fields.add(line.split("|", 2)[1].strip().strip("`"))
    if not fields:
        fail("could not read any field ids from MATH-FIELDS.md")
    return fields


def require_keys(context: str, value: dict[str, Any], keys: set[str]) -> None:
    missing = sorted(keys - set(value))
    if missing:
        fail(f"{context} missing required keys: {', '.join(missing)}")


def require_string(context: str, value: Any) -> None:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a non-empty string")


def require_string_list(context: str, value: Any, *, nonempty: bool = True) -> list[str]:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    if nonempty and not value:
        fail(f"{context} must not be empty")
    seen: set[str] = set()
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            fail(f"{context}[{index}] must be a non-empty string")
        if item in seen:
            fail(f"{context} repeats {item!r}")
        seen.add(item)
    return value


def check_local_source(context: str, source: str) -> None:
    if source.startswith(("http://", "https://")):
        return
    path_part = source.split("#", 1)[0]
    if not path_part:
        return
    if not (ROOT / path_part).exists():
        fail(f"{context} references missing local source: {source}")


def check_sources(context: str, sources: list[str]) -> None:
    for source in sources:
        check_local_source(context, source)


def check_path_reference(context: str, path: str, status: str) -> None:
    if status == "validated" and not (ROOT / path).exists():
        fail(f"{context} marks validated pack but path is missing: {path}")


def validate_pack(context: str, pack: Any) -> None:
    if not isinstance(pack, dict):
        fail(f"{context} must be an object")
    require_keys(context, pack, PACK_REQUIRED)
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", pack["id"]):
        fail(f"{context}.id must be lowercase kebab case")
    if pack["status"] not in PACK_STATUS:
        fail(f"{context}.status invalid: {pack['status']!r}")
    require_string(f"{context}.path", pack["path"])
    require_string(f"{context}.notes", pack["notes"])
    check_path_reference(context, pack["path"], pack["status"])


def validate_proof(context: str, proof: Any) -> None:
    if not isinstance(proof, dict):
        fail(f"{context} must be an object")
    require_keys(context, proof, PROOF_REQUIRED)
    require_string(f"{context}.name", proof["name"])
    if proof["status"] not in PROOF_STATUS:
        fail(f"{context}.status invalid: {proof['status']!r}")
    require_string(f"{context}.checker", proof["checker"])
    if proof["lean_status"] not in LEAN_STATUS:
        fail(f"{context}.lean_status invalid: {proof['lean_status']!r}")
    sources = require_string_list(f"{context}.sources", proof["sources"])
    check_sources(f"{context}.sources", sources)
    require_string(f"{context}.notes", proof["notes"])


def validate_graduation(context: str, graduation: Any) -> None:
    if not isinstance(graduation, dict):
        fail(f"{context} must be an object")
    require_keys(context, graduation, GRAD_REQUIRED)
    if graduation["status"] not in RESOURCE_STATUS:
        fail(f"{context}.status invalid: {graduation['status']!r}")
    require_string_list(f"{context}.criteria", graduation["criteria"])


def row_id_for_node(node_id: str) -> str:
    return f"curriculum_{node_id.replace('-', '_')}"


def validate_row(
    row: Any,
    seen: set[str],
    row_ids: set[str],
    curriculum: dict[str, dict[str, Any]],
    field_ids: set[str],
) -> None:
    if not isinstance(row, dict):
        fail("row must be an object")
    require_keys("row", row, ROW_REQUIRED)
    row_id = row["id"]
    if not isinstance(row_id, str) or not re.fullmatch(r"[a-z0-9_]+", row_id):
        fail(f"row id must be stable lowercase snake case: {row_id!r}")
    if row_id in seen:
        fail(f"duplicate row id: {row_id}")
    seen.add(row_id)

    if row["kind"] not in KINDS:
        fail(f"{row_id}.kind invalid: {row['kind']!r}")
    if row["domain"] not in DOMAINS:
        fail(f"{row_id}.domain invalid: {row['domain']!r}")
    if row["decidability"] not in DECIDABILITY:
        fail(f"{row_id}.decidability invalid: {row['decidability']!r}")
    if row["resource_status"] not in RESOURCE_STATUS:
        fail(f"{row_id}.resource_status invalid: {row['resource_status']!r}")
    if row["curriculum_status"] not in CURRICULUM_STATUS:
        fail(f"{row_id}.curriculum_status invalid: {row['curriculum_status']!r}")
    for key in ("title", "summary"):
        require_string(f"{row_id}.{key}", row[key])

    row_fields = set(require_string_list(f"{row_id}.field_ids", row["field_ids"]))
    missing_fields = sorted(row_fields - field_ids)
    if missing_fields:
        fail(f"{row_id}.field_ids has unknown fields: {', '.join(missing_fields)}")

    for edge_key in ("prerequisites", "unlocks"):
        edges = require_string_list(f"{row_id}.{edge_key}", row[edge_key], nonempty=False)
        missing_edges = sorted(set(edges) - row_ids)
        if missing_edges:
            fail(f"{row_id}.{edge_key} references unknown rows: {', '.join(missing_edges)}")

    require_string_list(f"{row_id}.axeyum_fragments", row["axeyum_fragments"])
    for index, pack in enumerate(row["example_packs"]):
        validate_pack(f"{row_id}.example_packs[{index}]", pack)
    if not row["example_packs"]:
        fail(f"{row_id}.example_packs must not be empty")
    for index, proof in enumerate(row["proof_routes"]):
        validate_proof(f"{row_id}.proof_routes[{index}]", proof)
    if not row["proof_routes"]:
        fail(f"{row_id}.proof_routes must not be empty")
    sources = require_string_list(f"{row_id}.source_refs", row["source_refs"])
    check_sources(f"{row_id}.source_refs", sources)
    require_string_list(f"{row_id}.open_gaps", row["open_gaps"])
    validate_graduation(f"{row_id}.graduation", row["graduation"])

    if row["kind"] == "curriculum-node":
        node_id = row["curriculum_node"]
        if node_id not in curriculum:
            fail(f"{row_id}.curriculum_node is not in curriculum.toml: {node_id!r}")
        node = curriculum[node_id]
        expected_id = row_id_for_node(node_id)
        if row_id != expected_id:
            fail(f"{row_id} should be {expected_id}")
        if row["title"] != node["title"]:
            fail(f"{row_id}.title does not match curriculum.toml")
        if row["curriculum_layer"] != node["layer"]:
            fail(f"{row_id}.curriculum_layer does not match curriculum.toml")
        if row["curriculum_area"] != node["area"]:
            fail(f"{row_id}.curriculum_area does not match curriculum.toml")
        if row["curriculum_status"] != node["status"]:
            fail(f"{row_id}.curriculum_status does not match curriculum.toml")
        if row["curriculum_family"] != node["family"]:
            fail(f"{row_id}.curriculum_family does not match curriculum.toml")
        expected_prereqs = [row_id_for_node(item) for item in node["prerequisites"]]
        expected_unlocks = [row_id_for_node(item) for item in node["unlocks"] if item in curriculum]
        if row["prerequisites"] != expected_prereqs:
            fail(f"{row_id}.prerequisites does not match curriculum.toml")
        if row["unlocks"] != expected_unlocks:
            fail(f"{row_id}.unlocks does not match curriculum.toml")
        if node["status"] == "covered" and not row["curriculum_family"]:
            text = " ".join(row["open_gaps"]).lower()
            if "migration" not in text:
                fail(f"{row_id} is covered but has no family or migration note")
    elif row["curriculum_node"] is not None:
        fail(f"{row_id}.curriculum_node must be null for non-curriculum rows")


def main() -> int:
    load_json(SCHEMA)
    atlas = load_json(ATLAS)
    if not isinstance(atlas, dict):
        fail("atlas must be an object")
    if atlas.get("schema_version") != 1:
        fail("atlas.schema_version must be 1")
    generated_from = require_string_list("atlas.generated_from", atlas.get("generated_from"))
    check_sources("atlas.generated_from", generated_from)
    rows = atlas.get("rows")
    if not isinstance(rows, list) or not rows:
        fail("atlas.rows must be a non-empty list")

    curriculum = load_curriculum()
    field_ids = load_math_field_ids()
    row_ids = {row.get("id") for row in rows if isinstance(row, dict)}
    seen: set[str] = set()
    for row in rows:
        validate_row(row, seen, row_ids, curriculum, field_ids)

    curriculum_rows = [row for row in rows if row.get("kind") == "curriculum-node"]
    seen_nodes = {row["curriculum_node"] for row in curriculum_rows}
    missing_nodes = sorted(set(curriculum) - seen_nodes)
    extra_nodes = sorted(seen_nodes - set(curriculum))
    if missing_nodes or extra_nodes:
        fail(f"curriculum node mismatch missing={missing_nodes} extra={extra_nodes}")
    for field_id in sorted(field_ids):
        if not any(field_id in row["field_ids"] for row in rows):
            fail(f"field id is not represented in atlas rows: {field_id}")

    print(
        f"validated {len(rows)} foundational concept rows "
        f"({len(curriculum_rows)} curriculum, {len(field_ids)} fields)"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validate-foundational-concepts: {error}", file=sys.stderr)
        raise SystemExit(1)
