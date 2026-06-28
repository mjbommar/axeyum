#!/usr/bin/env python3
"""Validate the first Axeyum SMT Fragment Atlas artifact.

The project deliberately keeps this validator dependency-free.  It is not a
complete JSON Schema implementation; it enforces the invariants that matter for
the incubator artifact: stable row identity, required evidence fields, local
source links, and no dominance claim without committed dominance evidence.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "artifacts" / "ontology" / "smt-fragments.json"
SCHEMA = ROOT / "artifacts" / "ontology" / "smt-fragments.schema.json"

STATUSES = {
    "accepted",
    "audited",
    "checked",
    "declined",
    "dominant-on-audited-row",
    "measured",
    "modeled",
    "none",
    "partial",
    "planned",
    "replay-checked",
    "sound-incomplete",
    "unknown",
    "validated",
}

ROW_REQUIRED = {
    "id",
    "smtlib_logic",
    "title",
    "scope",
    "sorts",
    "operators",
    "parser",
    "ir",
    "solver_routes",
    "model_replay",
    "proof_routes",
    "benchmarks",
    "dominance",
    "open_gaps",
    "axeyum_capability_links",
}

STATUS_BLOCK_REQUIRED = {"status", "sources", "notes"}
ROUTE_REQUIRED = {"name", "status", "sources", "notes"}
PROOF_REQUIRED = {"name", "status", "checker", "lean_status", "sources", "notes"}
BENCH_REQUIRED = {
    "name",
    "status",
    "source",
    "files",
    "decided",
    "decided_percent",
    "disagree",
    "notes",
}


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


def require_keys(context: str, value: dict[str, Any], required: set[str]) -> None:
    missing = sorted(required - set(value))
    if missing:
        fail(f"{context} missing required keys: {', '.join(missing)}")


def require_status(context: str, status: Any) -> None:
    if status not in STATUSES:
        fail(f"{context} has invalid status {status!r}")


def require_string_list(context: str, value: Any, *, nonempty: bool = True) -> None:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    if nonempty and not value:
        fail(f"{context} must not be empty")
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            fail(f"{context}[{index}] must be a non-empty string")


def check_source(context: str, source: str) -> None:
    if source.startswith(("http://", "https://")):
        return
    path_part = source.split("#", 1)[0]
    if not path_part:
        return
    path = ROOT / path_part
    if not path.exists():
        fail(f"{context} references missing local source: {source}")


def check_sources(context: str, sources: list[str]) -> None:
    seen: set[str] = set()
    for source in sources:
        if source in seen:
            fail(f"{context} repeats source: {source}")
        seen.add(source)
        check_source(context, source)


def validate_status_block(context: str, block: Any) -> None:
    if not isinstance(block, dict):
        fail(f"{context} must be an object")
    require_keys(context, block, STATUS_BLOCK_REQUIRED)
    require_status(f"{context}.status", block["status"])
    require_string_list(f"{context}.sources", block["sources"])
    check_sources(f"{context}.sources", block["sources"])
    if not isinstance(block["notes"], str) or not block["notes"]:
        fail(f"{context}.notes must be a non-empty string")


def validate_route(context: str, route: Any) -> None:
    if not isinstance(route, dict):
        fail(f"{context} must be an object")
    require_keys(context, route, ROUTE_REQUIRED)
    require_status(f"{context}.status", route["status"])
    require_string_list(f"{context}.sources", route["sources"])
    check_sources(f"{context}.sources", route["sources"])


def validate_proof(context: str, route: Any) -> None:
    if not isinstance(route, dict):
        fail(f"{context} must be an object")
    require_keys(context, route, PROOF_REQUIRED)
    require_status(f"{context}.status", route["status"])
    require_status(f"{context}.lean_status", route["lean_status"])
    require_string_list(f"{context}.sources", route["sources"])
    check_sources(f"{context}.sources", route["sources"])
    if not isinstance(route["checker"], str) or not route["checker"]:
        fail(f"{context}.checker must be a non-empty string")


def validate_benchmark(context: str, benchmark: Any) -> None:
    if not isinstance(benchmark, dict):
        fail(f"{context} must be an object")
    require_keys(context, benchmark, BENCH_REQUIRED)
    require_status(f"{context}.status", benchmark["status"])
    check_source(f"{context}.source", benchmark["source"])
    files = benchmark["files"]
    decided = benchmark["decided"]
    percent = benchmark["decided_percent"]
    disagree = benchmark["disagree"]
    if not isinstance(files, int) or files < 0:
        fail(f"{context}.files must be a non-negative integer")
    if not isinstance(decided, int) or decided < 0 or decided > files:
        fail(f"{context}.decided must be between 0 and files")
    if not isinstance(percent, int) or percent < 0 or percent > 100:
        fail(f"{context}.decided_percent must be between 0 and 100")
    expected = 0 if files == 0 else round(decided * 100 / files)
    if abs(expected - percent) > 1:
        fail(f"{context}.decided_percent={percent} does not match {decided}/{files}")
    if not isinstance(disagree, int) or disagree < 0:
        fail(f"{context}.disagree must be a non-negative integer")


def validate_row(row: Any, seen: set[str]) -> None:
    if not isinstance(row, dict):
        fail("row must be an object")
    require_keys("row", row, ROW_REQUIRED)
    row_id = row["id"]
    if not isinstance(row_id, str) or not re.fullmatch(r"[a-z0-9_]+", row_id):
        fail(f"row id must be stable lowercase snake case, got {row_id!r}")
    if row_id in seen:
        fail(f"duplicate row id: {row_id}")
    seen.add(row_id)

    for key in ("smtlib_logic", "title", "scope"):
        if not isinstance(row[key], str) or not row[key]:
            fail(f"{row_id}.{key} must be a non-empty string")
    require_string_list(f"{row_id}.sorts", row["sorts"])
    require_string_list(f"{row_id}.open_gaps", row["open_gaps"])
    require_string_list(f"{row_id}.axeyum_capability_links", row["axeyum_capability_links"])
    check_sources(f"{row_id}.axeyum_capability_links", row["axeyum_capability_links"])

    operators = row["operators"]
    if not isinstance(operators, dict):
        fail(f"{row_id}.operators must be an object")
    require_keys(f"{row_id}.operators", operators, {"supported_public", "partial", "declined"})
    for key in ("supported_public", "partial", "declined"):
        require_string_list(f"{row_id}.operators.{key}", operators[key], nonempty=False)

    validate_status_block(f"{row_id}.parser", row["parser"])
    validate_status_block(f"{row_id}.ir", row["ir"])
    validate_status_block(f"{row_id}.model_replay", row["model_replay"])

    if not row["solver_routes"]:
        fail(f"{row_id}.solver_routes must not be empty")
    for index, route in enumerate(row["solver_routes"]):
        validate_route(f"{row_id}.solver_routes[{index}]", route)

    if not row["proof_routes"]:
        fail(f"{row_id}.proof_routes must not be empty")
    for index, proof in enumerate(row["proof_routes"]):
        validate_proof(f"{row_id}.proof_routes[{index}]", proof)

    if not row["benchmarks"]:
        fail(f"{row_id}.benchmarks must not be empty")
    for index, benchmark in enumerate(row["benchmarks"]):
        validate_benchmark(f"{row_id}.benchmarks[{index}]", benchmark)

    dominance = row["dominance"]
    validate_status_block(f"{row_id}.dominance", dominance)
    if dominance["status"] == "dominant-on-audited-row":
        sources = dominance["sources"]
        has_report = any(source.startswith("bench-results/DOMINANCE.md") for source in sources)
        has_audit = any(source.startswith("bench-results/dominance/") for source in sources)
        if not has_report or not has_audit:
            fail(f"{row_id}.dominance must cite DOMINANCE.md and a dominance audit JSON")


def main() -> int:
    load_json(SCHEMA)
    atlas = load_json(ATLAS)
    if not isinstance(atlas, dict):
        fail("atlas must be an object")
    if atlas.get("schema_version") != 1:
        fail("atlas.schema_version must be 1")
    rows = atlas.get("rows")
    if not isinstance(rows, list) or not rows:
        fail("atlas.rows must be a non-empty list")
    seen: set[str] = set()
    for row in rows:
        validate_row(row, seen)
    print(f"validated {len(rows)} SMT fragment rows")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
