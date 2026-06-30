#!/usr/bin/env python3
"""Query the public foundational-resource JSON contract.

This is intentionally a tiny downstream-consumer example. It reads only the
committed atlas and example-pack JSON files, imports none of the validators or
generators, and prints stable table or JSON answers for common resource
questions.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
EXAMPLE_ROOT = ROOT / "artifacts" / "examples" / "math"
DEFAULT_LIMIT = 20
RECIPE_PREFIX = "docs/proof-cookbook/recipes/"


class QueryError(Exception):
    pass


def fail(message: str) -> None:
    raise QueryError(message)


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def join_values(values: list[str]) -> str:
    return ",".join(values) if values else "-"


def count_text(counter: Counter[str]) -> str:
    if not counter:
        return "-"
    return ",".join(f"{key}:{counter[key]}" for key in sorted(counter))


def contains_text(values: list[str], needle: str | None) -> bool:
    if needle is None:
        return True
    lowered = needle.lower()
    normalized = lowered.replace("_", "-")
    return any(
        lowered in value.lower() or normalized in value.lower().replace("_", "-")
        for value in values
    )


def flatten_strings(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, (int, float, bool)):
        return [str(value)]
    if isinstance(value, list):
        flattened: list[str] = []
        for item in value:
            flattened.extend(flatten_strings(item))
        return flattened
    if isinstance(value, dict):
        flattened = []
        for key, item in value.items():
            flattened.append(str(key))
            flattened.extend(flatten_strings(item))
        return flattened
    return [str(value)]


def check_route_text(check: dict[str, Any]) -> list[str]:
    return flatten_strings(
        {
            "id": check.get("id", ""),
            "claim": check.get("claim", ""),
            "validation": check.get("validation", ""),
            "proof_status": check.get("proof_status", ""),
            "expected_result": check.get("expected_result", ""),
            "data": check.get("data", {}),
            "notes": check.get("notes", ""),
        }
    )


def metadata_route_text(metadata: dict[str, Any]) -> list[str]:
    return flatten_strings(
        {
            "fragments": metadata.get("axeyum_fragments", []),
            "source_refs": metadata.get("source_refs", []),
            "trust_status": metadata.get("trust_status", ""),
            "solver_reuse": metadata.get("solver_reuse", {}),
            "graduation_criteria": metadata.get("graduation_criteria", []),
        }
    )


def recipe_names(metadata: dict[str, Any]) -> list[str]:
    names = []
    for source_ref in metadata.get("source_refs", []):
        if source_ref.startswith(RECIPE_PREFIX) and source_ref.endswith(".md"):
            names.append(Path(source_ref).stem)
    return sorted(set(names))


def shorten(value: str, width: int = 90) -> str:
    if len(value) <= width:
        return value
    return value[: width - 3].rstrip() + "..."


def as_table(rows: list[dict[str, Any]], columns: list[str]) -> str:
    if not rows:
        return "no rows"

    rendered = [
        {column: render_cell(row.get(column, "")) for column in columns}
        for row in rows
    ]
    widths = {
        column: max(len(column), *(len(row[column]) for row in rendered))
        for column in columns
    }
    header = " | ".join(column.ljust(widths[column]) for column in columns)
    separator = "-+-".join("-" * widths[column] for column in columns)
    lines = [header, separator]
    for row in rendered:
        lines.append(" | ".join(row[column].ljust(widths[column]) for column in columns))
    return "\n".join(lines)


def render_cell(value: Any) -> str:
    if isinstance(value, list):
        return join_values([str(item) for item in value])
    if isinstance(value, Counter):
        return count_text(value)
    if isinstance(value, dict):
        return json.dumps(value, sort_keys=True)
    return str(value)


def emit(rows: list[dict[str, Any]], columns: list[str], args: argparse.Namespace) -> int:
    if args.require_any and not rows:
        fail("query returned no rows")
    if args.limit is not None:
        rows = rows[: args.limit]
    if args.format == "json":
        print(json.dumps(rows, indent=2, sort_keys=True))
    else:
        print(as_table(rows, columns))
    return 0


class ResourceStore:
    def __init__(self) -> None:
        atlas = load_json(ATLAS)
        self.concepts: list[dict[str, Any]] = atlas.get("rows", [])
        if not self.concepts:
            fail(f"{ATLAS} has no rows")
        self.packs = self._load_packs()

    def pack_ids_for_concept(self, concept_id: str) -> set[str]:
        for concept in self.concepts:
            if concept.get("id") != concept_id:
                continue
            pack_ids = set()
            for pack_ref in concept.get("example_packs", []):
                if isinstance(pack_ref, dict):
                    pack_id = pack_ref.get("id")
                else:
                    pack_id = str(pack_ref)
                if pack_id:
                    pack_ids.add(pack_id)
            return pack_ids
        fail(f"unknown concept id: {concept_id}")

    def _load_packs(self) -> list[dict[str, Any]]:
        packs = []
        for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
            metadata = load_json(metadata_path)
            if metadata.get("claim_status") == "template":
                continue
            expected_path = metadata_path.parent / "expected.json"
            expected = load_json(expected_path)
            pack_id = metadata.get("id")
            if expected.get("pack_id") != pack_id:
                fail(f"{expected_path} pack_id does not match metadata id")
            packs.append(
                {
                    "id": pack_id,
                    "path": metadata_path.parent.relative_to(ROOT).as_posix(),
                    "metadata": metadata,
                    "expected": expected,
                    "checks": expected.get("checks", []),
                }
            )
        return packs

    def pack_rows(self) -> list[dict[str, Any]]:
        rows = []
        for pack in self.packs:
            metadata = pack["metadata"]
            checks = pack["checks"]
            proof_counts = Counter(check.get("proof_status", "") for check in checks)
            result_counts = Counter(check.get("expected_result", "") for check in checks)
            solver_reuse = metadata.get("solver_reuse") or {}
            rows.append(
                {
                    "pack": pack["id"],
                    "title": metadata["title"],
                    "fields": metadata["field_ids"],
                    "curriculum_nodes": metadata["curriculum_nodes"],
                    "fragments": metadata["axeyum_fragments"],
                    "trust": metadata["trust_status"],
                    "results": count_text(result_counts),
                    "proof": count_text(proof_counts),
                    "solver_reuse": solver_reuse.get("status", "unclassified"),
                    "solver_target": solver_reuse.get("target", "-"),
                    "path": pack["path"],
                    "_pack": pack,
                }
            )
        return sorted(rows, key=lambda row: row["pack"])

    def check_rows(self) -> list[dict[str, Any]]:
        rows = []
        for pack in self.packs:
            metadata = pack["metadata"]
            for check in pack["checks"]:
                rows.append(
                    {
                        "pack": pack["id"],
                        "check": check["id"],
                        "result": check.get("expected_result", ""),
                        "proof": check.get("proof_status", ""),
                        "validation": check.get("validation", ""),
                        "fields": metadata["field_ids"],
                        "fragments": metadata["axeyum_fragments"],
                        "claim": shorten(check.get("claim", "")),
                        "_pack": pack,
                        "_check": check,
                    }
                )
        return sorted(rows, key=lambda row: (row["pack"], row["check"]))

    def concept_rows(self) -> list[dict[str, Any]]:
        rows = []
        for concept in self.concepts:
            rows.append(
                {
                    "concept": concept["id"],
                    "kind": concept["kind"],
                    "title": concept["title"],
                    "fields": concept["field_ids"],
                    "curriculum_node": concept.get("curriculum_node") or "-",
                    "decidability": concept["decidability"],
                    "packs": [pack["id"] for pack in concept["example_packs"]],
                    "_concept": concept,
                }
            )
        return sorted(rows, key=lambda row: row["concept"])

    def field_summary_rows(self) -> list[dict[str, Any]]:
        field_titles = {}
        for concept in self.concepts:
            if concept.get("kind") != "field":
                continue
            field_ids = concept.get("field_ids", [])
            if len(field_ids) == 1:
                field_titles[field_ids[0]] = concept.get("title", field_ids[0])

        field_ids = set(field_titles)
        for concept in self.concepts:
            field_ids.update(concept.get("field_ids", []))
        for pack in self.packs:
            field_ids.update(pack["metadata"].get("field_ids", []))

        rows = []
        for field_id in sorted(field_ids):
            field_concepts = [
                concept
                for concept in self.concepts
                if field_id in concept.get("field_ids", [])
            ]
            field_packs = [
                pack
                for pack in self.packs
                if field_id in pack["metadata"].get("field_ids", [])
            ]
            proof_counts: Counter[str] = Counter()
            result_counts: Counter[str] = Counter()
            route_counts: Counter[str] = Counter()
            solver_reuse_counts: Counter[str] = Counter()
            curriculum_nodes = set()
            horizon_packs = []
            route_text = []

            for pack in field_packs:
                metadata = pack["metadata"]
                checks = pack["checks"]
                curriculum_nodes.update(metadata.get("curriculum_nodes", []))
                solver_reuse = metadata.get("solver_reuse") or {}
                solver_reuse_counts[solver_reuse.get("status", "unclassified")] += 1
                routes = recipe_names(metadata)
                route_counts.update(routes)
                route_text.extend(routes)
                route_text.extend(metadata_route_text(metadata))
                if any(check.get("proof_status") == "lean-horizon" for check in checks):
                    horizon_packs.append(pack["id"])
                for check in checks:
                    proof_counts[check.get("proof_status", "")] += 1
                    result_counts[check.get("expected_result", "")] += 1
                    route_text.extend(check_route_text(check))

            rows.append(
                {
                    "field": field_id,
                    "title": field_titles.get(field_id, field_id.replace("_", " ")),
                    "concepts": len(field_concepts),
                    "packs": len(field_packs),
                    "checks": sum(result_counts.values()),
                    "results": count_text(result_counts),
                    "proof": count_text(proof_counts),
                    "routes": count_text(route_counts),
                    "solver_reuse": count_text(solver_reuse_counts),
                    "curriculum_nodes": sorted(curriculum_nodes),
                    "sample_packs": [pack["id"] for pack in field_packs[:5]],
                    "horizon_packs": sorted(horizon_packs)[:5],
                    "_route_text": route_text,
                }
            )
        return rows


def command_summary(args: argparse.Namespace) -> int:
    store = ResourceStore()
    concept_counts = Counter(row["kind"] for row in store.concepts)
    proof_counts: Counter[str] = Counter()
    result_counts: Counter[str] = Counter()
    solver_reuse_counts: Counter[str] = Counter()
    for pack in store.packs:
        reuse = pack["metadata"].get("solver_reuse") or {}
        solver_reuse_counts[reuse.get("status", "unclassified")] += 1
        for check in pack["checks"]:
            proof_counts[check.get("proof_status", "")] += 1
            result_counts[check.get("expected_result", "")] += 1

    summary = {
        "concept_rows": len(store.concepts),
        "concept_kinds": dict(sorted(concept_counts.items())),
        "non_template_packs": len(store.packs),
        "checks": sum(len(pack["checks"]) for pack in store.packs),
        "expected_results": dict(sorted(result_counts.items())),
        "proof_statuses": dict(sorted(proof_counts.items())),
        "solver_reuse": dict(sorted(solver_reuse_counts.items())),
    }
    if args.format == "json":
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("foundational resource query summary")
        for key, value in summary.items():
            if isinstance(value, dict):
                value_text = ",".join(f"{item}:{value[item]}" for item in value)
            else:
                value_text = str(value)
            print(f"{key}={value_text}")
    return 0


def command_packs(args: argparse.Namespace) -> int:
    store = ResourceStore()
    concept_pack_ids = (
        store.pack_ids_for_concept(args.concept) if args.concept else None
    )
    rows = []
    for row in store.pack_rows():
        pack = row["_pack"]
        metadata = pack["metadata"]
        checks = pack["checks"]
        if concept_pack_ids is not None and row["pack"] not in concept_pack_ids:
            continue
        if args.field and args.field not in metadata["field_ids"]:
            continue
        if args.curriculum_node and args.curriculum_node not in metadata["curriculum_nodes"]:
            continue
        if args.solver_reuse and row["solver_reuse"] != args.solver_reuse:
            continue
        if args.proof_status and not any(
            check.get("proof_status") == args.proof_status for check in checks
        ):
            continue
        if args.expected_result and not any(
            check.get("expected_result") == args.expected_result for check in checks
        ):
            continue
        route_matches = [
            check
            for check in checks
            if contains_text(check_route_text(check), args.route)
        ]
        if args.route and not route_matches and not contains_text(
            metadata_route_text(metadata), args.route
        ):
            continue
        if not contains_text(metadata["axeyum_fragments"], args.fragment):
            continue
        if args.text:
            solver_reuse = metadata.get("solver_reuse") or {}
            haystack = [
                metadata["id"],
                metadata["title"],
                metadata["trust_status"],
                solver_reuse.get("target", ""),
                solver_reuse.get("pressure", ""),
                solver_reuse.get("next_step", ""),
                *(metadata["source_refs"]),
                *(metadata["graduation_criteria"]),
            ]
            if not contains_text(haystack, args.text):
                continue
        if args.route:
            row["route_checks"] = [check["id"] for check in route_matches] or [
                "pack-metadata"
            ]
            row["route_validations"] = sorted(
                {
                    check.get("validation", "")
                    for check in route_matches
                    if check.get("validation")
                }
            )
        rows.append(clean_row(row))
    columns = ["pack", "fields", "trust", "results", "proof", "solver_reuse", "path"]
    if args.route:
        columns = [
            "pack",
            "fields",
            "route_checks",
            "route_validations",
            "trust",
            "solver_reuse",
            "path",
        ]
    return emit(
        rows,
        columns,
        args,
    )


def command_checks(args: argparse.Namespace) -> int:
    store = ResourceStore()
    concept_pack_ids = (
        store.pack_ids_for_concept(args.concept) if args.concept else None
    )
    rows = []
    for row in store.check_rows():
        pack = row["_pack"]
        metadata = pack["metadata"]
        check = row["_check"]
        if concept_pack_ids is not None and row["pack"] not in concept_pack_ids:
            continue
        if args.pack and row["pack"] != args.pack:
            continue
        if args.field and args.field not in metadata["field_ids"]:
            continue
        if args.proof_status and row["proof"] != args.proof_status:
            continue
        if args.expected_result and row["result"] != args.expected_result:
            continue
        if args.validation and args.validation.lower() not in row["validation"].lower():
            continue
        if args.route and not contains_text(check_route_text(check), args.route):
            continue
        if not contains_text(metadata["axeyum_fragments"], args.fragment):
            continue
        if args.text:
            haystack = [
                check.get("id", ""),
                check.get("claim", ""),
                check.get("notes", ""),
                check.get("validation", ""),
            ]
            if not contains_text(haystack, args.text):
                continue
        rows.append(clean_row(row))
    return emit(rows, ["pack", "check", "result", "proof", "validation", "claim"], args)


def command_concepts(args: argparse.Namespace) -> int:
    store = ResourceStore()
    rows = []
    for row in store.concept_rows():
        concept = row["_concept"]
        if args.kind and row["kind"] != args.kind:
            continue
        if args.field and args.field not in concept["field_ids"]:
            continue
        if args.curriculum_node and row["curriculum_node"] != args.curriculum_node:
            continue
        if args.decidability and row["decidability"] != args.decidability:
            continue
        if args.pack and args.pack not in row["packs"]:
            continue
        if args.text:
            haystack = [
                concept["id"],
                concept["title"],
                concept["summary"],
                *(concept["open_gaps"]),
            ]
            if not contains_text(haystack, args.text):
                continue
        rows.append(clean_row(row))
    return emit(
        rows,
        ["concept", "kind", "fields", "curriculum_node", "decidability", "packs"],
        args,
    )


def command_fields(args: argparse.Namespace) -> int:
    store = ResourceStore()
    rows = []
    for row in store.field_summary_rows():
        if args.field and row["field"] != args.field:
            continue
        if args.route and not contains_text(row["_route_text"], args.route):
            continue
        if args.text:
            haystack = [
                row["field"],
                row["title"],
                *(row["curriculum_nodes"]),
                *(row["sample_packs"]),
                *(row["horizon_packs"]),
            ]
            if not contains_text(haystack, args.text):
                continue
        rows.append(clean_row(row))
    return emit(
        rows,
        [
            "field",
            "packs",
            "checks",
            "proof",
            "routes",
            "solver_reuse",
            "sample_packs",
            "horizon_packs",
        ],
        args,
    )


def clean_row(row: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in row.items() if not key.startswith("_")}


def add_output_args(parser: argparse.ArgumentParser, *, default_limit: int | None) -> None:
    parser.add_argument("--format", choices=["table", "json"], default="table")
    parser.add_argument("--limit", type=int, default=default_limit)
    parser.add_argument(
        "--require-any",
        action="store_true",
        help="fail if the query returns no rows before --limit is applied",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Query Axeyum foundational-resource JSON data."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    summary = subparsers.add_parser("summary", help="print aggregate contract counts")
    summary.add_argument("--format", choices=["table", "json"], default="table")
    summary.set_defaults(func=command_summary)

    packs = subparsers.add_parser("packs", help="list example packs")
    packs.add_argument("--field", help="exact field id, such as graph_theory")
    packs.add_argument("--curriculum-node", help="exact curriculum node id")
    packs.add_argument("--concept", help="exact atlas concept id")
    packs.add_argument("--fragment", help="case-insensitive fragment substring")
    packs.add_argument(
        "--route",
        help="case-insensitive proof/evidence route substring, such as Farkas or qf-bv",
    )
    packs.add_argument("--proof-status", help="pack has at least one check with this status")
    packs.add_argument("--expected-result", help="pack has at least one sat/unsat/unknown row")
    packs.add_argument(
        "--solver-reuse",
        choices=["candidate", "promoted", "non-benchmark-horizon", "unclassified"],
    )
    packs.add_argument("--text", help="case-insensitive search over pack metadata text")
    add_output_args(packs, default_limit=DEFAULT_LIMIT)
    packs.set_defaults(func=command_packs)

    checks = subparsers.add_parser("checks", help="list expected-result rows")
    checks.add_argument("--pack", help="exact example-pack id")
    checks.add_argument("--field", help="exact field id")
    checks.add_argument("--concept", help="exact atlas concept id")
    checks.add_argument("--fragment", help="case-insensitive fragment substring")
    checks.add_argument(
        "--route",
        help="case-insensitive proof/evidence route substring, such as Farkas or qf-bv",
    )
    checks.add_argument("--proof-status", help="exact proof_status")
    checks.add_argument("--expected-result", help="exact expected_result")
    checks.add_argument("--validation", help="case-insensitive validation substring")
    checks.add_argument("--text", help="case-insensitive search over check text")
    add_output_args(checks, default_limit=DEFAULT_LIMIT)
    checks.set_defaults(func=command_checks)

    concepts = subparsers.add_parser("concepts", help="list atlas rows")
    concepts.add_argument("--kind", help="exact concept kind")
    concepts.add_argument("--field", help="exact field id")
    concepts.add_argument("--curriculum-node", help="exact curriculum node id")
    concepts.add_argument("--decidability", help="exact decidability class")
    concepts.add_argument("--pack", help="concept references this pack")
    concepts.add_argument("--text", help="case-insensitive search over concept text")
    add_output_args(concepts, default_limit=DEFAULT_LIMIT)
    concepts.set_defaults(func=command_concepts)

    fields = subparsers.add_parser("fields", help="summarize curriculum fields")
    fields.add_argument("--field", help="exact field id, such as probability_theory")
    fields.add_argument(
        "--route",
        help="case-insensitive proof/evidence route substring, such as Farkas or Lean",
    )
    fields.add_argument(
        "--text",
        help="case-insensitive search over field, curriculum-node, and pack names",
    )
    add_output_args(fields, default_limit=DEFAULT_LIMIT)
    fields.set_defaults(func=command_fields)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        return args.func(args)
    except QueryError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
