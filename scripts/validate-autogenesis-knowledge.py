#!/usr/bin/env python3
"""Validate the additive Autogenesis knowledge overlay.

The overlay is additive: it does not modify facts, operations, or kernel
projections. This validator checks the relational contract that JSON Schema
cannot: unique identities, typed endpoints, local resolution, and
relation-domain/range compatibility.

EVERY ENDPOINT RESOLVES INSIDE THIS CHECKOUT. Until 2026-08-24 this validator
read a sibling repository at ``root.parent / "math-education"`` and resolved
concept and technique ids against its files. ADR-0553 removed that: the overlay
may not name an external repository, so there is nothing outside this tree to
resolve against and no code here that looks. `scripts/check-external-coupling.py`
is the gate that keeps it that way.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
SCHEMA = ROOT / "artifacts/ontology/autogenesis-knowledge-overlay.schema.json"

TOP_KEYS = {
    "schema_version",
    "kind",
    "sources",
    "namespaces",
    "relation_types",
    "entities",
    "links",
}
ENTITY_KINDS = {
    "fact",
    "kernel-declaration",
    "operation",
    "producer",
    "checker",
    "capability",
    "obstruction",
    "episode",
    "evidence-artifact",
    "representation",
    "concept",
}
ASSURANCE = {
    "formal-derived",
    "independently-checked",
    "registry-derived",
    "mechanically-observed",
    "human-reviewed",
    "heuristic",
    "proposed",
}
METHODS = {
    "kernel-derived",
    "checker-derived",
    "registry-derived",
    "mechanically-observed",
    "human-reviewed",
    "heuristic",
    "proposed",
}


def load_json(path: Path, errors: list[str]) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"{path}: cannot read JSON: {exc}")
        return None


def duplicate_ids(rows: list[dict[str, Any]], label: str, errors: list[str]) -> None:
    seen: set[str] = set()
    for row in rows:
        ident = row.get("id")
        if not isinstance(ident, str):
            errors.append(f"{label}: row has no string id")
        elif ident in seen:
            errors.append(f"{label}: duplicate id {ident!r}")
        else:
            seen.add(ident)


def schema_check(doc: Any, errors: list[str]) -> None:
    """Use Draft 2020-12 when available; retain essential checks without it."""
    try:
        import jsonschema  # type: ignore[import-not-found]
    except ImportError:
        jsonschema = None
    if jsonschema is not None:
        schema = json.loads(SCHEMA.read_text())
        validator = jsonschema.Draft202012Validator(schema)
        for err in sorted(validator.iter_errors(doc), key=lambda e: list(e.path)):
            where = ".".join(str(part) for part in err.path) or "<root>"
            errors.append(f"schema {where}: {err.message}")
        return
    if not isinstance(doc, dict):
        errors.append("overlay root must be an object")
        return
    if set(doc) != TOP_KEYS:
        errors.append(f"overlay root keys differ: got {sorted(doc)}, expected {sorted(TOP_KEYS)}")
    if doc.get("schema_version") != 1:
        errors.append("schema_version must be 1")
    if doc.get("kind") != "axeyum-autogenesis-knowledge-overlay":
        errors.append("kind must be axeyum-autogenesis-knowledge-overlay")
    for key in ("sources", "namespaces", "relation_types", "entities", "links"):
        if not isinstance(doc.get(key), list):
            errors.append(f"{key} must be an array")


def validate_document(doc: Any, root: Path = ROOT) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    schema_check(doc, errors)
    if errors or not isinstance(doc, dict):
        return errors, warnings

    sources = doc["sources"]
    namespaces = doc["namespaces"]
    relations = doc["relation_types"]
    entities = doc["entities"]
    links = doc["links"]
    for label, rows in (
        ("sources", sources),
        ("namespaces", namespaces),
        ("relation_types", relations),
        ("entities", entities),
        ("links", links),
    ):
        duplicate_ids(rows, label, errors)

    source_by_id = {row["id"]: row for row in sources}
    ns_by_id = {row["id"]: row for row in namespaces}
    relation_by_id = {row["id"]: row for row in relations}
    entity_by_id = {row["id"]: row for row in entities}

    for source in sources:
        if source.get("revision_policy") == "pinned" and not source.get("revision"):
            errors.append(f"source {source['id']}: pinned source has no revision")
    for namespace in namespaces:
        if namespace.get("source_id") not in source_by_id:
            errors.append(
                f"namespace {namespace['id']}: unknown source_id {namespace.get('source_id')!r}"
            )
        for kind in namespace.get("entity_kinds", []):
            if kind not in ENTITY_KINDS:
                errors.append(f"namespace {namespace['id']}: unknown entity kind {kind!r}")
        pattern = namespace.get("id_pattern")
        if pattern:
            try:
                re.compile(pattern)
            except re.error as exc:
                errors.append(f"namespace {namespace['id']}: invalid id_pattern: {exc}")

    operation_doc = load_json(root / "artifacts/autogenesis/operations.json", errors)
    fact_docs = {}
    for path in sorted((root / "artifacts/facts").glob("*.json")):
        document = load_json(path, errors)
        if isinstance(document, dict) and isinstance(document.get("id"), str):
            fact_docs[document["id"]] = document
    operation_ids = {row.get("id") for row in (operation_doc or {}).get("operations", [])}
    kernel_projection = load_json(
        root / "artifacts/autogenesis/kernel-dependency-projection-v1.json", errors
    )
    kernel_declaration_ids = {
        row.get("id")
        for row in (kernel_projection or {}).get("declarations", [])
        if isinstance(row, dict)
    }
    kernel_declarations = {
        row.get("id"): row
        for row in (kernel_projection or {}).get("declarations", [])
        if isinstance(row, dict) and isinstance(row.get("id"), str)
    }

    def check_endpoint(endpoint: dict[str, Any], link_id: str, side: str) -> None:
        namespace_id = endpoint.get("namespace")
        namespace = ns_by_id.get(namespace_id)
        if namespace is None:
            errors.append(f"link {link_id} {side}: unknown namespace {namespace_id!r}")
            return
        kind = endpoint.get("kind")
        ident = endpoint.get("id")
        if kind not in namespace.get("entity_kinds", []):
            errors.append(
                f"link {link_id} {side}: kind {kind!r} not allowed by namespace {namespace_id}"
            )
        pattern = namespace.get("id_pattern")
        if pattern and (not isinstance(ident, str) or re.fullmatch(pattern, ident) is None):
            errors.append(f"link {link_id} {side}: id {ident!r} violates namespace pattern")
        resolution = namespace.get("resolution")
        if resolution == "overlay-entity":
            entity = entity_by_id.get(ident)
            if entity is None:
                errors.append(f"link {link_id} {side}: unknown overlay entity {ident!r}")
            elif entity.get("kind") != kind:
                errors.append(f"link {link_id} {side}: overlay entity kind mismatch for {ident}")
        elif namespace_id == "axeyum-fact":
            if ident not in fact_docs:
                errors.append(f"link {link_id} {side}: unknown fact {ident!r}")
        elif namespace_id == "axeyum-operation" and ident not in operation_ids:
            errors.append(f"link {link_id} {side}: unknown operation {ident!r}")
        elif namespace_id == "axeyum-kernel" and ident not in kernel_declaration_ids:
            errors.append(f"link {link_id} {side}: unknown kernel declaration {ident!r}")

    for link in links:
        link_id = link.get("id", "<missing>")
        relation = relation_by_id.get(link.get("relation"))
        if relation is None:
            errors.append(f"link {link_id}: unknown relation {link.get('relation')!r}")
            continue
        if link.get("assurance") not in ASSURANCE:
            errors.append(f"link {link_id}: unknown assurance {link.get('assurance')!r}")
        provenance = link.get("provenance", {})
        if provenance.get("method") not in METHODS:
            errors.append(f"link {link_id}: unknown provenance method {provenance.get('method')!r}")
        if not link.get("reason"):
            errors.append(f"link {link_id}: reason is required")
        source = link.get("source", {})
        target = link.get("target", {})
        check_endpoint(source, link_id, "source")
        check_endpoint(target, link_id, "target")
        if source.get("kind") not in relation.get("source_kinds", []):
            errors.append(f"link {link_id}: source kind is outside relation domain")
        if target.get("kind") not in relation.get("target_kinds", []):
            errors.append(f"link {link_id}: target kind is outside relation range")
        if link.get("relation") == "established-by":
            fact = fact_docs.get(source.get("id"))
            credited = operation_ids_for_fact(fact) if fact else set()
            if target.get("id") not in credited:
                errors.append(
                    f"link {link_id}: established-by target is not credited by the fact evidence"
                )
        if link.get("relation") == "formalizes":
            if link.get("assurance") != "human-reviewed":
                errors.append(f"link {link_id}: formalizes assurance must be human-reviewed")
            qualifiers = link.get("qualifiers")
            if not isinstance(qualifiers, dict) or not qualifiers.get("coverage"):
                errors.append(f"link {link_id}: formalizes requires a coverage qualifier")
            if not isinstance(qualifiers, dict) or qualifiers.get("completeness") != "partial":
                errors.append(f"link {link_id}: formalizes completeness must be partial")
            if source.get("kind") == "kernel-declaration":
                declaration = kernel_declarations.get(source.get("id"))
                if declaration is not None:
                    if declaration.get("declaration_kind") != "theorem":
                        errors.append(f"link {link_id}: formalizes kernel source is not a theorem")
                    if declaration.get("axiom_footprint_size") != 0:
                        errors.append(
                            f"link {link_id}: formalizes kernel theorem has a nonempty axiom footprint"
                        )
    return errors, warnings


def operation_ids_for_fact(fact: dict[str, Any]) -> set[str]:
    """Read operation credit from evidence; never trust a sidecar assertion."""
    found = set()
    for evidence in fact.get("evidence", []) or []:
        if not isinstance(evidence, dict):
            continue
        checker = evidence.get("checker_operation")
        if isinstance(checker, dict) and isinstance(checker.get("id"), str):
            found.add(checker["id"])
    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", type=Path, default=DEFAULT_OVERLAY)
    args = parser.parse_args()
    errors: list[str] = []
    doc = load_json(args.path, errors)
    if not errors:
        errors, warnings = validate_document(doc)
    else:
        warnings = []
    for warning in warnings:
        print(f"AUTOGENESIS_KNOWLEDGE_WARNING|{warning}", file=sys.stderr)
    for error in errors:
        print(f"AUTOGENESIS_KNOWLEDGE_ERROR|{error}", file=sys.stderr)
    if errors:
        return 1
    print(
        "AUTOGENESIS_KNOWLEDGE_OK|"
        f"entities={len(doc['entities'])}|links={len(doc['links'])}|"
        f"relations={len(doc['relation_types'])}|sources={len(doc['sources'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
