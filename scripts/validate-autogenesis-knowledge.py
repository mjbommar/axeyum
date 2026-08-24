#!/usr/bin/env python3
"""Validate the additive Autogenesis knowledge overlay.

The overlay deliberately does not modify facts, operations, or external source
graphs. This validator checks the relational contract that JSON Schema cannot:
unique identities, typed endpoints, local resolution, pinned external
revisions, and relation-domain/range compatibility. The sibling
``../math-education`` checkout is optional; when present at the pinned commit,
referenced concept and technique files are also resolved.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
SCHEMA = ROOT / "artifacts/ontology/autogenesis-knowledge-overlay.schema.json"

TOP_KEYS = {
    "schema_version", "kind", "sources", "namespaces", "relation_types",
    "entities", "links",
}
ENTITY_KINDS = {
    "concept", "encounter", "technique", "curriculum-node", "fact",
    "kernel-declaration", "external-declaration", "operation", "producer",
    "checker", "capability", "obstruction", "episode", "evidence-artifact",
    "representation",
}
ASSURANCE = {
    "formal-derived", "independently-checked", "registry-derived",
    "mechanically-observed", "human-reviewed", "heuristic", "proposed",
}
METHODS = {
    "kernel-derived", "checker-derived", "registry-derived",
    "mechanically-observed", "human-reviewed", "heuristic", "proposed",
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


def git_head(path: Path) -> str | None:
    try:
        return subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def math_education_resolves(root: Path, ident: str) -> bool:
    stem = ident.split("@", 1)[0]
    if stem.startswith("C:"):
        return (root / "graph/concepts" / f"{stem[2:]}.md").is_file()
    if stem.startswith("TQ:"):
        return (root / "graph/techniques" / f"{stem[3:]}.md").is_file()
    return False


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
        ("sources", sources), ("namespaces", namespaces),
        ("relation_types", relations), ("entities", entities), ("links", links),
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
            errors.append(f"namespace {namespace['id']}: unknown source_id {namespace.get('source_id')!r}")
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
    operation_ids = {
        row.get("id") for row in (operation_doc or {}).get("operations", [])
    }

    external_source = source_by_id.get("math-education", {})
    external_root = root.parent / "math-education"
    external_available = external_root.is_dir()
    external_revision = external_source.get("revision")
    if external_available:
        actual = git_head(external_root)
        if actual != external_revision:
            warnings.append(
                "math-education checkout is present but not at the overlay pin; "
                f"skipping live endpoint resolution (expected {external_revision}, got {actual})"
            )
            external_available = False

    def check_endpoint(endpoint: dict[str, Any], link_id: str, side: str) -> None:
        namespace_id = endpoint.get("namespace")
        namespace = ns_by_id.get(namespace_id)
        if namespace is None:
            errors.append(f"link {link_id} {side}: unknown namespace {namespace_id!r}")
            return
        kind = endpoint.get("kind")
        ident = endpoint.get("id")
        if kind not in namespace.get("entity_kinds", []):
            errors.append(f"link {link_id} {side}: kind {kind!r} not allowed by namespace {namespace_id}")
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
            candidates = list((root / "artifacts/facts").glob("*.json"))
            if not any(load_json(path, errors).get("id") == ident for path in candidates):
                errors.append(f"link {link_id} {side}: unknown fact {ident!r}")
        elif namespace_id == "axeyum-operation" and ident not in operation_ids:
            errors.append(f"link {link_id} {side}: unknown operation {ident!r}")
        elif resolution == "external-pinned":
            source = source_by_id.get(namespace.get("source_id"), {})
            expected = source.get("revision")
            if endpoint.get("source_revision") != expected:
                errors.append(
                    f"link {link_id} {side}: external endpoint must carry source revision {expected}"
                )
            if external_available and namespace_id == "math-education" and not math_education_resolves(external_root, ident):
                errors.append(f"link {link_id} {side}: unresolved pinned math-education id {ident!r}")

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

    return errors, warnings


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
