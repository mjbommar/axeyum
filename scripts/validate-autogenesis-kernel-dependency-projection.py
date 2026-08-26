#!/usr/bin/env python3
"""Fail closed on malformed or semantically diluted kernel dependency data."""

from __future__ import annotations

import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
PATH = ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json"
KINDS = {"axiom", "constructor", "definition", "inductive", "recursor", "theorem", "opaque", "quotient"}


def validate(data: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(data, dict) or data.get("schema_version") != 1 or data.get("kind") != "axeyum-kernel-dependency-projection":
        return ["projection identity/version is invalid"]
    declarations = data.get("declarations")
    edges = data.get("direct_theorem_dependency_edges")
    if not isinstance(declarations, list) or not isinstance(edges, list):
        return ["declarations and direct dependency edges must be arrays"]
    by_id: dict[str, dict[str, Any]] = {}
    for declaration in declarations:
        if not isinstance(declaration, dict) or not isinstance(declaration.get("id"), str):
            errors.append("declaration has no string id")
            continue
        ident = declaration["id"]
        if ident in by_id:
            errors.append(f"duplicate declaration {ident}")
            continue
        by_id[ident] = declaration
        kind = declaration.get("declaration_kind")
        if kind not in KINDS:
            errors.append(f"{ident}: unknown declaration kind {kind!r}")
        direct_declarations = declaration.get("direct_declaration_dependencies")
        if not isinstance(direct_declarations, list) or direct_declarations != sorted(set(direct_declarations)):
            errors.append(f"{ident}: direct declaration dependencies must be sorted and unique")
        direct_types = declaration.get("direct_type_dependencies")
        if not isinstance(direct_types, list) or direct_types != sorted(set(direct_types)):
            errors.append(f"{ident}: direct type dependencies must be sorted and unique")
        direct = declaration.get("direct_theorem_dependencies")
        if not isinstance(direct, list) or direct != sorted(set(direct)):
            errors.append(f"{ident}: direct theorem dependencies must be sorted and unique")
        if kind != "theorem" and direct:
            errors.append(f"{ident}: non-theorem declaration carries invented theorem dependencies")
        if isinstance(direct_declarations, list) and isinstance(direct, list):
            if not set(direct).issubset(direct_declarations):
                errors.append(f"{ident}: theorem dependencies are not a subset of direct declarations")
            if ident in direct_declarations:
                errors.append(f"{ident}: direct declaration dependencies contain self-reference")
            if isinstance(direct_types, list) and not set(direct_types).issubset(direct_declarations):
                errors.append(f"{ident}: direct type dependencies are not a subset of direct declarations")
        if not declaration.get("visible_in"):
            errors.append(f"{ident}: declaration has no prelude visibility")
        canonical_type = declaration.get("canonical_type")
        if not isinstance(canonical_type, str) or not canonical_type:
            errors.append(f"{ident}: declaration has no canonical kernel type")
    if len(by_id) < 700:
        errors.append(f"projection covers only {len(by_id)} declarations; wrong or incomplete kernel environment")
    for source, declaration in by_id.items():
        for target in declaration.get("direct_type_dependencies", []):
            if target not in by_id:
                errors.append(f"direct type endpoint missing: {source!r} -> {target!r}")
        for target in declaration.get("direct_declaration_dependencies", []):
            if target not in by_id:
                errors.append(f"direct declaration endpoint missing: {source!r} -> {target!r}")
    expected = {
        (source, target)
        for source, declaration in by_id.items()
        for target in declaration.get("direct_theorem_dependencies", [])
    }
    actual: set[tuple[str, str]] = set()
    for edge in edges:
        if not isinstance(edge, dict) or edge.get("relation") != "direct-theorem-depends-on":
            errors.append("edge is not a direct theorem dependency")
            continue
        source, target = edge.get("source"), edge.get("target")
        pair = (source, target)
        if pair in actual:
            errors.append(f"duplicate dependency edge {source!r} -> {target!r}")
        actual.add(pair)
        if source not in by_id or target not in by_id:
            errors.append(f"edge endpoint missing: {source!r} -> {target!r}")
        elif by_id[source].get("declaration_kind") != "theorem" or by_id[target].get("declaration_kind") != "theorem":
            errors.append(f"edge is not theorem -> theorem: {source!r} -> {target!r}")
    if actual != expected:
        errors.append("edge list does not exactly match declaration direct-dependency fields")
    census = data.get("census", {})
    if census.get("declarations") != len(by_id) or census.get("direct_theorem_dependency_edges") != len(actual):
        errors.append("census does not match projection content")
    return errors


def main() -> int:
    try:
        data = json.loads(PATH.read_text())
    except (OSError, json.JSONDecodeError) as error:
        print(f"AUTOGENESIS_KERNEL_PROJECTION_ERROR|cannot read projection: {error}", file=sys.stderr)
        return 1
    errors = validate(data)
    for error in errors:
        print(f"AUTOGENESIS_KERNEL_PROJECTION_ERROR|{error}", file=sys.stderr)
    if errors:
        return 1
    census = data["census"]
    print(f"AUTOGENESIS_KERNEL_PROJECTION_OK|declarations={census['declarations']}|edges={census['direct_theorem_dependency_edges']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
