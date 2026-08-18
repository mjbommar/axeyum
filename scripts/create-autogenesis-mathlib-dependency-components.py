#!/usr/bin/env python3
"""Derive leakage groups from an evaluation-only Mathlib dependency projection."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/mathlib-dependency-source-v1.json"
CANDIDATES = ROOT / "artifacts/autogenesis/mathlib-nat-int-candidates-v1.json"
COMMITTED = ROOT / "artifacts/autogenesis/mathlib-nat-int-dependency-components-v1.json"
EXPECTED_ROW_KEYS = {"module", "name", "theorem_dependencies"}


class DependencyError(RuntimeError):
    """The dependency source or derived component projection is invalid."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise DependencyError(f"{path} is not a JSON object")
    return value


def verify_manifest(manifest: dict[str, Any], candidates: dict[str, Any], root: pathlib.Path = ROOT) -> None:
    unsigned = dict(manifest)
    claimed = unsigned.pop("manifest_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise DependencyError("dependency manifest digest is missing or invalid")
    if manifest.get("schema_version") != 1 or manifest.get("kind") != "axeyum-autogenesis-external-theorem-dependency-source":
        raise DependencyError("dependency manifest schema identity is invalid")
    if manifest.get("candidate_set_sha256") != candidates.get("candidates_sha256"):
        raise DependencyError("dependency manifest names a different candidate population")
    if manifest.get("statement_source_manifest_sha256") != candidates.get("source_manifest_sha256"):
        raise DependencyError("dependency and statement source identities differ")
    source = manifest.get("source")
    if not isinstance(source, dict) or source.get("commit") != "c5ea00351c28e24afc9f0f84379aa41082b1188f" or source.get("tag") != "v4.30.0":
        raise DependencyError("Mathlib dependency source identity changed")
    extractor = manifest.get("extractor")
    if not isinstance(extractor, dict):
        raise DependencyError("dependency extractor identity is absent")
    path = root / str(extractor.get("path"))
    if not path.is_file() or sha256_file(path) != extractor.get("sha256"):
        raise DependencyError("dependency extractor bytes do not match the manifest")
    text = path.read_text()
    for marker in ("theoremInfo.value", "getUsedConstants", '"theorem_dependencies"'):
        if marker not in text:
            raise DependencyError(f"dependency extractor lacks required marker {marker!r}")
    if re.search(r'\("(?:value|proof|tactic_trace|source_location)"\s*,', text):
        raise DependencyError("dependency extractor emits a forbidden proof-bearing field")
    policy = manifest.get("isolation_policy")
    if not isinstance(policy, dict) or "proposers" not in str(policy.get("forbidden_consumers")):
        raise DependencyError("proof-search isolation policy is absent")
    artifact = manifest.get("external_artifact")
    if not isinstance(artifact, dict) or artifact.get("content") != "names-and-direct-theorem-edges-only-ndjson":
        raise DependencyError("external dependency artifact contract is invalid")


def read_rows(path: pathlib.Path, artifact: dict[str, Any]) -> list[dict[str, Any]]:
    if path.stat().st_size != artifact.get("bytes") or sha256_file(path) != artifact.get("sha256"):
        raise DependencyError("external dependency artifact identity changed")
    rows: list[dict[str, Any]] = []
    previous = ""
    with path.open() as source:
        for line_number, line in enumerate(source, start=1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as error:
                raise DependencyError(f"external dependency row {line_number} is malformed: {error}") from error
            if not isinstance(row, dict) or set(row) != EXPECTED_ROW_KEYS:
                raise DependencyError(f"external dependency row {line_number} has forbidden or missing fields")
            name = row.get("name")
            dependencies = row.get("theorem_dependencies")
            if not isinstance(name, str) or not (name.startswith("Nat.") or name.startswith("Int.")):
                raise DependencyError(f"external dependency row {line_number} is outside Nat/Int scope")
            if previous and name <= previous:
                raise DependencyError(f"external dependency row {line_number} is duplicate or out of order")
            if not isinstance(row.get("module"), str) or not row["module"]:
                raise DependencyError(f"external dependency row {line_number} lacks a module")
            if not isinstance(dependencies, list) or not all(isinstance(value, str) and value for value in dependencies):
                raise DependencyError(f"external dependency row {line_number} has malformed dependency names")
            if dependencies != sorted(set(dependencies)) or name in dependencies:
                raise DependencyError(f"external dependency row {line_number} has unsorted, duplicate, or self dependencies")
            rows.append(row)
            previous = name
    if len(rows) != artifact.get("records"):
        raise DependencyError("external dependency artifact record count changed")
    return rows


def assert_acyclic(names: set[str], edges: list[tuple[str, str]]) -> None:
    outgoing: dict[str, list[str]] = {name: [] for name in names}
    for dependent, dependency in edges:
        outgoing[dependent].append(dependency)
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in active:
            raise DependencyError(f"candidate dependency graph contains a cycle at {name}")
        if name in done:
            return
        active.add(name)
        for dependency in outgoing[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)

    for name in sorted(names):
        visit(name)


def build(candidates: dict[str, Any], manifest: dict[str, Any], rows: list[dict[str, Any]]) -> dict[str, Any]:
    candidate_rows = candidates.get("candidates")
    if not isinstance(candidate_rows, list) or not candidate_rows:
        raise DependencyError("candidate population is absent")
    by_name = {row.get("name"): row for row in candidate_rows if isinstance(row, dict)}
    if len(by_name) != len(candidate_rows) or not all(isinstance(name, str) for name in by_name):
        raise DependencyError("candidate names are malformed or duplicate")
    names = set(by_name)
    source_rows = {row["name"]: row for row in rows}
    missing = sorted(names - set(source_rows))
    if missing:
        raise DependencyError(f"dependency source omits {len(missing)} candidates, first={missing[0]}")
    edges = sorted(
        (name, dependency)
        for name in names
        for dependency in source_rows[name]["theorem_dependencies"]
        if dependency in names
    )
    assert_acyclic(names, edges)

    undirected: dict[str, set[str]] = {name: set() for name in names}
    for dependent, dependency in edges:
        undirected[dependent].add(dependency)
        undirected[dependency].add(dependent)
    components: list[list[str]] = []
    seen: set[str] = set()
    for start in sorted(names):
        if start in seen:
            continue
        stack = [start]
        seen.add(start)
        members: list[str] = []
        while stack:
            name = stack.pop()
            members.append(name)
            for adjacent in sorted(undirected[name], reverse=True):
                if adjacent not in seen:
                    seen.add(adjacent)
                    stack.append(adjacent)
        components.append(sorted(members))
    components.sort(key=lambda members: members[0])

    component_rows = []
    for members in components:
        member_set = set(members)
        component_edges = [edge for edge in edges if edge[0] in member_set]
        identity = digest(members)[:16]
        component_rows.append(
            {
                "component_id": f"mathlib-v4.30.0-{identity}",
                "members": [
                    {
                        "candidate_id": by_name[name]["candidate_id"],
                        "module": by_name[name]["module"],
                        "name": name,
                        "theme": by_name[name]["theme"],
                    }
                    for name in members
                ],
                "edges": [
                    {"dependent": dependent, "dependency": dependency}
                    for dependent, dependency in component_edges
                ],
            }
        )

    size_counts = Counter(len(members) for members in components)
    cross_theme = sum(by_name[a]["theme"] != by_name[b]["theme"] for a, b in edges)
    cross_module = sum(by_name[a]["module"] != by_name[b]["module"] for a, b in edges)
    result: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-mathlib-candidate-dependency-components",
        "state": "dependency-metadata-not-frozen-split",
        "dependency_manifest_sha256": manifest["manifest_sha256"],
        "candidate_set_sha256": candidates["candidates_sha256"],
        "edge_semantics": "dependent-directly-uses-dependency; both endpoints are candidates",
        "component_semantics": "weakly-connected-components; assign-whole-component-to-one-future-split",
        "coverage": {
            "candidate_count": len(names),
            "candidate_rows_found": len(names),
            "direct_edges": len(edges),
            "nodes_with_dependencies_in_population": len({a for a, _ in edges}),
            "component_count": len(components),
            "isolated_candidates": sum(len(members) == 1 for members in components),
            "largest_component": max(map(len, components)),
            "component_size_counts": {str(size): count for size, count in sorted(size_counts.items())},
            "cross_theme_edges": cross_theme,
            "cross_module_edges": cross_module,
        },
        "components": component_rows,
        "limitations": [
            "direct proof dependencies outside the 240-candidate population are intentionally projected away",
            "a missing candidate-to-candidate edge can still reflect an extractor or upstream representation limitation",
            "component membership prevents direct dependency leakage but does not replace family, proof-shape, mutation, or longitudinal controls",
            "dependency metadata grants no Axeyum route, outcome, proof-plan, or construction credit",
            "this artifact does not assign train, development, or held-out membership",
        ],
    }
    result["components_sha256"] = digest(result)
    return result


def validate_committed(actual: dict[str, Any], candidates: dict[str, Any], manifest: dict[str, Any]) -> None:
    unsigned = dict(actual)
    claimed = unsigned.pop("components_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise DependencyError("committed component digest is missing or invalid")
    if actual.get("schema_version") != 1 or actual.get("kind") != "axeyum-autogenesis-mathlib-candidate-dependency-components":
        raise DependencyError("committed component schema identity is invalid")
    if actual.get("state") != "dependency-metadata-not-frozen-split":
        raise DependencyError("dependency metadata falsely claims a frozen population")
    if actual.get("candidate_set_sha256") != candidates.get("candidates_sha256"):
        raise DependencyError("committed components name a different candidate population")
    if actual.get("dependency_manifest_sha256") != manifest.get("manifest_sha256"):
        raise DependencyError("committed components name a different dependency source")
    components = actual.get("components")
    if not isinstance(components, list) or not components:
        raise DependencyError("committed components are absent")
    members = [member.get("name") for component in components for member in component.get("members", [])]
    expected = sorted(row["name"] for row in candidates["candidates"])
    if sorted(members) != expected or len(set(members)) != len(expected):
        raise DependencyError("committed components do not partition the candidate population")
    by_name = {row["name"]: row for row in candidates["candidates"]}
    edges: list[tuple[str, str]] = []
    component_sizes: Counter[int] = Counter()
    previous_first = ""
    for component in components:
        component_members = component.get("members")
        component_edges = component.get("edges")
        if not isinstance(component_members, list) or not component_members or not isinstance(component_edges, list):
            raise DependencyError("committed component has malformed members or edges")
        names = [member.get("name") for member in component_members]
        if names != sorted(names) or component.get("component_id") != f"mathlib-v4.30.0-{digest(names)[:16]}":
            raise DependencyError("committed component identity or member order is invalid")
        if previous_first and names[0] <= previous_first:
            raise DependencyError("committed components are out of order")
        previous_first = names[0]
        member_set = set(names)
        component_sizes[len(names)] += 1
        expected_members = [
            {
                "candidate_id": by_name[name]["candidate_id"],
                "module": by_name[name]["module"],
                "name": name,
                "theme": by_name[name]["theme"],
            }
            for name in names
        ]
        if component_members != expected_members:
            raise DependencyError("committed component member metadata is stale")
        local_edges = [(edge.get("dependent"), edge.get("dependency")) for edge in component_edges]
        if local_edges != sorted(set(local_edges)) or any(a not in member_set or b not in member_set for a, b in local_edges):
            raise DependencyError("committed component edges are duplicate, unordered, or cross-component")
        local_graph = {name: set() for name in names}
        for dependent, dependency in local_edges:
            local_graph[dependent].add(dependency)
            local_graph[dependency].add(dependent)
        # The explicit loop avoids accepting a rehashed artifact that splits one
        # dependency component into several rows when the bulk source is absent.
        reached = set()
        stack = [names[0]]
        while stack:
            name = stack.pop()
            if name in reached:
                continue
            reached.add(name)
            stack.extend(sorted(local_graph[name] - reached, reverse=True))
        if reached != member_set:
            raise DependencyError("committed component is not weakly connected")
        edges.extend(local_edges)
    assert_acyclic(set(expected), edges)
    coverage = actual.get("coverage")
    if not isinstance(coverage, dict) or coverage.get("candidate_count") != len(expected):
        raise DependencyError("committed component coverage is invalid")
    if coverage.get("direct_edges") != len(edges) or coverage.get("component_count") != len(components):
        raise DependencyError("committed component counts do not match their rows")
    expected_coverage = {
        "candidate_count": len(expected),
        "candidate_rows_found": len(expected),
        "direct_edges": len(edges),
        "nodes_with_dependencies_in_population": len({a for a, _ in edges}),
        "component_count": len(components),
        "isolated_candidates": component_sizes[1],
        "largest_component": max(component_sizes),
        "component_size_counts": {str(size): count for size, count in sorted(component_sizes.items())},
        "cross_theme_edges": sum(by_name[a]["theme"] != by_name[b]["theme"] for a, b in edges),
        "cross_module_edges": sum(by_name[a]["module"] != by_name[b]["module"] for a, b in edges),
    }
    if coverage != expected_coverage:
        raise DependencyError("committed component coverage does not match the graph")


def check(manifest: dict[str, Any], candidates: dict[str, Any], root: pathlib.Path = ROOT) -> tuple[str, dict[str, Any] | None]:
    verify_manifest(manifest, candidates, root)
    artifact = manifest["external_artifact"]
    storage = pathlib.Path(artifact["storage_root"])
    if not storage.exists():
        return "unavailable", None
    path = storage / artifact["file"]
    if not path.is_file():
        raise DependencyError("external storage is mounted but the dependency artifact is absent")
    return "verified", build(candidates, manifest, read_rows(path, artifact))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        manifest = load_object(MANIFEST)
        candidates = load_object(CANDIDATES)
        external, derived = check(manifest, candidates)
        if args.check:
            committed = load_object(COMMITTED)
            validate_committed(committed, candidates, manifest)
            if derived is not None and committed != derived:
                raise DependencyError("committed component projection is stale or mutated")
        else:
            if derived is None:
                raise DependencyError("cannot generate components without the external dependency artifact")
            COMMITTED.write_text(json.dumps(derived, indent=2, sort_keys=True) + "\n")
        output = derived if derived is not None else load_object(COMMITTED)
        print(
            "AUTOGENESIS_MATHLIB_DEPENDENCIES_OK|"
            f"{output['components_sha256']}|external={external}|"
            f"candidates={output['coverage']['candidate_count']}|"
            f"edges={output['coverage']['direct_edges']}|components={output['coverage']['component_count']}"
        )
    except (OSError, json.JSONDecodeError, DependencyError) as error:
        print(f"autogenesis-mathlib-dependencies: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
