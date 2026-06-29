#!/usr/bin/env python3
"""Validate foundational math example-pack structure.

Usage:
  python3 scripts/validate-foundational-example-pack.py
  python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
"""

from __future__ import annotations

import json
import re
import sys
from collections import deque
from fractions import Fraction
from itertools import combinations, product
from math import gcd
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "foundational-example-pack.schema.json"
CONCEPTS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
DEFAULT_ROOT = ROOT / "artifacts" / "examples" / "math"
REQUIRED_FILES = {"README.md", "metadata.json", "model.md", "checks.md", "expected.json"}

CLAIM_STATUS = {"template", "planned", "witnessed", "checked", "proof-gap"}
TRUST_STATUS = {"template", "planned", "replay-only", "checked-evidence", "proof-gap", "numerical"}
EXPECTED_RESULT = {"sat", "unsat", "unknown", "not-run"}
PROOF_STATUS = {"template", "checked", "replay-only", "proof-gap", "lean-horizon", "not-required"}


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


def check_source(context: str, source: str) -> None:
    if source.startswith(("http://", "https://")):
        return
    path_part = source.split("#", 1)[0]
    if not path_part:
        return
    if not (ROOT / path_part).exists():
        fail(f"{context} references missing local source: {source}")


def concept_indexes() -> tuple[set[str], set[str], set[str]]:
    data = load_json(CONCEPTS)
    rows = data["rows"]
    concept_ids = {row["id"] for row in rows}
    field_ids = {field_id for row in rows for field_id in row["field_ids"]}
    curriculum_nodes = {
        row["curriculum_node"]
        for row in rows
        if row["kind"] == "curriculum-node" and row["curriculum_node"]
    }
    return concept_ids, field_ids, curriculum_nodes


def validate_metadata(
    pack_dir: Path,
    metadata: dict[str, Any],
    concept_ids: set[str],
    field_ids: set[str],
    curriculum_nodes: set[str],
) -> None:
    require_keys(
        "metadata",
        metadata,
        {
            "schema_version",
            "id",
            "title",
            "domain",
            "claim_status",
            "trust_status",
            "concept_ids",
            "field_ids",
            "curriculum_nodes",
            "axeyum_fragments",
            "validator_command",
            "source_refs",
            "expected_results",
            "graduation_criteria",
        },
    )
    if metadata["schema_version"] != 1:
        fail("metadata.schema_version must be 1")
    if metadata["id"] != pack_dir.name:
        fail(f"metadata.id must match directory name {pack_dir.name!r}")
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", metadata["id"]):
        fail("metadata.id must be lowercase kebab case")
    require_string("metadata.title", metadata["title"])
    if metadata["domain"] not in {"mathematics", "computer-science", "logic", "statistics"}:
        fail(f"metadata.domain invalid: {metadata['domain']!r}")
    if metadata["claim_status"] not in CLAIM_STATUS:
        fail(f"metadata.claim_status invalid: {metadata['claim_status']!r}")
    if metadata["trust_status"] not in TRUST_STATUS:
        fail(f"metadata.trust_status invalid: {metadata['trust_status']!r}")
    pack_concepts = set(require_string_list("metadata.concept_ids", metadata["concept_ids"]))
    missing_concepts = sorted(pack_concepts - concept_ids)
    if missing_concepts:
        fail(f"metadata.concept_ids references unknown concepts: {', '.join(missing_concepts)}")
    pack_fields = set(require_string_list("metadata.field_ids", metadata["field_ids"]))
    missing_fields = sorted(pack_fields - field_ids)
    if missing_fields:
        fail(f"metadata.field_ids references unknown fields: {', '.join(missing_fields)}")
    nodes = set(require_string_list("metadata.curriculum_nodes", metadata["curriculum_nodes"], nonempty=False))
    missing_nodes = sorted(nodes - curriculum_nodes)
    if missing_nodes:
        fail(f"metadata.curriculum_nodes references unknown nodes: {', '.join(missing_nodes)}")
    require_string_list("metadata.axeyum_fragments", metadata["axeyum_fragments"])
    require_string("metadata.validator_command", metadata["validator_command"])
    sources = require_string_list("metadata.source_refs", metadata["source_refs"])
    for source in sources:
        check_source("metadata.source_refs", source)
    expected_ids = require_string_list(
        "metadata.expected_results",
        metadata["expected_results"],
        nonempty=metadata["claim_status"] != "template",
    )
    if metadata["claim_status"] == "template" and metadata["trust_status"] != "template":
        fail("template claim_status requires template trust_status")
    criteria = require_string_list("metadata.graduation_criteria", metadata["graduation_criteria"])
    if metadata["claim_status"] != "template" and not criteria:
        fail("non-template packs require graduation criteria")
    return expected_ids


def validate_expected(metadata: dict[str, Any], expected: dict[str, Any], expected_ids: list[str]) -> None:
    require_keys("expected", expected, {"schema_version", "pack_id", "witnesses", "checks"})
    if expected["schema_version"] != 1:
        fail("expected.schema_version must be 1")
    if expected["pack_id"] != metadata["id"]:
        fail("expected.pack_id must match metadata.id")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(f"witnesses[{index}]", witness, {"id", "description", "values"})
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        require_string(f"witnesses[{index}].description", witness["description"])
        if not isinstance(witness["values"], dict):
            fail(f"witnesses[{index}].values must be an object")

    check_ids: set[str] = set()
    for index, check in enumerate(expected["checks"]):
        require_keys(
            f"checks[{index}]",
            check,
            {"id", "claim", "expected_result", "validation", "proof_status", "notes"},
        )
        check_id = check["id"]
        if check_id in check_ids:
            fail(f"duplicate check id {check_id}")
        check_ids.add(check_id)
        require_string(f"checks[{index}].claim", check["claim"])
        if check["expected_result"] not in EXPECTED_RESULT:
            fail(f"{check_id}.expected_result invalid: {check['expected_result']!r}")
        require_string(f"checks[{index}].validation", check["validation"])
        if check["proof_status"] not in PROOF_STATUS:
            fail(f"{check_id}.proof_status invalid: {check['proof_status']!r}")
        for witness_id in check.get("witnesses", []):
            if witness_id not in witness_ids:
                fail(f"{check_id} references unknown witness {witness_id}")
        if "data" in check and not isinstance(check["data"], dict):
            fail(f"{check_id}.data must be an object when present")
        require_string(f"checks[{index}].notes", check["notes"])

    if set(expected_ids) != check_ids:
        fail(
            "metadata.expected_results must match expected.checks ids: "
            f"metadata={sorted(expected_ids)} expected={sorted(check_ids)}"
        )
    validate_pack_semantics(metadata, expected)


def require_int(context: str, value: Any) -> int:
    if not isinstance(value, int):
        fail(f"{context} must be an integer")
    return value


def witness_by_id(expected: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {witness["id"]: witness for witness in expected["witnesses"]}


def single_witness_values(check: dict[str, Any], witnesses: dict[str, dict[str, Any]]) -> dict[str, Any]:
    ids = check.get("witnesses", [])
    if len(ids) != 1:
        fail(f"{check['id']} must reference exactly one witness")
    values = witnesses[ids[0]]["values"]
    if not isinstance(values, dict):
        fail(f"{check['id']} witness values must be an object")
    return values


def require_set_values(context: str, values: dict[str, Any]) -> tuple[set[str], set[str], set[str], set[str]]:
    universe = require_string_list(f"{context}.universe", values.get("universe"))
    universe_set = set(universe)

    def read_subset(name: str) -> set[str]:
        items = require_string_list(f"{context}.{name}", values.get(name), nonempty=False)
        extra = sorted(set(items) - universe_set)
        if extra:
            fail(f"{context}.{name} contains elements outside universe: {extra}")
        return set(items)

    return universe_set, read_subset("A"), read_subset("B"), read_subset("C")


def validate_finite_sets(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    identity = checks["union-intersection-identity"]
    if identity["expected_result"] != "sat":
        fail("union-intersection-identity must expect sat")
    values = single_witness_values(identity, witnesses)
    _, a_set, b_set, c_set = require_set_values("union-intersection identity", values)
    left = a_set | (b_set & c_set)
    right = (a_set | b_set) & (a_set | c_set)
    if left != right:
        fail("union-intersection identity witness does not satisfy distributivity")

    transitivity = checks["subset-transitivity-witness"]
    if transitivity["expected_result"] != "sat":
        fail("subset-transitivity-witness must expect sat")
    values = single_witness_values(transitivity, witnesses)
    _, a_set, b_set, c_set = require_set_values("subset transitivity", values)
    if not (a_set <= b_set and b_set <= c_set and a_set <= c_set):
        fail("subset transitivity witness does not satisfy A <= B <= C")

    bad_identity = checks["distributive-law-counterexample-rejected"]
    if bad_identity["expected_result"] != "unsat":
        fail("distributive-law-counterexample-rejected must expect unsat")
    values = single_witness_values(bad_identity, witnesses)
    _, a_set, b_set, c_set = require_set_values("bad distributive identity", values)
    left = a_set & (b_set | c_set)
    right = (a_set & b_set) | c_set
    if left == right:
        fail("bad distributive identity unexpectedly holds for the fixed witness")


def require_pair_set(
    context: str,
    value: Any,
    left_values: set[str],
    right_values: set[str],
) -> set[tuple[str, str]]:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    pairs: set[tuple[str, str]] = set()
    for index, pair in enumerate(value):
        if not isinstance(pair, list) or len(pair) != 2:
            fail(f"{context}[{index}] must be a two-element list")
        left, right = pair
        require_string(f"{context}[{index}][0]", left)
        require_string(f"{context}[{index}][1]", right)
        if left not in left_values:
            fail(f"{context}[{index}][0] references missing left element {left!r}")
        if right not in right_values:
            fail(f"{context}[{index}][1] references missing right element {right!r}")
        normalized = (left, right)
        if normalized in pairs:
            fail(f"{context} repeats pair {normalized}")
        pairs.add(normalized)
    return pairs


def require_relation_data(context: str, values: dict[str, Any]) -> tuple[list[str], set[tuple[str, str]]]:
    elements = require_string_list(f"{context}.elements", values.get("elements"))
    element_set = set(elements)
    pairs = require_pair_set(f"{context}.pairs", values.get("pairs"), element_set, element_set)
    return elements, pairs


def is_reflexive(elements: list[str], pairs: set[tuple[str, str]]) -> bool:
    return all((element, element) in pairs for element in elements)


def is_antisymmetric(pairs: set[tuple[str, str]]) -> bool:
    return all(left == right or (right, left) not in pairs for left, right in pairs)


def is_transitive(pairs: set[tuple[str, str]]) -> bool:
    return all(
        (left, right_2) in pairs
        for left, right_1 in pairs
        for left_2, right_2 in pairs
        if right_1 == left_2
    )


def require_function_graph_data(
    context: str,
    values: dict[str, Any],
) -> tuple[list[str], list[str], set[tuple[str, str]]]:
    domain = require_string_list(f"{context}.domain", values.get("domain"))
    codomain = require_string_list(f"{context}.codomain", values.get("codomain"))
    pairs = require_pair_set(f"{context}.pairs", values.get("pairs"), set(domain), set(codomain))
    return domain, codomain, pairs


def outputs_by_input(domain: list[str], pairs: set[tuple[str, str]]) -> dict[str, set[str]]:
    return {
        item: {output for input_item, output in pairs if input_item == item}
        for item in domain
    }


def is_total_function(domain: list[str], pairs: set[tuple[str, str]]) -> bool:
    outputs = outputs_by_input(domain, pairs)
    return all(outputs[item] for item in domain)


def is_single_valued(domain: list[str], pairs: set[tuple[str, str]]) -> bool:
    outputs = outputs_by_input(domain, pairs)
    return all(len(outputs[item]) <= 1 for item in domain)


def function_mapping(domain: list[str], pairs: set[tuple[str, str]]) -> dict[str, str]:
    outputs = outputs_by_input(domain, pairs)
    if not all(len(outputs[item]) == 1 for item in domain):
        fail("function graph must be total and single-valued before extracting a mapping")
    return {item: next(iter(outputs[item])) for item in domain}


def validate_relations_functions(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    order = checks["partial-order-witness"]
    if order["expected_result"] != "sat":
        fail("partial-order-witness must expect sat")
    values = single_witness_values(order, witnesses)
    elements, pairs = require_relation_data("partial order", values)
    if not is_reflexive(elements, pairs):
        fail("partial-order-witness relation is not reflexive")
    if not is_antisymmetric(pairs):
        fail("partial-order-witness relation is not antisymmetric")
    if not is_transitive(pairs):
        fail("partial-order-witness relation is not transitive")

    bijection = checks["bijection-table-witness"]
    if bijection["expected_result"] != "sat":
        fail("bijection-table-witness must expect sat")
    values = single_witness_values(bijection, witnesses)
    domain, codomain, pairs = require_function_graph_data("bijection table", values)
    if not is_total_function(domain, pairs):
        fail("bijection-table-witness graph is not total")
    if not is_single_valued(domain, pairs):
        fail("bijection-table-witness graph is not single-valued")
    mapping = function_mapping(domain, pairs)
    images = list(mapping.values())
    if len(set(images)) != len(images):
        fail("bijection-table-witness graph is not injective")
    if set(images) != set(codomain):
        fail("bijection-table-witness graph is not surjective")

    bad_function = checks["non-function-rejected"]
    if bad_function["expected_result"] != "unsat":
        fail("non-function-rejected must expect unsat")
    values = single_witness_values(bad_function, witnesses)
    domain, _, pairs = require_function_graph_data("non-function graph", values)
    if is_single_valued(domain, pairs):
        fail("non-function-rejected graph unexpectedly is single-valued")
    if is_total_function(domain, pairs) and is_single_valued(domain, pairs):
        fail("non-function-rejected graph unexpectedly is a function")


def require_graph_data(context: str, values: dict[str, Any]) -> tuple[list[str], list[tuple[str, str]], list[str]]:
    vertices = require_string_list(f"{context}.vertices", values.get("vertices"))
    colors = require_string_list(f"{context}.colors", values.get("colors"))
    edge_values = values.get("edges")
    if not isinstance(edge_values, list):
        fail(f"{context}.edges must be a list")
    vertex_set = set(vertices)
    edges: list[tuple[str, str]] = []
    seen_edges: set[tuple[str, str]] = set()
    for index, edge in enumerate(edge_values):
        if not isinstance(edge, list) or len(edge) != 2:
            fail(f"{context}.edges[{index}] must be a two-element list")
        left, right = edge
        require_string(f"{context}.edges[{index}][0]", left)
        require_string(f"{context}.edges[{index}][1]", right)
        if left == right:
            fail(f"{context}.edges[{index}] must not be a self-loop")
        if left not in vertex_set or right not in vertex_set:
            fail(f"{context}.edges[{index}] references a missing vertex")
        normalized = tuple(sorted((left, right)))
        if normalized in seen_edges:
            fail(f"{context}.edges repeats undirected edge {normalized}")
        seen_edges.add(normalized)
        edges.append((left, right))
    return vertices, edges, colors


def require_coloring_assignment(
    context: str,
    values: dict[str, Any],
    vertices: list[str],
    colors: list[str],
) -> dict[str, str]:
    assignment = values.get("assignment")
    if not isinstance(assignment, dict):
        fail(f"{context}.assignment must be an object")
    vertex_set = set(vertices)
    color_set = set(colors)
    if set(assignment) != vertex_set:
        missing = sorted(vertex_set - set(assignment))
        extra = sorted(set(assignment) - vertex_set)
        fail(f"{context}.assignment must cover exactly the graph vertices; missing={missing} extra={extra}")
    for vertex, color in assignment.items():
        require_string(f"{context}.assignment key", vertex)
        require_string(f"{context}.assignment[{vertex}]", color)
        if color not in color_set:
            fail(f"{context}.assignment[{vertex}] uses unknown color {color!r}")
    return assignment


def is_proper_coloring(edges: list[tuple[str, str]], assignment: dict[str, str]) -> bool:
    return all(assignment[left] != assignment[right] for left, right in edges)


def has_proper_coloring(vertices: list[str], edges: list[tuple[str, str]], colors: list[str]) -> bool:
    for color_tuple in product(colors, repeat=len(vertices)):
        assignment = dict(zip(vertices, color_tuple))
        if is_proper_coloring(edges, assignment):
            return True
    return False


def validate_graph_coloring(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    triangle = checks["triangle-3-coloring-witness"]
    if triangle["expected_result"] != "sat":
        fail("triangle-3-coloring-witness must expect sat")
    values = single_witness_values(triangle, witnesses)
    vertices, edges, colors = require_graph_data("triangle coloring", values)
    if len(colors) != 3:
        fail("triangle-3-coloring-witness must use three colors")
    assignment = require_coloring_assignment("triangle coloring", values, vertices, colors)
    if not is_proper_coloring(edges, assignment):
        fail("triangle-3-coloring witness is not a proper coloring")

    bad_edge = checks["bad-edge-coloring-rejected"]
    if bad_edge["expected_result"] != "unsat":
        fail("bad-edge-coloring-rejected must expect unsat")
    values = single_witness_values(bad_edge, witnesses)
    vertices, edges, colors = require_graph_data("bad edge coloring", values)
    assignment = require_coloring_assignment("bad edge coloring", values, vertices, colors)
    if is_proper_coloring(edges, assignment):
        fail("bad-edge-coloring-rejected witness unexpectedly is a proper coloring")

    noncolorable = checks["triangle-not-2-colorable"]
    if noncolorable["expected_result"] != "unsat":
        fail("triangle-not-2-colorable must expect unsat")
    data = noncolorable.get("data", {})
    vertices, edges, colors = require_graph_data("triangle-not-2-colorable data", data)
    if len(vertices) != 3 or len(edges) != 3 or len(colors) != 2:
        fail("triangle-not-2-colorable must use K3 with exactly two colors")
    if has_proper_coloring(vertices, edges, colors):
        fail("triangle-not-2-colorable found a proper 2-coloring unexpectedly")


def require_finite_graph(context: str, values: dict[str, Any]) -> tuple[list[str], list[tuple[str, str]]]:
    vertices = require_string_list(f"{context}.vertices", values.get("vertices"))
    edge_values = values.get("edges")
    if not isinstance(edge_values, list):
        fail(f"{context}.edges must be a list")
    vertex_set = set(vertices)
    edges: list[tuple[str, str]] = []
    seen_edges: set[tuple[str, str]] = set()
    for index, edge in enumerate(edge_values):
        if not isinstance(edge, list) or len(edge) != 2:
            fail(f"{context}.edges[{index}] must be a two-element list")
        left, right = edge
        require_string(f"{context}.edges[{index}][0]", left)
        require_string(f"{context}.edges[{index}][1]", right)
        if left == right:
            fail(f"{context}.edges[{index}] must not be a self-loop")
        if left not in vertex_set or right not in vertex_set:
            fail(f"{context}.edges[{index}] references a missing vertex")
        normalized = tuple(sorted((left, right)))
        if normalized in seen_edges:
            fail(f"{context}.edges repeats undirected edge {normalized}")
        seen_edges.add(normalized)
        edges.append((left, right))
    return vertices, edges


def require_graph_vertex(context: str, value: Any, vertices: list[str]) -> str:
    require_string(context, value)
    if value not in set(vertices):
        fail(f"{context} references a missing vertex")
    return value


def require_graph_path(context: str, value: Any, vertices: list[str]) -> list[str]:
    path = require_string_list(context, value)
    vertex_set = set(vertices)
    for vertex in path:
        if vertex not in vertex_set:
            fail(f"{context} references missing vertex {vertex!r}")
    return path


def graph_edge_set(edges: list[tuple[str, str]]) -> set[tuple[str, str]]:
    return {tuple(sorted(edge)) for edge in edges}


def graph_adjacency(vertices: list[str], edges: list[tuple[str, str]]) -> dict[str, list[str]]:
    order = {vertex: index for index, vertex in enumerate(vertices)}
    adjacency = {vertex: [] for vertex in vertices}
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    for vertex in vertices:
        adjacency[vertex].sort(key=lambda item: order[item])
    return adjacency


def shortest_distances(
    vertices: list[str],
    edges: list[tuple[str, str]],
    source: str,
) -> dict[str, int]:
    adjacency = graph_adjacency(vertices, edges)
    distances = {source: 0}
    queue: deque[str] = deque([source])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if neighbor not in distances:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    return distances


def deterministic_dfs_order(vertices: list[str], edges: list[tuple[str, str]], start: str) -> list[str]:
    adjacency = graph_adjacency(vertices, edges)
    seen: set[str] = set()
    order: list[str] = []

    def visit(vertex: str) -> None:
        seen.add(vertex)
        order.append(vertex)
        for neighbor in adjacency[vertex]:
            if neighbor not in seen:
                visit(neighbor)

    visit(start)
    return order


def path_is_valid(path: list[str], edges: list[tuple[str, str]]) -> bool:
    edge_set = graph_edge_set(edges)
    return all(tuple(sorted((left, right))) in edge_set for left, right in zip(path, path[1:]))


def require_distance_map(context: str, value: Any, vertices: list[str]) -> dict[str, int]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    vertex_set = set(vertices)
    if set(value) != vertex_set:
        missing = sorted(vertex_set - set(value))
        extra = sorted(set(value) - vertex_set)
        fail(f"{context} must cover exactly the graph vertices; missing={missing} extra={extra}")
    distances: dict[str, int] = {}
    for vertex in vertices:
        distance = require_int(f"{context}.{vertex}", value[vertex])
        if distance < 0:
            fail(f"{context}.{vertex} must be nonnegative")
        distances[vertex] = distance
    return distances


def require_cut_edges(
    context: str,
    value: Any,
    vertices: list[str],
    graph_edges: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    cut_edges = require_finite_graph(context, {"vertices": vertices, "edges": value})[1]
    graph_edge_set_value = graph_edge_set(graph_edges)
    for edge in cut_edges:
        if tuple(sorted(edge)) not in graph_edge_set_value:
            fail(f"{context} contains an edge that is not in the graph")
    return cut_edges


def remove_edges(
    edges: list[tuple[str, str]],
    removed: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    removed_set = graph_edge_set(removed)
    return [edge for edge in edges if tuple(sorted(edge)) not in removed_set]


def validate_graph_reachability(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    bfs = checks["bfs-shortest-distance-witness"]
    if bfs["expected_result"] != "sat" or bfs.get("proof_status") != "checked":
        fail("bfs-shortest-distance-witness must be a checked sat row")
    values = single_witness_values(bfs, witnesses)
    vertices, edges = require_finite_graph("bfs shortest path", values)
    source = require_graph_vertex("bfs shortest path source", values.get("source"), vertices)
    target = require_graph_vertex("bfs shortest path target", values.get("target"), vertices)
    path = require_graph_path("bfs shortest path path", values.get("path"), vertices)
    if path[0] != source or path[-1] != target:
        fail("bfs-shortest-distance-witness path endpoints do not match source/target")
    if not path_is_valid(path, edges):
        fail("bfs-shortest-distance-witness path contains a non-edge")
    claimed_distance = require_int("bfs shortest path distance", values.get("distance"))
    if claimed_distance < 0:
        fail("bfs shortest path distance must be nonnegative")
    if len(path) - 1 != claimed_distance:
        fail("bfs-shortest-distance-witness distance does not match path length")
    computed_distances = shortest_distances(vertices, edges, source)
    if computed_distances.get(target) != claimed_distance:
        fail("bfs-shortest-distance-witness distance is not shortest")
    listed_distances = require_distance_map("bfs shortest path distances", values.get("distances"), vertices)
    if listed_distances != computed_distances:
        fail("bfs-shortest-distance-witness distance map does not match BFS")

    dfs = checks["dfs-long-tail-order-replay"]
    if dfs["expected_result"] != "sat" or dfs.get("proof_status") != "checked":
        fail("dfs-long-tail-order-replay must be a checked sat row")
    values = single_witness_values(dfs, witnesses)
    vertices, edges = require_finite_graph("dfs long-tail order", values)
    start = require_graph_vertex("dfs long-tail start", values.get("start"), vertices)
    target = require_graph_vertex("dfs long-tail target", values.get("target"), vertices)
    order = require_string_list("dfs long-tail order", values.get("order"))
    expected_order = deterministic_dfs_order(vertices, edges, start)
    if order != expected_order:
        fail("dfs-long-tail-order-replay order does not match deterministic DFS")
    if target not in order:
        fail("dfs-long-tail-order-replay target is not reached")
    target_index = require_int("dfs target_discovery_index", values.get("target_discovery_index"))
    if target_index != order.index(target):
        fail("dfs-long-tail-order-replay target discovery index is wrong")
    distances = shortest_distances(vertices, edges, start)
    if target not in distances:
        fail("dfs-long-tail-order-replay target must be BFS-reachable")
    if target_index <= distances[target]:
        fail("dfs-long-tail-order-replay must witness DFS doing more work than BFS distance")

    unreachable = checks["disconnected-no-path"]
    if unreachable["expected_result"] != "unsat" or unreachable.get("proof_status") != "checked":
        fail("disconnected-no-path must be a checked unsat row")
    data = unreachable.get("data", {})
    vertices, edges = require_finite_graph("disconnected no path", data)
    source = require_graph_vertex("disconnected source", data.get("source"), vertices)
    target = require_graph_vertex("disconnected target", data.get("target"), vertices)
    if target in shortest_distances(vertices, edges, source):
        fail("disconnected-no-path unexpectedly has a source-to-target path")

    cut = checks["edge-cut-separates"]
    if cut["expected_result"] != "sat" or cut.get("proof_status") != "checked":
        fail("edge-cut-separates must be a checked sat row")
    data = cut.get("data", {})
    vertices, edges = require_finite_graph("edge cut", data)
    source = require_graph_vertex("edge cut source", data.get("source"), vertices)
    target = require_graph_vertex("edge cut target", data.get("target"), vertices)
    cut_edges = require_cut_edges("edge cut cut_edges", data.get("cut_edges"), vertices, edges)
    if target not in shortest_distances(vertices, edges, source):
        fail("edge-cut-separates original graph must have an s-t path")
    if target in shortest_distances(vertices, remove_edges(edges, cut_edges), source):
        fail("edge-cut-separates cut edges do not separate source and target")


def require_graph_edge_list(
    context: str,
    value: Any,
    vertices: list[str],
    graph_edges: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    vertex_set = set(vertices)
    available_edges = graph_edge_set(graph_edges)
    parsed_edges: list[tuple[str, str]] = []
    seen_edges: set[tuple[str, str]] = set()
    for index, edge in enumerate(value):
        if not isinstance(edge, list) or len(edge) != 2:
            fail(f"{context}[{index}] must be a two-element list")
        left, right = edge
        require_string(f"{context}[{index}][0]", left)
        require_string(f"{context}[{index}][1]", right)
        if left == right:
            fail(f"{context}[{index}] must not be a self-loop")
        if left not in vertex_set or right not in vertex_set:
            fail(f"{context}[{index}] references a missing vertex")
        normalized = tuple(sorted((left, right)))
        if normalized not in available_edges:
            fail(f"{context}[{index}] is not an edge of the graph")
        if normalized in seen_edges:
            fail(f"{context} repeats edge {normalized}")
        seen_edges.add(normalized)
        parsed_edges.append((left, right))
    return parsed_edges


def is_matching(edge_list: list[tuple[str, str]]) -> bool:
    used: set[str] = set()
    for left, right in edge_list:
        if left in used or right in used:
            return False
        used.add(left)
        used.add(right)
    return True


def covered_vertices(edge_list: list[tuple[str, str]]) -> set[str]:
    covered: set[str] = set()
    for left, right in edge_list:
        covered.add(left)
        covered.add(right)
    return covered


def enumerate_matchings(edges: list[tuple[str, str]]) -> list[list[tuple[str, str]]]:
    matchings: list[list[tuple[str, str]]] = []

    def visit(index: int, current: list[tuple[str, str]], used: set[str]) -> None:
        if index == len(edges):
            matchings.append(list(current))
            return
        visit(index + 1, current, used)
        left, right = edges[index]
        if left not in used and right not in used:
            current.append((left, right))
            visit(index + 1, current, used | {left, right})
            current.pop()

    visit(0, [], set())
    return matchings


def maximum_matching_size(edges: list[tuple[str, str]]) -> int:
    return max(len(matching) for matching in enumerate_matchings(edges))


def has_perfect_matching(vertices: list[str], edges: list[tuple[str, str]]) -> bool:
    vertex_set = set(vertices)
    return any(covered_vertices(matching) == vertex_set for matching in enumerate_matchings(edges))


def normalized_edge_set(edges: list[tuple[str, str]]) -> set[tuple[str, str]]:
    return {tuple(sorted(edge)) for edge in edges}


def validate_augmenting_path(
    context: str,
    graph_edges: list[tuple[str, str]],
    current_matching: list[tuple[str, str]],
    path: list[str],
    improved_matching: list[tuple[str, str]],
) -> None:
    if not is_matching(current_matching):
        fail(f"{context} current matching is not a matching")
    if not is_matching(improved_matching):
        fail(f"{context} improved matching is not a matching")
    if len(path) < 2:
        fail(f"{context} augmenting path must contain at least two vertices")
    if len(set(path)) != len(path):
        fail(f"{context} augmenting path must be simple")
    if not path_is_valid(path, graph_edges):
        fail(f"{context} augmenting path contains a non-edge")

    current_set = normalized_edge_set(current_matching)
    path_edges = [
        tuple(sorted((left, right)))
        for left, right in zip(path, path[1:])
    ]
    if len(path_edges) % 2 == 0:
        fail(f"{context} augmenting path must have odd edge length")
    current_covered = covered_vertices(current_matching)
    if path[0] in current_covered or path[-1] in current_covered:
        fail(f"{context} augmenting path endpoints must be unmatched")
    for index, edge in enumerate(path_edges):
        edge_is_matched = edge in current_set
        if index % 2 == 0 and edge_is_matched:
            fail(f"{context} even path edge {index} must be unmatched")
        if index % 2 == 1 and not edge_is_matched:
            fail(f"{context} odd path edge {index} must be matched")
    flipped = current_set ^ set(path_edges)
    if flipped != normalized_edge_set(improved_matching):
        fail(f"{context} improved matching is not the path flip")
    if len(improved_matching) != len(current_matching) + 1:
        fail(f"{context} improved matching must increase size by one")
    if not normalized_edge_set(improved_matching).issubset(graph_edge_set(graph_edges)):
        fail(f"{context} improved matching contains an edge outside the graph")


def validate_graph_matching(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    size_two = checks["matching-size-two-witness"]
    if size_two["expected_result"] != "sat" or size_two.get("proof_status") != "checked":
        fail("matching-size-two-witness must be a checked sat row")
    values = single_witness_values(size_two, witnesses)
    vertices, edges = require_finite_graph("matching-size-two", values)
    matching = require_graph_edge_list("matching-size-two.matching", values.get("matching"), vertices, edges)
    if not is_matching(matching):
        fail("matching-size-two-witness listed edges are not a matching")
    size = require_int("matching-size-two.size", values.get("size"))
    if len(matching) != size:
        fail("matching-size-two-witness size does not match listed matching")
    if size != maximum_matching_size(edges):
        fail("matching-size-two-witness is not maximum for the graph")
    if covered_vertices(matching) != set(vertices):
        fail("matching-size-two-witness should cover every vertex in the path graph")

    overlapping = checks["overlapping-matching-rejected"]
    if overlapping["expected_result"] != "unsat" or overlapping.get("proof_status") != "checked":
        fail("overlapping-matching-rejected must be a checked unsat row")
    values = single_witness_values(overlapping, witnesses)
    vertices, edges = require_finite_graph("overlapping matching", values)
    matching = require_graph_edge_list("overlapping matching.matching", values.get("matching"), vertices, edges)
    if is_matching(matching):
        fail("overlapping-matching-rejected unexpectedly is a valid matching")

    augmenting = checks["augmenting-path-improves"]
    if augmenting["expected_result"] != "sat" or augmenting.get("proof_status") != "checked":
        fail("augmenting-path-improves must be a checked sat row")
    values = single_witness_values(augmenting, witnesses)
    vertices, edges = require_finite_graph("augmenting path", values)
    current_matching = require_graph_edge_list(
        "augmenting path.current_matching",
        values.get("current_matching"),
        vertices,
        edges,
    )
    improved_matching = require_graph_edge_list(
        "augmenting path.improved_matching",
        values.get("improved_matching"),
        vertices,
        edges,
    )
    path = require_graph_path("augmenting path.path", values.get("augmenting_path"), vertices)
    validate_augmenting_path("augmenting-path-improves", edges, current_matching, path, improved_matching)

    no_perfect = checks["triangle-no-perfect-matching"]
    if no_perfect["expected_result"] != "unsat" or no_perfect.get("proof_status") != "checked":
        fail("triangle-no-perfect-matching must be a checked unsat row")
    data = no_perfect.get("data", {})
    vertices, edges = require_finite_graph("triangle no perfect matching", data)
    maximum_size = require_int("triangle no perfect matching maximum_size", data.get("maximum_size"))
    if maximum_size != maximum_matching_size(edges):
        fail("triangle-no-perfect-matching maximum_size does not match enumeration")
    if has_perfect_matching(vertices, edges):
        fail("triangle-no-perfect-matching unexpectedly has a perfect matching")


def require_directed_acyclic_graph(
    context: str,
    values: dict[str, Any],
) -> tuple[list[str], list[tuple[str, str]]]:
    vertices = require_string_list(f"{context}.vertices", values.get("vertices"))
    edge_values = values.get("directed_edges")
    if not isinstance(edge_values, list):
        fail(f"{context}.directed_edges must be a list")
    vertex_set = set(vertices)
    directed_edges: list[tuple[str, str]] = []
    seen_edges: set[tuple[str, str]] = set()
    for index, edge in enumerate(edge_values):
        if not isinstance(edge, list) or len(edge) != 2:
            fail(f"{context}.directed_edges[{index}] must be a two-element list")
        parent, child = edge
        require_string(f"{context}.directed_edges[{index}][0]", parent)
        require_string(f"{context}.directed_edges[{index}][1]", child)
        if parent == child:
            fail(f"{context}.directed_edges[{index}] must not be a self-loop")
        if parent not in vertex_set or child not in vertex_set:
            fail(f"{context}.directed_edges[{index}] references a missing vertex")
        directed_edge = (parent, child)
        if directed_edge in seen_edges:
            fail(f"{context}.directed_edges repeats edge {directed_edge}")
        seen_edges.add(directed_edge)
        directed_edges.append(directed_edge)
    if not is_dag(vertices, directed_edges):
        fail(f"{context} must be acyclic")
    return vertices, directed_edges


def is_dag(vertices: list[str], directed_edges: list[tuple[str, str]]) -> bool:
    indegree = {vertex: 0 for vertex in vertices}
    children = {vertex: [] for vertex in vertices}
    for parent, child in directed_edges:
        children[parent].append(child)
        indegree[child] += 1
    queue = deque([vertex for vertex in vertices if indegree[vertex] == 0])
    visited = 0
    while queue:
        vertex = queue.popleft()
        visited += 1
        for child in children[vertex]:
            indegree[child] -= 1
            if indegree[child] == 0:
                queue.append(child)
    return visited == len(vertices)


def require_vertex_set(context: str, value: Any, vertices: list[str], *, nonempty: bool = False) -> set[str]:
    items = require_string_list(context, value, nonempty=nonempty)
    vertex_set = set(vertices)
    for item in items:
        if item not in vertex_set:
            fail(f"{context} references missing vertex {item!r}")
    return set(items)


def directed_edge_set(directed_edges: list[tuple[str, str]]) -> set[tuple[str, str]]:
    return set(directed_edges)


def dag_skeleton_edges(directed_edges: list[tuple[str, str]]) -> list[tuple[str, str]]:
    skeleton: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for parent, child in directed_edges:
        edge = tuple(sorted((parent, child)))
        if edge not in seen:
            seen.add(edge)
            skeleton.append((parent, child))
    return skeleton


def dag_descendants(vertices: list[str], directed_edges: list[tuple[str, str]]) -> dict[str, set[str]]:
    children = {vertex: [] for vertex in vertices}
    for parent, child in directed_edges:
        children[parent].append(child)
    descendants: dict[str, set[str]] = {}
    for root in vertices:
        seen: set[str] = set()
        stack = list(children[root])
        while stack:
            vertex = stack.pop()
            if vertex in seen:
                continue
            seen.add(vertex)
            stack.extend(children[vertex])
        descendants[root] = seen
    return descendants


def is_collider(prev_vertex: str, middle: str, next_vertex: str, edge_set: set[tuple[str, str]]) -> bool:
    return (prev_vertex, middle) in edge_set and (next_vertex, middle) in edge_set


def dag_path_is_valid(path: list[str], directed_edges: list[tuple[str, str]]) -> bool:
    skeleton = graph_edge_set(dag_skeleton_edges(directed_edges))
    return all(tuple(sorted((left, right))) in skeleton for left, right in zip(path, path[1:]))


def active_dag_path(
    vertices: list[str],
    directed_edges: list[tuple[str, str]],
    path: list[str],
    conditioned: set[str],
) -> bool:
    if len(path) < 2:
        fail("d-separation path must contain at least two vertices")
    if len(set(path)) != len(path):
        fail("d-separation path must be simple")
    if not all(vertex in set(vertices) for vertex in path):
        fail("d-separation path references a missing vertex")
    if not dag_path_is_valid(path, directed_edges):
        fail("d-separation path contains a non-edge")
    edge_set = directed_edge_set(directed_edges)
    descendants = dag_descendants(vertices, directed_edges)
    for prev_vertex, middle, next_vertex in zip(path, path[1:], path[2:]):
        if is_collider(prev_vertex, middle, next_vertex, edge_set):
            if middle not in conditioned and descendants[middle].isdisjoint(conditioned):
                return False
        elif middle in conditioned:
            return False
    return True


def enumerate_simple_skeleton_paths(
    vertices: list[str],
    directed_edges: list[tuple[str, str]],
    source: str,
    target: str,
) -> list[list[str]]:
    adjacency = graph_adjacency(vertices, dag_skeleton_edges(directed_edges))
    paths: list[list[str]] = []

    def visit(vertex: str, path: list[str], seen: set[str]) -> None:
        if vertex == target:
            paths.append(list(path))
            return
        for neighbor in adjacency[vertex]:
            if neighbor in seen:
                continue
            path.append(neighbor)
            visit(neighbor, path, seen | {neighbor})
            path.pop()

    visit(source, [source], {source})
    return paths


def d_connected(
    vertices: list[str],
    directed_edges: list[tuple[str, str]],
    source: str,
    target: str,
    conditioned: set[str],
) -> bool:
    return any(
        active_dag_path(vertices, directed_edges, path, conditioned)
        for path in enumerate_simple_skeleton_paths(vertices, directed_edges, source, target)
    )


def validate_active_path_witness(context: str, values: dict[str, Any]) -> None:
    vertices, directed_edges = require_directed_acyclic_graph(context, values)
    source = require_graph_vertex(f"{context}.source", values.get("source"), vertices)
    target = require_graph_vertex(f"{context}.target", values.get("target"), vertices)
    conditioned = require_vertex_set(
        f"{context}.conditioning_set",
        values.get("conditioning_set", []),
        vertices,
        nonempty=False,
    )
    path = require_graph_path(f"{context}.path", values.get("path"), vertices)
    if path[0] != source or path[-1] != target:
        fail(f"{context} path endpoints must match source and target")
    if not active_dag_path(vertices, directed_edges, path, conditioned):
        fail(f"{context} path is not active under the conditioning set")
    if not d_connected(vertices, directed_edges, source, target, conditioned):
        fail(f"{context} source and target should be d-connected")


def validate_blocked_dag_query(context: str, data: dict[str, Any]) -> None:
    vertices, directed_edges = require_directed_acyclic_graph(context, data)
    source = require_graph_vertex(f"{context}.source", data.get("source"), vertices)
    target = require_graph_vertex(f"{context}.target", data.get("target"), vertices)
    conditioned = require_vertex_set(
        f"{context}.conditioning_set",
        data.get("conditioning_set", []),
        vertices,
        nonempty=False,
    )
    expected_paths = data.get("all_simple_paths")
    if expected_paths is not None:
        if not isinstance(expected_paths, list):
            fail(f"{context}.all_simple_paths must be a list")
        listed_paths = [
            require_graph_path(f"{context}.all_simple_paths[{index}]", path, vertices)
            for index, path in enumerate(expected_paths)
        ]
        computed_paths = enumerate_simple_skeleton_paths(vertices, directed_edges, source, target)
        if listed_paths != computed_paths:
            fail(f"{context}.all_simple_paths does not match skeleton-path enumeration")
    if d_connected(vertices, directed_edges, source, target, conditioned):
        fail(f"{context} unexpectedly has an active path")


def validate_graph_d_separation(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    chain_active = checks["chain-active-without-conditioning"]
    if chain_active["expected_result"] != "sat" or chain_active.get("proof_status") != "checked":
        fail("chain-active-without-conditioning must be a checked sat row")
    validate_active_path_witness("chain-active-without-conditioning", single_witness_values(chain_active, witnesses))

    chain_blocked = checks["chain-conditioned-blocks"]
    if chain_blocked["expected_result"] != "unsat" or chain_blocked.get("proof_status") != "checked":
        fail("chain-conditioned-blocks must be a checked unsat row")
    validate_blocked_dag_query("chain-conditioned-blocks", chain_blocked.get("data", {}))

    fork_blocked = checks["fork-conditioned-blocks"]
    if fork_blocked["expected_result"] != "unsat" or fork_blocked.get("proof_status") != "checked":
        fail("fork-conditioned-blocks must be a checked unsat row")
    validate_blocked_dag_query("fork-conditioned-blocks", fork_blocked.get("data", {}))

    collider_blocked = checks["collider-unconditioned-blocks"]
    if collider_blocked["expected_result"] != "unsat" or collider_blocked.get("proof_status") != "checked":
        fail("collider-unconditioned-blocks must be a checked unsat row")
    validate_blocked_dag_query("collider-unconditioned-blocks", collider_blocked.get("data", {}))

    collider_open = checks["collider-descendant-opens"]
    if collider_open["expected_result"] != "sat" or collider_open.get("proof_status") != "checked":
        fail("collider-descendant-opens must be a checked sat row")
    validate_active_path_witness("collider-descendant-opens", single_witness_values(collider_open, witnesses))


def graph_separates(
    vertices: list[str],
    edges: list[tuple[str, str]],
    source: str,
    target: str,
) -> bool:
    return target not in shortest_distances(vertices, edges, source)


def minimum_edge_cut_size(
    vertices: list[str],
    edges: list[tuple[str, str]],
    source: str,
    target: str,
) -> int:
    if graph_separates(vertices, edges, source, target):
        return 0
    for size in range(1, len(edges) + 1):
        for removed in combinations(edges, size):
            if graph_separates(vertices, remove_edges(edges, list(removed)), source, target):
                return size
    fail("minimum edge cut search failed to separate a finite connected graph")


def remove_vertices(edges: list[tuple[str, str]], removed_vertices: set[str]) -> list[tuple[str, str]]:
    return [
        edge
        for edge in edges
        if edge[0] not in removed_vertices and edge[1] not in removed_vertices
    ]


def minimum_vertex_cut_size(
    vertices: list[str],
    edges: list[tuple[str, str]],
    source: str,
    target: str,
) -> int:
    if graph_separates(vertices, edges, source, target):
        return 0
    candidates = [vertex for vertex in vertices if vertex not in {source, target}]
    for size in range(1, len(candidates) + 1):
        for removed in combinations(candidates, size):
            if graph_separates(vertices, remove_vertices(edges, set(removed)), source, target):
                return size
    return len(candidates) + 1


def require_graph_cut_partition(
    context: str,
    data: dict[str, Any],
    vertices: list[str],
    source: str,
    target: str,
) -> tuple[set[str], set[str]]:
    source_side = require_vertex_set(
        f"{context}.source_side",
        data.get("source_side"),
        vertices,
        nonempty=True,
    )
    target_side = require_vertex_set(
        f"{context}.target_side",
        data.get("target_side"),
        vertices,
        nonempty=True,
    )
    if source_side & target_side:
        fail(f"{context} partition sides must be disjoint")
    if source_side | target_side != set(vertices):
        fail(f"{context} partition sides must cover every vertex")
    if source not in source_side:
        fail(f"{context} source must be in source_side")
    if target not in target_side:
        fail(f"{context} target must be in target_side")
    return source_side, target_side


def crossing_edges(edges: list[tuple[str, str]], source_side: set[str], target_side: set[str]) -> list[tuple[str, str]]:
    return [
        edge
        for edge in edges
        if (edge[0] in source_side and edge[1] in target_side)
        or (edge[1] in source_side and edge[0] in target_side)
    ]


def require_cut_vertices(
    context: str,
    value: Any,
    vertices: list[str],
    source: str,
    target: str,
) -> set[str]:
    cut_vertices = require_vertex_set(context, value, vertices, nonempty=True)
    if source in cut_vertices or target in cut_vertices:
        fail(f"{context} must not remove source or target")
    return cut_vertices


def validate_graph_cut(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    edge_cut = checks["min-edge-cut-partition-witness"]
    if edge_cut["expected_result"] != "sat" or edge_cut.get("proof_status") != "checked":
        fail("min-edge-cut-partition-witness must be a checked sat row")
    values = single_witness_values(edge_cut, witnesses)
    vertices, edges = require_finite_graph("min edge cut", values)
    source = require_graph_vertex("min edge cut source", values.get("source"), vertices)
    target = require_graph_vertex("min edge cut target", values.get("target"), vertices)
    cut_edges = require_graph_edge_list("min edge cut.cut_edges", values.get("cut_edges"), vertices, edges)
    source_side, target_side = require_graph_cut_partition("min edge cut", values, vertices, source, target)
    if normalized_edge_set(cut_edges) != normalized_edge_set(crossing_edges(edges, source_side, target_side)):
        fail("min-edge-cut-partition-witness cut_edges do not match the partition crossing edges")
    if not graph_separates(vertices, remove_edges(edges, cut_edges), source, target):
        fail("min-edge-cut-partition-witness cut does not separate source and target")
    min_size = require_int("min edge cut min_cut_size", values.get("min_cut_size"))
    if min_size != len(cut_edges) or min_size != minimum_edge_cut_size(vertices, edges, source, target):
        fail("min-edge-cut-partition-witness minimum edge cut size is wrong")

    bad_edge_cut = checks["one-edge-cut-rejected"]
    if bad_edge_cut["expected_result"] != "unsat" or bad_edge_cut.get("proof_status") != "checked":
        fail("one-edge-cut-rejected must be a checked unsat row")
    values = single_witness_values(bad_edge_cut, witnesses)
    vertices, edges = require_finite_graph("bad edge cut", values)
    source = require_graph_vertex("bad edge cut source", values.get("source"), vertices)
    target = require_graph_vertex("bad edge cut target", values.get("target"), vertices)
    cut_edges = require_graph_edge_list("bad edge cut.cut_edges", values.get("cut_edges"), vertices, edges)
    if graph_separates(vertices, remove_edges(edges, cut_edges), source, target):
        fail("one-edge-cut-rejected unexpectedly separates source and target")

    vertex_cut = checks["min-vertex-cut-witness"]
    if vertex_cut["expected_result"] != "sat" or vertex_cut.get("proof_status") != "checked":
        fail("min-vertex-cut-witness must be a checked sat row")
    values = single_witness_values(vertex_cut, witnesses)
    vertices, edges = require_finite_graph("min vertex cut", values)
    source = require_graph_vertex("min vertex cut source", values.get("source"), vertices)
    target = require_graph_vertex("min vertex cut target", values.get("target"), vertices)
    cut_vertices = require_cut_vertices("min vertex cut.cut_vertices", values.get("cut_vertices"), vertices, source, target)
    if not graph_separates(vertices, remove_vertices(edges, cut_vertices), source, target):
        fail("min-vertex-cut-witness cut does not separate source and target")
    min_size = require_int("min vertex cut min_cut_size", values.get("min_cut_size"))
    if min_size != len(cut_vertices) or min_size != minimum_vertex_cut_size(vertices, edges, source, target):
        fail("min-vertex-cut-witness minimum vertex cut size is wrong")

    bad_vertex_cut = checks["one-vertex-cut-rejected"]
    if bad_vertex_cut["expected_result"] != "unsat" or bad_vertex_cut.get("proof_status") != "checked":
        fail("one-vertex-cut-rejected must be a checked unsat row")
    values = single_witness_values(bad_vertex_cut, witnesses)
    vertices, edges = require_finite_graph("bad vertex cut", values)
    source = require_graph_vertex("bad vertex cut source", values.get("source"), vertices)
    target = require_graph_vertex("bad vertex cut target", values.get("target"), vertices)
    cut_vertices = require_cut_vertices("bad vertex cut.cut_vertices", values.get("cut_vertices"), vertices, source, target)
    if graph_separates(vertices, remove_vertices(edges, cut_vertices), source, target):
        fail("one-vertex-cut-rejected unexpectedly separates source and target")


def has_mod_inverse(a: int, modulus: int) -> bool:
    return any((a * candidate) % modulus == 1 for candidate in range(modulus))


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    for candidate in range(2, int(value**0.5) + 1):
        if value % candidate == 0:
            return False
    return True


def require_modulus(context: str, value: Any) -> int:
    modulus = require_int(context, value)
    if modulus <= 1:
        fail(f"{context} must be > 1")
    return modulus


def validate_finite_fields(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    inverse_table = checks["prime-field-inverse-table"]
    if inverse_table["expected_result"] != "sat":
        fail("prime-field-inverse-table must expect sat")
    values = single_witness_values(inverse_table, witnesses)
    modulus = require_modulus("finite field inverse modulus", values.get("modulus"))
    if not is_prime(modulus):
        fail("finite field inverse modulus must be prime")
    inverses = values.get("inverses")
    if not isinstance(inverses, dict):
        fail("finite field inverses must be an object")
    expected_keys = {str(residue) for residue in range(1, modulus)}
    if set(inverses) != expected_keys:
        fail(
            "finite field inverse table must cover exactly nonzero residues: "
            f"expected={sorted(expected_keys, key=int)} actual={sorted(inverses, key=int)}"
        )
    for residue_text in sorted(inverses, key=int):
        residue = int(residue_text)
        inverse = require_int(f"inverse table {residue_text}", inverses[residue_text])
        if inverse <= 0 or inverse >= modulus:
            fail(f"inverse for {residue} must be a nonzero residue modulo {modulus}")
        if (residue * inverse) % modulus != 1:
            fail(f"inverse table entry {residue}->{inverse} does not multiply to 1 modulo {modulus}")

    distributivity = checks["prime-field-distributivity-no-counterexample"]
    if distributivity["expected_result"] != "unsat":
        fail("prime-field-distributivity-no-counterexample must expect unsat")
    data = distributivity.get("data", {})
    modulus = require_modulus("finite field distributivity modulus", data.get("modulus"))
    if not is_prime(modulus):
        fail("finite field distributivity modulus must be prime")
    for a, b, c in product(range(modulus), repeat=3):
        left = (a * ((b + c) % modulus)) % modulus
        right = ((a * b) + (a * c)) % modulus
        if left != right:
            fail(f"distributivity counterexample found modulo {modulus}: {(a, b, c)}")

    composite = checks["composite-modulus-nonfield"]
    if composite["expected_result"] != "unsat":
        fail("composite-modulus-nonfield must expect unsat")
    data = composite.get("data", {})
    modulus = require_modulus("composite modulus", data.get("modulus"))
    if is_prime(modulus):
        fail("composite-modulus-nonfield must use a composite modulus")
    element = require_int("composite modulus element", data.get("element"))
    if element <= 0 or element >= modulus:
        fail("composite modulus element must be a nonzero residue")
    if has_mod_inverse(element, modulus):
        fail(f"element {element} unexpectedly has an inverse modulo {modulus}")


def require_cayley_table(
    context: str,
    values: dict[str, Any],
) -> tuple[list[str], str, dict[tuple[str, str], str]]:
    carrier = require_string_list(f"{context}.carrier", values.get("carrier"))
    carrier_set = set(carrier)
    identity = values.get("identity")
    require_string(f"{context}.identity", identity)
    if identity not in carrier_set:
        fail(f"{context}.identity must be in the carrier")
    raw_table = values.get("table")
    if not isinstance(raw_table, list) or len(raw_table) != len(carrier):
        fail(f"{context}.table must have one row per carrier element")
    operation: dict[tuple[str, str], str] = {}
    for row_index, row in enumerate(raw_table):
        if not isinstance(row, list) or len(row) != len(carrier):
            fail(f"{context}.table[{row_index}] must have one entry per carrier element")
        left = carrier[row_index]
        for col_index, result in enumerate(row):
            require_string(f"{context}.table[{row_index}][{col_index}]", result)
            if result not in carrier_set:
                fail(f"{context}.table[{row_index}][{col_index}] is outside the carrier")
            operation[(left, carrier[col_index])] = result
    return carrier, identity, operation


def table_op(operation: dict[tuple[str, str], str], left: str, right: str) -> str:
    return operation[(left, right)]


def group_axiom_failures(
    carrier: list[str],
    identity: str,
    operation: dict[tuple[str, str], str],
) -> list[str]:
    failures: list[str] = []
    for item in carrier:
        if table_op(operation, identity, item) != item:
            failures.append(f"left identity fails for {item}")
        if table_op(operation, item, identity) != item:
            failures.append(f"right identity fails for {item}")
    for item in carrier:
        if not any(
            table_op(operation, item, candidate) == identity
            and table_op(operation, candidate, item) == identity
            for candidate in carrier
        ):
            failures.append(f"inverse fails for {item}")
    for left in carrier:
        for middle in carrier:
            for right in carrier:
                lhs = table_op(operation, table_op(operation, left, middle), right)
                rhs = table_op(operation, left, table_op(operation, middle, right))
                if lhs != rhs:
                    failures.append(f"associativity fails for {(left, middle, right)}")
                    return failures
    return failures


def require_inverse_table(
    context: str,
    value: Any,
    carrier: list[str],
) -> dict[str, str]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    carrier_set = set(carrier)
    if set(value) != carrier_set:
        fail(f"{context} must cover exactly the carrier")
    inverses: dict[str, str] = {}
    for item, inverse in value.items():
        require_string(f"{context}.{item}", inverse)
        if inverse not in carrier_set:
            fail(f"{context}.{item} must be in the carrier")
        inverses[item] = inverse
    return inverses


def validate_finite_groups(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    group_table = checks["z4-addition-group-table"]
    if group_table["expected_result"] != "sat":
        fail("z4-addition-group-table must expect sat")
    values = single_witness_values(group_table, witnesses)
    carrier, identity, operation = require_cayley_table("z4 addition", values)
    failures = group_axiom_failures(carrier, identity, operation)
    if failures:
        fail(f"z4-addition-group-table failed group axioms: {failures[0]}")

    inverse_check = checks["z4-inverse-table"]
    if inverse_check["expected_result"] != "sat":
        fail("z4-inverse-table must expect sat")
    values = single_witness_values(inverse_check, witnesses)
    carrier, identity, operation = require_cayley_table("z4 inverse table", values)
    inverses = require_inverse_table("z4 inverses", values.get("inverses"), carrier)
    for item, inverse in inverses.items():
        if table_op(operation, item, inverse) != identity:
            fail(f"z4 inverse table has bad right inverse for {item}")
        if table_op(operation, inverse, item) != identity:
            fail(f"z4 inverse table has bad left inverse for {item}")

    bad_group = checks["subtraction-mod3-non-group"]
    if bad_group["expected_result"] != "unsat":
        fail("subtraction-mod3-non-group must expect unsat")
    values = single_witness_values(bad_group, witnesses)
    carrier, identity, operation = require_cayley_table("subtraction mod 3", values)
    if not group_axiom_failures(carrier, identity, operation):
        fail("subtraction-mod3-non-group unexpectedly satisfies the group axioms")


def require_binary_table(
    context: str,
    carrier: list[str],
    value: Any,
) -> dict[tuple[str, str], str]:
    carrier_set = set(carrier)
    if not isinstance(value, list) or len(value) != len(carrier):
        fail(f"{context} must have one row per carrier element")
    operation: dict[tuple[str, str], str] = {}
    for row_index, row in enumerate(value):
        if not isinstance(row, list) or len(row) != len(carrier):
            fail(f"{context}[{row_index}] must have one entry per carrier element")
        left = carrier[row_index]
        for col_index, result in enumerate(row):
            require_string(f"{context}[{row_index}][{col_index}]", result)
            if result not in carrier_set:
                fail(f"{context}[{row_index}][{col_index}] is outside the carrier")
            operation[(left, carrier[col_index])] = result
    return operation


def require_ring_tables(
    context: str,
    values: dict[str, Any],
) -> tuple[list[str], str, str | None, dict[tuple[str, str], str], dict[tuple[str, str], str]]:
    carrier = require_string_list(f"{context}.carrier", values.get("carrier"))
    carrier_set = set(carrier)
    zero = values.get("zero")
    require_string(f"{context}.zero", zero)
    if zero not in carrier_set:
        fail(f"{context}.zero must be in the carrier")
    one = values.get("one")
    if one is not None:
        require_string(f"{context}.one", one)
        if one not in carrier_set:
            fail(f"{context}.one must be in the carrier")
    add_op = require_binary_table(f"{context}.add", carrier, values.get("add"))
    mul_op = require_binary_table(f"{context}.mul", carrier, values.get("mul"))
    return carrier, zero, one, add_op, mul_op


def is_commutative(carrier: list[str], operation: dict[tuple[str, str], str]) -> bool:
    return all(table_op(operation, left, right) == table_op(operation, right, left) for left in carrier for right in carrier)


def is_associative(carrier: list[str], operation: dict[tuple[str, str], str]) -> bool:
    for left in carrier:
        for middle in carrier:
            for right in carrier:
                lhs = table_op(operation, table_op(operation, left, middle), right)
                rhs = table_op(operation, left, table_op(operation, middle, right))
                if lhs != rhs:
                    return False
    return True


def distributivity_failures(
    carrier: list[str],
    add_op: dict[tuple[str, str], str],
    mul_op: dict[tuple[str, str], str],
) -> list[str]:
    failures: list[str] = []
    for left in carrier:
        for middle in carrier:
            for right in carrier:
                left_distrib = table_op(mul_op, left, table_op(add_op, middle, right))
                left_sum = table_op(add_op, table_op(mul_op, left, middle), table_op(mul_op, left, right))
                if left_distrib != left_sum:
                    failures.append(f"left distributivity fails for {(left, middle, right)}")
                    return failures
                right_distrib = table_op(mul_op, table_op(add_op, left, middle), right)
                right_sum = table_op(add_op, table_op(mul_op, left, right), table_op(mul_op, middle, right))
                if right_distrib != right_sum:
                    failures.append(f"right distributivity fails for {(left, middle, right)}")
                    return failures
    return failures


def ring_axiom_failures(
    carrier: list[str],
    zero: str,
    one: str | None,
    add_op: dict[tuple[str, str], str],
    mul_op: dict[tuple[str, str], str],
) -> list[str]:
    failures = group_axiom_failures(carrier, zero, add_op)
    if failures:
        return [f"addition {failures[0]}"]
    if not is_commutative(carrier, add_op):
        return ["addition is not commutative"]
    if not is_associative(carrier, mul_op):
        return ["multiplication is not associative"]
    if one is not None:
        for item in carrier:
            if table_op(mul_op, one, item) != item:
                return [f"left multiplicative identity fails for {item}"]
            if table_op(mul_op, item, one) != item:
                return [f"right multiplicative identity fails for {item}"]
    return distributivity_failures(carrier, add_op, mul_op)


def validate_finite_rings(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    ring_table = checks["z4-ring-table"]
    if ring_table["expected_result"] != "sat":
        fail("z4-ring-table must expect sat")
    values = single_witness_values(ring_table, witnesses)
    carrier, zero, one, add_op, mul_op = require_ring_tables("z4 ring", values)
    failures = ring_axiom_failures(carrier, zero, one, add_op, mul_op)
    if failures:
        fail(f"z4-ring-table failed ring axioms: {failures[0]}")

    zero_divisor = checks["z4-zero-divisor-witness"]
    if zero_divisor["expected_result"] != "sat":
        fail("z4-zero-divisor-witness must expect sat")
    values = single_witness_values(zero_divisor, witnesses)
    carrier, zero, one, add_op, mul_op = require_ring_tables("z4 zero divisor", values)
    failures = ring_axiom_failures(carrier, zero, one, add_op, mul_op)
    if failures:
        fail(f"z4-zero-divisor-witness ring table failed axioms: {failures[0]}")
    witness = values.get("zero_divisor")
    if not isinstance(witness, dict):
        fail("z4-zero-divisor-witness zero_divisor must be an object")
    left = witness.get("left")
    right = witness.get("right")
    require_string("zero divisor left", left)
    require_string("zero divisor right", right)
    if left not in set(carrier) or right not in set(carrier):
        fail("zero divisor factors must be in the carrier")
    if left == zero or right == zero:
        fail("zero divisor factors must both be nonzero")
    if table_op(mul_op, left, right) != zero:
        fail("zero divisor factors do not multiply to zero")

    bad_table = checks["non-distributive-table-rejected"]
    if bad_table["expected_result"] != "unsat":
        fail("non-distributive-table-rejected must expect unsat")
    values = single_witness_values(bad_table, witnesses)
    carrier, zero, one, add_op, mul_op = require_ring_tables("non-distributive table", values)
    failures = ring_axiom_failures(carrier, zero, one, add_op, mul_op)
    if not failures:
        fail("non-distributive-table-rejected unexpectedly satisfies the ring axioms")
    if not distributivity_failures(carrier, add_op, mul_op):
        fail("non-distributive-table-rejected must fail distributivity specifically")


def require_counting_int(context: str, value: Any) -> int:
    item = require_int(context, value)
    if item < 0:
        fail(f"{context} must be nonnegative")
    return item


def factorial(value: int) -> int:
    result = 1
    for item in range(2, value + 1):
        result *= item
    return result


def permutation_count(n_value: int, k_value: int) -> int:
    if k_value > n_value:
        return 0
    return factorial(n_value) // factorial(n_value - k_value)


def combination_count(n_value: int, k_value: int) -> int:
    if k_value > n_value:
        return 0
    return factorial(n_value) // (factorial(k_value) * factorial(n_value - k_value))


def has_injective_placement(pigeons: int, holes: int) -> bool:
    for placement in product(range(holes), repeat=pigeons):
        if len(set(placement)) == pigeons:
            return True
    return False


def validate_counting(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    permutation = checks["permutation-count-fixed"]
    if permutation["expected_result"] != "sat":
        fail("permutation-count-fixed must expect sat")
    values = single_witness_values(permutation, witnesses)
    n_value = require_counting_int("permutation n", values.get("n"))
    k_value = require_counting_int("permutation k", values.get("k"))
    expected_count = require_counting_int("permutation expected", values.get("expected"))
    if permutation_count(n_value, k_value) != expected_count:
        fail("permutation-count-fixed expected count does not match P(n,k)")

    pascal = checks["pascal-identity-fixed"]
    if pascal["expected_result"] != "sat":
        fail("pascal-identity-fixed must expect sat")
    values = single_witness_values(pascal, witnesses)
    n_value = require_counting_int("pascal n", values.get("n"))
    k_value = require_counting_int("pascal k", values.get("k"))
    left = require_counting_int("pascal left", values.get("left"))
    lower_left = require_counting_int("pascal lower_left", values.get("lower_left"))
    lower_right = require_counting_int("pascal lower_right", values.get("lower_right"))
    if n_value <= 0 or k_value <= 0 or k_value > n_value:
        fail("pascal identity requires 0 < k <= n")
    if combination_count(n_value, k_value) != left:
        fail("pascal left does not match C(n,k)")
    if combination_count(n_value - 1, k_value - 1) != lower_left:
        fail("pascal lower_left does not match C(n-1,k-1)")
    if combination_count(n_value - 1, k_value) != lower_right:
        fail("pascal lower_right does not match C(n-1,k)")
    if left != lower_left + lower_right:
        fail("pascal identity row does not satisfy left = lower_left + lower_right")

    pigeonhole = checks["pigeonhole-3-2-unsat"]
    if pigeonhole["expected_result"] != "unsat":
        fail("pigeonhole-3-2-unsat must expect unsat")
    data = pigeonhole.get("data", {})
    pigeons = require_counting_int("pigeonhole pigeons", data.get("pigeons"))
    holes = require_counting_int("pigeonhole holes", data.get("holes"))
    if pigeons <= holes:
        fail("pigeonhole unsat row must use more pigeons than holes")
    if has_injective_placement(pigeons, holes):
        fail("pigeonhole check unexpectedly found an injective placement")


def is_injective_mapping(mapping: dict[str, str]) -> bool:
    return len(set(mapping.values())) == len(mapping)


def is_surjective_mapping(mapping: dict[str, str], codomain: list[str]) -> bool:
    return set(mapping.values()) == set(codomain)


def function_space_size(domain: list[str], codomain: list[str]) -> int:
    return len(codomain) ** len(domain)


def require_small_function_space(context: str, domain: list[str], codomain: list[str]) -> None:
    size = function_space_size(domain, codomain)
    if size > 100_000:
        fail(f"{context} function space is too large for deterministic example-pack enumeration")


def has_injective_function(domain: list[str], codomain: list[str]) -> bool:
    require_small_function_space("injective-function search", domain, codomain)
    for outputs in product(codomain, repeat=len(domain)):
        if len(set(outputs)) == len(outputs):
            return True
    return False


def has_surjective_function(domain: list[str], codomain: list[str]) -> bool:
    require_small_function_space("surjective-function search", domain, codomain)
    codomain_set = set(codomain)
    for outputs in product(codomain, repeat=len(domain)):
        if set(outputs) == codomain_set:
            return True
    return False


def require_cardinality_sets(context: str, data: dict[str, Any]) -> tuple[list[str], list[str]]:
    domain = require_string_list(f"{context}.domain", data.get("domain"))
    codomain = require_string_list(f"{context}.codomain", data.get("codomain"))
    require_small_function_space(context, domain, codomain)
    return domain, codomain


def validate_finite_cardinality(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    bijection = checks["finite-bijection-cardinality-witness"]
    if bijection["expected_result"] != "sat":
        fail("finite-bijection-cardinality-witness must expect sat")
    values = single_witness_values(bijection, witnesses)
    domain, codomain, pairs = require_function_graph_data("finite cardinality bijection", values)
    if len(domain) != len(codomain):
        fail("finite-bijection-cardinality-witness must use equal finite sizes")
    if not is_total_function(domain, pairs):
        fail("finite-bijection-cardinality-witness graph is not total")
    if not is_single_valued(domain, pairs):
        fail("finite-bijection-cardinality-witness graph is not single-valued")
    mapping = function_mapping(domain, pairs)
    if not is_injective_mapping(mapping):
        fail("finite-bijection-cardinality-witness graph is not injective")
    if not is_surjective_mapping(mapping, codomain):
        fail("finite-bijection-cardinality-witness graph is not surjective")

    proper_subset = checks["proper-subset-injection-witness"]
    if proper_subset["expected_result"] != "sat":
        fail("proper-subset-injection-witness must expect sat")
    values = single_witness_values(proper_subset, witnesses)
    domain, codomain, pairs = require_function_graph_data("proper subset injection", values)
    if not set(domain) < set(codomain):
        fail("proper-subset-injection-witness domain must be a proper subset of codomain")
    if not is_total_function(domain, pairs):
        fail("proper-subset-injection-witness graph is not total")
    if not is_single_valued(domain, pairs):
        fail("proper-subset-injection-witness graph is not single-valued")
    mapping = function_mapping(domain, pairs)
    if not is_injective_mapping(mapping):
        fail("proper-subset-injection-witness graph is not injective")
    if is_surjective_mapping(mapping, codomain):
        fail("proper-subset-injection-witness graph unexpectedly is surjective")

    no_injection = checks["no-injection-four-to-three"]
    if no_injection["expected_result"] != "unsat":
        fail("no-injection-four-to-three must expect unsat")
    domain, codomain = require_cardinality_sets("no-injection-four-to-three", no_injection.get("data", {}))
    if len(domain) <= len(codomain):
        fail("no-injection-four-to-three must use a larger domain than codomain")
    if has_injective_function(domain, codomain):
        fail("no-injection-four-to-three unexpectedly found an injective function")

    no_surjection = checks["no-surjection-two-to-three"]
    if no_surjection["expected_result"] != "unsat":
        fail("no-surjection-two-to-three must expect unsat")
    domain, codomain = require_cardinality_sets("no-surjection-two-to-three", no_surjection.get("data", {}))
    if len(domain) >= len(codomain):
        fail("no-surjection-two-to-three must use a smaller domain than codomain")
    if has_surjective_function(domain, codomain):
        fail("no-surjection-two-to-three unexpectedly found a surjective function")

    cantor = checks["cantor-diagonal-lean-horizon"]
    if cantor["expected_result"] != "not-run":
        fail("cantor-diagonal-lean-horizon must be not-run")
    if cantor["proof_status"] != "lean-horizon":
        fail("cantor-diagonal-lean-horizon must remain lean-horizon")
    data = cantor.get("data", {})
    require_string("cantor target theorem", data.get("target_theorem"))
    require_string("cantor future checker", data.get("future_checker"))


def validate_modular_arithmetic(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    crt = checks["crt-coprime-witness"]
    if crt["expected_result"] != "sat":
        fail("crt-coprime-witness must expect sat")
    crt_values = single_witness_values(crt, witnesses)
    x = require_int("crt witness x", crt_values.get("x"))
    congruences = crt_values.get("congruences")
    if not isinstance(congruences, list) or len(congruences) < 2:
        fail("crt witness congruences must contain at least two congruences")
    moduli: list[int] = []
    for index, congruence in enumerate(congruences):
        if not isinstance(congruence, dict):
            fail(f"crt congruence {index} must be an object")
        remainder = require_int(f"crt congruence {index}.remainder", congruence.get("remainder"))
        modulus = require_int(f"crt congruence {index}.modulus", congruence.get("modulus"))
        if modulus <= 1:
            fail(f"crt congruence {index}.modulus must be > 1")
        if x % modulus != remainder % modulus:
            fail(f"crt witness does not satisfy x == {remainder} mod {modulus}")
        moduli.append(modulus)
    for left_index, left in enumerate(moduli):
        for right in moduli[left_index + 1 :]:
            if gcd(left, right) != 1:
                fail(f"CRT moduli must be coprime: {left}, {right}")

    inverse = checks["modular-inverse-witness"]
    if inverse["expected_result"] != "sat":
        fail("modular-inverse-witness must expect sat")
    inv_values = single_witness_values(inverse, witnesses)
    a = require_int("inverse witness a", inv_values.get("a"))
    modulus = require_int("inverse witness modulus", inv_values.get("modulus"))
    inv = require_int("inverse witness inverse", inv_values.get("inverse"))
    if modulus <= 1:
        fail("inverse modulus must be > 1")
    if gcd(a, modulus) != 1:
        fail("inverse witness a must be coprime to modulus")
    if (a * inv) % modulus != 1:
        fail("inverse witness does not multiply to 1 modulo modulus")

    nonunit = checks["composite-nonunit-no-inverse"]
    if nonunit["expected_result"] != "unsat":
        fail("composite-nonunit-no-inverse must expect unsat")
    data = nonunit.get("data", {})
    a = require_int("nonunit data a", data.get("a"))
    modulus = require_int("nonunit data modulus", data.get("modulus"))
    if modulus <= 1:
        fail("nonunit modulus must be > 1")
    if gcd(a, modulus) == 1:
        fail("nonunit data must use a non-coprime residue")
    if has_mod_inverse(a, modulus):
        fail("nonunit check found an inverse unexpectedly")

    fermat = checks["fermat-units-mod-prime"]
    if fermat["expected_result"] != "unsat":
        fail("fermat-units-mod-prime must expect unsat")
    data = fermat.get("data", {})
    modulus = require_int("fermat data modulus", data.get("modulus"))
    exponent = require_int("fermat data exponent", data.get("exponent"))
    if modulus <= 1:
        fail("fermat modulus must be > 1")
    for a in range(1, modulus):
        if gcd(a, modulus) == 1 and pow(a, exponent, modulus) != 1:
            fail(f"fermat counterexample found: a={a}, modulus={modulus}, exponent={exponent}")


def positive_divisors(value: int) -> list[int]:
    value = abs(value)
    if value == 0:
        fail("positive divisors are undefined for zero")
    return [candidate for candidate in range(1, value + 1) if value % candidate == 0]


def require_int_list(context: str, value: Any) -> list[int]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty integer list")
    return [require_int(f"{context}[{index}]", item) for index, item in enumerate(value)]


def validate_gcd_bezout(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    gcd_check = checks["gcd-common-divisors-replay"]
    if gcd_check["expected_result"] != "sat":
        fail("gcd-common-divisors-replay must expect sat")
    values = single_witness_values(gcd_check, witnesses)
    a = require_int("gcd witness a", values.get("a"))
    b = require_int("gcd witness b", values.get("b"))
    expected_gcd = require_int("gcd witness gcd", values.get("gcd"))
    if expected_gcd <= 0:
        fail("gcd witness gcd must be positive")
    computed_gcd = gcd(abs(a), abs(b))
    if computed_gcd != expected_gcd:
        fail("gcd-common-divisors-replay gcd does not match")
    listed_common_divisors = sorted(
        require_int_list("gcd witness common_divisors", values.get("common_divisors"))
    )
    computed_common_divisors = [
        divisor
        for divisor in positive_divisors(computed_gcd)
        if a % divisor == 0 and b % divisor == 0
    ]
    if listed_common_divisors != computed_common_divisors:
        fail("gcd-common-divisors-replay common divisors do not match")

    bezout = checks["bezout-identity-replay"]
    if bezout["expected_result"] != "sat":
        fail("bezout-identity-replay must expect sat")
    values = single_witness_values(bezout, witnesses)
    a = require_int("bezout witness a", values.get("a"))
    b = require_int("bezout witness b", values.get("b"))
    expected_gcd = require_int("bezout witness gcd", values.get("gcd"))
    x = require_int("bezout witness x", values.get("x"))
    y = require_int("bezout witness y", values.get("y"))
    if expected_gcd <= 0:
        fail("bezout witness gcd must be positive")
    if gcd(abs(a), abs(b)) != expected_gcd:
        fail("bezout-identity-replay gcd does not match")
    if a * x + b * y != expected_gcd:
        fail("bezout-identity-replay coefficients do not produce the gcd")

    divisibility = checks["divisibility-quotient-replay"]
    if divisibility["expected_result"] != "sat":
        fail("divisibility-quotient-replay must expect sat")
    values = single_witness_values(divisibility, witnesses)
    divisor = require_int("divisibility witness divisor", values.get("divisor"))
    dividend = require_int("divisibility witness dividend", values.get("dividend"))
    quotient = require_int("divisibility witness quotient", values.get("quotient"))
    if divisor == 0:
        fail("divisibility witness divisor must be nonzero")
    if divisor * quotient != dividend:
        fail("divisibility-quotient-replay quotient does not match dividend")

    obstruction = checks["diophantine-gcd-obstruction"]
    if obstruction["expected_result"] != "unsat":
        fail("diophantine-gcd-obstruction must expect unsat")
    data = obstruction.get("data", {})
    a = require_int("diophantine data a", data.get("a"))
    b = require_int("diophantine data b", data.get("b"))
    target = require_int("diophantine data target", data.get("target"))
    coefficient_gcd = gcd(abs(a), abs(b))
    if coefficient_gcd == 0:
        fail("diophantine coefficients must not both be zero")
    if target % coefficient_gcd == 0:
        fail("diophantine-gcd-obstruction data is satisfiable by the gcd criterion")


def require_residue(context: str, value: Any, modulus: int) -> int:
    residue = require_int(context, value)
    if residue < 0 or residue >= modulus:
        fail(f"{context} must be a residue in [0, {modulus})")
    return residue


def require_congruences(context: str, value: Any) -> list[dict[str, int]]:
    if not isinstance(value, list) or len(value) < 2:
        fail(f"{context} must contain at least two congruences")
    congruences: list[dict[str, int]] = []
    for index, congruence in enumerate(value):
        if not isinstance(congruence, dict):
            fail(f"{context}[{index}] must be an object")
        modulus = require_modulus(
            f"{context}[{index}].modulus",
            congruence.get("modulus"),
        )
        remainder = require_int(f"{context}[{index}].remainder", congruence.get("remainder"))
        congruences.append({"remainder": remainder, "modulus": modulus})
    return congruences


def has_square_root_mod(residue: int, modulus: int) -> bool:
    return any(
        (candidate * candidate) % modulus == residue % modulus
        for candidate in range(modulus)
    )


def validate_number_theory(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    crt = checks["crt-compatible-noncoprime-witness"]
    if crt["expected_result"] != "sat":
        fail("crt-compatible-noncoprime-witness must expect sat")
    values = single_witness_values(crt, witnesses)
    x = require_int("number theory CRT x", values.get("x"))
    congruences = require_congruences("number theory CRT congruences", values.get("congruences"))
    has_noncoprime_pair = False
    for congruence in congruences:
        if x % congruence["modulus"] != congruence["remainder"] % congruence["modulus"]:
            fail("crt-compatible-noncoprime-witness does not satisfy all congruences")
    for left_index, left in enumerate(congruences):
        for right in congruences[left_index + 1 :]:
            divisor = gcd(left["modulus"], right["modulus"])
            if divisor > 1:
                has_noncoprime_pair = True
            if (left["remainder"] - right["remainder"]) % divisor != 0:
                fail("crt-compatible-noncoprime-witness has incompatible congruences")
    if not has_noncoprime_pair:
        fail("crt-compatible-noncoprime-witness must include a non-coprime modulus pair")

    residue = checks["quadratic-residue-witness"]
    if residue["expected_result"] != "sat":
        fail("quadratic-residue-witness must expect sat")
    values = single_witness_values(residue, witnesses)
    modulus = require_modulus("quadratic residue modulus", values.get("modulus"))
    if not is_prime(modulus):
        fail("quadratic residue modulus must be prime")
    target = require_residue("quadratic residue target", values.get("residue"), modulus)
    root = require_residue("quadratic residue root", values.get("root"), modulus)
    if (root * root) % modulus != target:
        fail("quadratic-residue-witness root does not square to the target")

    nonresidue = checks["quadratic-nonresidue-rejected"]
    if nonresidue["expected_result"] != "unsat":
        fail("quadratic-nonresidue-rejected must expect unsat")
    data = nonresidue.get("data", {})
    modulus = require_modulus("quadratic nonresidue modulus", data.get("modulus"))
    if not is_prime(modulus):
        fail("quadratic nonresidue modulus must be prime")
    target = require_residue("quadratic nonresidue target", data.get("residue"), modulus)
    if has_square_root_mod(target, modulus):
        fail("quadratic-nonresidue-rejected found a square root unexpectedly")

    sum_squares = checks["sum-two-squares-witness"]
    if sum_squares["expected_result"] != "sat":
        fail("sum-two-squares-witness must expect sat")
    values = single_witness_values(sum_squares, witnesses)
    n_value = require_int("sum two squares n", values.get("n"))
    left = require_int("sum two squares a", values.get("a"))
    right = require_int("sum two squares b", values.get("b"))
    if n_value < 0:
        fail("sum-two-squares-witness n must be nonnegative")
    if left * left + right * right != n_value:
        fail("sum-two-squares-witness does not match a^2 + b^2")

    mod4 = checks["sum-two-squares-mod4-rejected"]
    if mod4["expected_result"] != "unsat":
        fail("sum-two-squares-mod4-rejected must expect unsat")
    data = mod4.get("data", {})
    n_value = require_int("sum two squares mod4 n", data.get("n"))
    if n_value < 0:
        fail("sum-two-squares-mod4-rejected n must be nonnegative")
    square_residues = {candidate * candidate % 4 for candidate in range(4)}
    possible_sums = {(left + right) % 4 for left, right in product(square_residues, repeat=2)}
    if n_value % 4 in possible_sums:
        fail("sum-two-squares-mod4-rejected data is not ruled out by mod-4 squares")

    diophantine = checks["bounded-diophantine-witness"]
    if diophantine["expected_result"] != "sat":
        fail("bounded-diophantine-witness must expect sat")
    values = single_witness_values(diophantine, witnesses)
    coefficients = require_int_list("bounded diophantine coefficients", values.get("coefficients"))
    solution = require_int_list("bounded diophantine solution", values.get("solution"))
    target = require_int("bounded diophantine target", values.get("target"))
    if len(coefficients) != len(solution):
        fail("bounded-diophantine-witness coefficients and solution must have the same length")
    total = sum(coefficient * value for coefficient, value in zip(coefficients, solution))
    if total != target:
        fail("bounded-diophantine-witness solution does not satisfy the equation")


def integer_relation(left: int, right: int) -> str:
    if left < right:
        return "lt"
    if left > right:
        return "gt"
    return "eq"


def require_linear_integer_witness(
    context: str,
    values: dict[str, Any],
) -> tuple[list[int], list[int], int]:
    coefficients = require_int_list(f"{context}.coefficients", values.get("coefficients"))
    solution = require_int_list(f"{context}.solution", values.get("solution"))
    target = require_int(f"{context}.target", values.get("target"))
    if len(coefficients) != len(solution):
        fail(f"{context} coefficients and solution must have the same length")
    return coefficients, solution, target


def dot_product(left: list[int], right: list[int]) -> int:
    return sum(left_value * right_value for left_value, right_value in zip(left, right))


def validate_integer_lia(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    trichotomy = checks["signed-trichotomy-fixed"]
    if trichotomy["expected_result"] != "sat":
        fail("signed-trichotomy-fixed must expect sat")
    values = single_witness_values(trichotomy, witnesses)
    left = require_int("trichotomy left", values.get("left"))
    right = require_int("trichotomy right", values.get("right"))
    relation = values.get("relation")
    require_string("trichotomy relation", relation)
    if relation not in {"lt", "eq", "gt"}:
        fail("trichotomy relation must be one of lt, eq, gt")
    truth_values = [left < right, left == right, left > right]
    if sum(1 for truth_value in truth_values if truth_value) != 1:
        fail("signed-trichotomy-fixed did not find exactly one true relation")
    if integer_relation(left, right) != relation:
        fail("signed-trichotomy-fixed listed relation is not the true relation")

    transitivity = checks["order-transitivity-fixed"]
    if transitivity["expected_result"] != "sat":
        fail("order-transitivity-fixed must expect sat")
    values = single_witness_values(transitivity, witnesses)
    a_value = require_int("transitivity a", values.get("a"))
    b_value = require_int("transitivity b", values.get("b"))
    c_value = require_int("transitivity c", values.get("c"))
    if not (a_value < b_value and b_value < c_value and a_value < c_value):
        fail("order-transitivity-fixed chain does not satisfy transitivity")

    identity = checks["integer-ring-identity-replay"]
    if identity["expected_result"] != "sat":
        fail("integer-ring-identity-replay must expect sat")
    values = single_witness_values(identity, witnesses)
    a_value = require_int("ring identity a", values.get("a"))
    b_value = require_int("ring identity b", values.get("b"))
    result = require_int("ring identity result", values.get("result"))
    if (a_value + b_value) - b_value != result:
        fail("integer-ring-identity-replay result does not match")
    if result != a_value:
        fail("integer-ring-identity-replay result must equal a")

    equation = checks["linear-equation-witness"]
    if equation["expected_result"] != "sat":
        fail("linear-equation-witness must expect sat")
    values = single_witness_values(equation, witnesses)
    coefficients, solution, target = require_linear_integer_witness("linear equation", values)
    if dot_product(coefficients, solution) != target:
        fail("linear-equation-witness solution does not satisfy the equation")

    interval = checks["integer-interval-infeasible"]
    if interval["expected_result"] != "unsat":
        fail("integer-interval-infeasible must expect unsat")
    data = interval.get("data", {})
    lower = require_int("integer interval lower", data.get("lower"))
    upper = require_int("integer interval upper", data.get("upper"))
    if lower <= upper:
        fail("integer-interval-infeasible data is satisfiable")

    obstruction = checks["diophantine-gcd-obstruction"]
    if obstruction["expected_result"] != "unsat":
        fail("diophantine-gcd-obstruction must expect unsat")
    data = obstruction.get("data", {})
    coefficients = require_int_list("integer diophantine coefficients", data.get("coefficients"))
    target = require_int("integer diophantine target", data.get("target"))
    coefficient_gcd = 0
    for coefficient in coefficients:
        coefficient_gcd = gcd(coefficient_gcd, abs(coefficient))
    if coefficient_gcd == 0:
        fail("diophantine-gcd-obstruction coefficients must not all be zero")
    if target % coefficient_gcd == 0:
        fail("diophantine-gcd-obstruction data is satisfiable by the gcd criterion")


def require_natural(context: str, value: Any) -> int:
    item = require_int(context, value)
    if item < 0:
        fail(f"{context} must be nonnegative")
    return item


def require_bounded_natural_max(context: str, data: dict[str, Any]) -> int:
    max_value = require_natural(f"{context}.max", data.get("max"))
    if max_value > 1024:
        fail(f"{context}.max is too large for deterministic example-pack enumeration")
    return max_value


def validate_natural_arithmetic(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    successor_addition = checks["successor-addition-replay"]
    if successor_addition["expected_result"] != "sat":
        fail("successor-addition-replay must expect sat")
    values = single_witness_values(successor_addition, witnesses)
    a_value = require_natural("successor addition a", values.get("a"))
    b_value = require_natural("successor addition b", values.get("b"))
    successor_b = require_natural("successor addition successor_b", values.get("successor_b"))
    left = require_natural("successor addition left", values.get("left"))
    right = require_natural("successor addition right", values.get("right"))
    if successor_b != b_value + 1:
        fail("successor-addition-replay successor_b does not equal b + 1")
    if a_value + successor_b != left:
        fail("successor-addition-replay left side does not match a + S(b)")
    if a_value + b_value + 1 != right:
        fail("successor-addition-replay right side does not match S(a + b)")
    if left != right:
        fail("successor-addition-replay sides are not equal")

    commutativity = checks["addition-commutativity-fixed"]
    if commutativity["expected_result"] != "sat":
        fail("addition-commutativity-fixed must expect sat")
    values = single_witness_values(commutativity, witnesses)
    a_value = require_natural("commutativity a", values.get("a"))
    b_value = require_natural("commutativity b", values.get("b"))
    sum_ab = require_natural("commutativity sum_ab", values.get("sum_ab"))
    sum_ba = require_natural("commutativity sum_ba", values.get("sum_ba"))
    if a_value + b_value != sum_ab:
        fail("addition-commutativity-fixed sum_ab does not match")
    if b_value + a_value != sum_ba:
        fail("addition-commutativity-fixed sum_ba does not match")
    if sum_ab != sum_ba:
        fail("addition-commutativity-fixed sums are not equal")

    distributivity = checks["multiplication-distributivity-fixed"]
    if distributivity["expected_result"] != "sat":
        fail("multiplication-distributivity-fixed must expect sat")
    values = single_witness_values(distributivity, witnesses)
    a_value = require_natural("distributivity a", values.get("a"))
    b_value = require_natural("distributivity b", values.get("b"))
    c_value = require_natural("distributivity c", values.get("c"))
    left = require_natural("distributivity left", values.get("left"))
    right = require_natural("distributivity right", values.get("right"))
    if a_value * (b_value + c_value) != left:
        fail("multiplication-distributivity-fixed left side does not match")
    if a_value * b_value + a_value * c_value != right:
        fail("multiplication-distributivity-fixed right side does not match")
    if left != right:
        fail("multiplication-distributivity-fixed sides are not equal")

    injective = checks["successor-injective-bounded"]
    if injective["expected_result"] != "unsat":
        fail("successor-injective-bounded must expect unsat")
    max_value = require_bounded_natural_max("successor-injective-bounded", injective.get("data", {}))
    for left_value in range(max_value + 1):
        for right_value in range(max_value + 1):
            if left_value != right_value and left_value + 1 == right_value + 1:
                fail("successor-injective-bounded found a counterexample")

    zero = checks["zero-not-successor-bounded"]
    if zero["expected_result"] != "unsat":
        fail("zero-not-successor-bounded must expect unsat")
    max_value = require_bounded_natural_max("zero-not-successor-bounded", zero.get("data", {}))
    for value in range(max_value + 1):
        if value + 1 == 0:
            fail("zero-not-successor-bounded found a predecessor of zero")

    nonnegative = checks["bounded-natural-negative-rejected"]
    if nonnegative["expected_result"] != "unsat":
        fail("bounded-natural-negative-rejected must expect unsat")
    max_value = require_bounded_natural_max(
        "bounded-natural-negative-rejected",
        nonnegative.get("data", {}),
    )
    for value in range(max_value + 1):
        if value < 0:
            fail("bounded-natural-negative-rejected found a negative natural")


def require_bool(context: str, value: Any) -> bool:
    if not isinstance(value, bool):
        fail(f"{context} must be a boolean")
    return value


def prefix_sum(n_value: int) -> int:
    return sum(range(n_value + 1))


def prefix_sum_formula(n_value: int) -> int:
    return n_value * (n_value + 1) // 2


def prefix_sum_property_holds(n_value: int) -> bool:
    return prefix_sum(n_value) == prefix_sum_formula(n_value)


def require_bounded_induction_limit(context: str, data: dict[str, Any], key: str) -> int:
    max_value = require_natural(f"{context}.{key}", data.get(key))
    if max_value > 1024:
        fail(f"{context}.{key} is too large for deterministic example-pack enumeration")
    return max_value


def validate_induction_obligations(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    base = checks["sum-formula-base-case"]
    if base["expected_result"] != "sat":
        fail("sum-formula-base-case must expect sat")
    values = single_witness_values(base, witnesses)
    n_value = require_natural("sum formula base n", values.get("n"))
    listed_sum = require_natural("sum formula base sum_0_to_n", values.get("sum_0_to_n"))
    listed_formula = require_natural("sum formula base formula", values.get("formula"))
    if n_value != 0:
        fail("sum-formula-base-case must use n = 0")
    if listed_sum != prefix_sum(n_value):
        fail("sum-formula-base-case listed sum does not match sum(0..n)")
    if listed_formula != prefix_sum_formula(n_value):
        fail("sum-formula-base-case listed formula does not match n*(n+1)/2")
    if listed_sum != listed_formula:
        fail("sum-formula-base-case does not satisfy the property")

    step = checks["sum-formula-step-bounded"]
    if step["expected_result"] != "unsat":
        fail("sum-formula-step-bounded must expect unsat")
    max_k = require_bounded_induction_limit("sum-formula-step-bounded", step.get("data", {}), "max_k")
    for k_value in range(max_k + 1):
        if prefix_sum_property_holds(k_value) and not prefix_sum_property_holds(k_value + 1):
            fail("sum-formula-step-bounded found a step counterexample")

    conclusion = checks["sum-formula-conclusion-bounded"]
    if conclusion["expected_result"] != "unsat":
        fail("sum-formula-conclusion-bounded must expect unsat")
    max_n = require_bounded_induction_limit("sum-formula-conclusion-bounded", conclusion.get("data", {}), "max_n")
    for n_value in range(max_n + 1):
        if not prefix_sum_property_holds(n_value):
            fail("sum-formula-conclusion-bounded found a formula counterexample")

    bad_step = checks["bad-step-counterexample-witness"]
    if bad_step["expected_result"] != "sat":
        fail("bad-step-counterexample-witness must expect sat")
    values = single_witness_values(bad_step, witnesses)
    property_name = values.get("property")
    require_string("bad step property", property_name)
    if property_name != "n_eq_0":
        fail("bad-step-counterexample-witness must use property n_eq_0")
    k_value = require_natural("bad step k", values.get("k"))
    p_k = require_bool("bad step p_k", values.get("p_k"))
    p_next = require_bool("bad step p_next", values.get("p_next"))
    if p_k != (k_value == 0):
        fail("bad-step-counterexample-witness p_k does not match n_eq_0")
    if p_next != (k_value + 1 == 0):
        fail("bad-step-counterexample-witness p_next does not match n_eq_0 at k+1")
    if not p_k or p_next:
        fail("bad-step-counterexample-witness does not witness a step failure")

    schema = checks["induction-schema-lean-horizon"]
    if schema["expected_result"] != "not-run":
        fail("induction-schema-lean-horizon must be not-run")
    if schema["proof_status"] != "lean-horizon":
        fail("induction-schema-lean-horizon must remain lean-horizon")
    data = schema.get("data", {})
    require_string("induction target theorem", data.get("target_theorem"))
    require_string("induction future checker", data.get("future_checker"))


def require_bool_assignment(
    context: str,
    value: Any,
    variables: list[str],
) -> dict[str, bool]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    variable_set = set(variables)
    if set(value) != variable_set:
        missing = sorted(variable_set - set(value))
        extra = sorted(set(value) - variable_set)
        fail(f"{context} must cover exactly variables; missing={missing} extra={extra}")
    return {
        variable: require_bool(f"{context}.{variable}", value[variable])
        for variable in variables
    }


def boolean_assignments(variables: list[str]) -> list[dict[str, bool]]:
    return [
        dict(zip(variables, values))
        for values in product([False, True], repeat=len(variables))
    ]


def require_boolean_variables(context: str, data: dict[str, Any], expected: list[str]) -> list[str]:
    variables = require_string_list(f"{context}.variables", data.get("variables"))
    if variables != expected:
        fail(f"{context}.variables must be exactly {expected}")
    if len(variables) > 16:
        fail(f"{context}.variables is too large for deterministic truth-table enumeration")
    return variables


def eval_boolean_literal(literal: str, assignment: dict[str, bool]) -> bool:
    if literal.startswith("!"):
        variable = literal[1:]
        if variable not in assignment:
            fail(f"literal {literal!r} references unknown variable")
        return not assignment[variable]
    if literal not in assignment:
        fail(f"literal {literal!r} references unknown variable")
    return assignment[literal]


def require_cnf_clauses(context: str, value: Any) -> list[list[str]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty list")
    clauses: list[list[str]] = []
    for clause_index, clause in enumerate(value):
        literals = require_string_list(f"{context}[{clause_index}]", clause)
        clauses.append(literals)
    return clauses


def cnf_satisfied(clauses: list[list[str]], assignment: dict[str, bool]) -> bool:
    return all(any(eval_boolean_literal(literal, assignment) for literal in clause) for clause in clauses)


def php_variable(pigeon: int, hole: int) -> str:
    return f"x_p{pigeon}_h{hole}"


def php_variables(pigeons: int, holes: int) -> list[str]:
    return [
        php_variable(pigeon, hole)
        for pigeon in range(pigeons)
        for hole in range(holes)
    ]


def php_cnf(pigeons: int, holes: int) -> list[list[str]]:
    clauses: list[list[str]] = []

    for pigeon in range(pigeons):
        clauses.append([php_variable(pigeon, hole) for hole in range(holes)])
        for left_hole in range(holes):
            for right_hole in range(left_hole + 1, holes):
                clauses.append(
                    [
                        f"!{php_variable(pigeon, left_hole)}",
                        f"!{php_variable(pigeon, right_hole)}",
                    ]
                )

    for hole in range(holes):
        for left_pigeon in range(pigeons):
            for right_pigeon in range(left_pigeon + 1, pigeons):
                clauses.append(
                    [
                        f"!{php_variable(left_pigeon, hole)}",
                        f"!{php_variable(right_pigeon, hole)}",
                    ]
                )

    return clauses


def validate_php_assignment(
    context: str,
    pigeons: int,
    holes: int,
    assignment: dict[str, bool],
) -> None:
    for pigeon in range(pigeons):
        chosen = [
            hole
            for hole in range(holes)
            if assignment[php_variable(pigeon, hole)]
        ]
        if len(chosen) != 1:
            fail(f"{context}: pigeon {pigeon} must choose exactly one hole")

    for hole in range(holes):
        occupants = [
            pigeon
            for pigeon in range(pigeons)
            if assignment[php_variable(pigeon, hole)]
        ]
        if len(occupants) > 1:
            fail(f"{context}: hole {hole} receives multiple pigeons")


def validate_proof_methods_refutation(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    sat_control = checks["php-2-2-sat"]
    if sat_control["expected_result"] != "sat":
        fail("php-2-2-sat must expect sat")
    if sat_control.get("proof_status") != "checked":
        fail("php-2-2-sat proof_status must be checked")
    values = single_witness_values(sat_control, witnesses)
    pigeons = require_counting_int("php-2-2-sat pigeons", values.get("pigeons"))
    holes = require_counting_int("php-2-2-sat holes", values.get("holes"))
    if (pigeons, holes) != (2, 2):
        fail("php-2-2-sat must use PHP(2,2)")
    assignment = require_bool_assignment(
        "php-2-2-sat assignment",
        values.get("assignment"),
        php_variables(pigeons, holes),
    )
    validate_php_assignment("php-2-2-sat", pigeons, holes, assignment)

    unsat_row = checks["php-3-2-unsat"]
    if unsat_row["expected_result"] != "unsat":
        fail("php-3-2-unsat must expect unsat")
    if unsat_row.get("proof_status") != "checked":
        fail("php-3-2-unsat proof_status must be checked")
    data = unsat_row.get("data", {})
    if not isinstance(data, dict):
        fail("php-3-2-unsat data must be an object")
    pigeons = require_counting_int("php-3-2-unsat pigeons", data.get("pigeons"))
    holes = require_counting_int("php-3-2-unsat holes", data.get("holes"))
    if (pigeons, holes) != (3, 2):
        fail("php-3-2-unsat must use PHP(3,2)")
    if pigeons <= holes:
        fail("php-3-2-unsat must use more pigeons than holes")

    variables = require_boolean_variables(
        "php-3-2-unsat",
        data,
        php_variables(pigeons, holes),
    )
    clauses = require_cnf_clauses("php-3-2-unsat.clauses", data.get("clauses"))
    if clauses != php_cnf(pigeons, holes):
        fail("php-3-2-unsat clauses are not the deterministic PHP CNF")
    if has_injective_placement(pigeons, holes):
        fail("php-3-2-unsat unexpectedly has an injective placement")
    for assignment in boolean_assignments(variables):
        if cnf_satisfied(clauses, assignment):
            fail("php-3-2-unsat CNF is satisfied by an assignment")


def require_predicate_table(context: str, universe: list[str], value: Any) -> dict[str, bool]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    universe_set = set(universe)
    keys = set(value)
    missing = sorted(universe_set - keys)
    extra = sorted(keys - universe_set)
    if missing or extra:
        fail(f"{context} must cover exactly the universe; missing={missing} extra={extra}")
    return {
        element: require_bool(f"{context}.{element}", value[element])
        for element in universe
    }


def predicate_valuations(universe: list[str]) -> list[dict[str, bool]]:
    if len(universe) > 16:
        fail("finite predicate valuation universe is too large for deterministic enumeration")
    return [
        dict(zip(universe, values))
        for values in product([False, True], repeat=len(universe))
    ]


def validate_finite_predicate(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    forall = checks["forall-predicate-finite-replay"]
    if forall["expected_result"] != "sat":
        fail("forall-predicate-finite-replay must expect sat")
    values = single_witness_values(forall, witnesses)
    universe = require_string_list("forall predicate universe", values.get("universe"))
    predicate = require_predicate_table("forall predicate table", universe, values.get("predicate"))
    if not all(predicate[element] for element in universe):
        fail("forall-predicate-finite-replay predicate table does not satisfy forall x. P(x)")

    exists = checks["exists-predicate-finite-replay"]
    if exists["expected_result"] != "sat":
        fail("exists-predicate-finite-replay must expect sat")
    values = single_witness_values(exists, witnesses)
    universe = require_string_list("exists predicate universe", values.get("universe"))
    predicate = require_predicate_table("exists predicate table", universe, values.get("predicate"))
    witness = values.get("witness_element")
    require_string("exists predicate witness_element", witness)
    if witness not in universe:
        fail("exists-predicate-finite-replay witness_element is outside the universe")
    if not predicate[witness]:
        fail("exists-predicate-finite-replay witness_element does not satisfy P")
    if not any(predicate[element] for element in universe):
        fail("exists-predicate-finite-replay predicate table does not satisfy exists x. P(x)")

    implication = checks["forall-implies-exists-finite"]
    if implication["expected_result"] != "unsat":
        fail("forall-implies-exists-finite must expect unsat")
    universe = require_string_list("forall-implies-exists-finite.universe", implication.get("data", {}).get("universe"))
    if not universe:
        fail("forall-implies-exists-finite universe must be non-empty")
    for valuation in predicate_valuations(universe):
        if all(valuation[element] for element in universe) and not any(valuation[element] for element in universe):
            fail("forall-implies-exists-finite found a finite counterexample")

    not_forall = checks["exists-not-forall-counterexample"]
    if not_forall["expected_result"] != "sat":
        fail("exists-not-forall-counterexample must expect sat")
    values = single_witness_values(not_forall, witnesses)
    universe = require_string_list("exists-not-forall universe", values.get("universe"))
    predicate = require_predicate_table("exists-not-forall predicate table", universe, values.get("predicate"))
    witness = values.get("witness_element")
    counterexample = values.get("counterexample_element")
    require_string("exists-not-forall witness_element", witness)
    require_string("exists-not-forall counterexample_element", counterexample)
    if witness not in universe or counterexample not in universe:
        fail("exists-not-forall witness/counterexample element is outside the universe")
    if not predicate[witness]:
        fail("exists-not-forall witness_element does not satisfy P")
    if predicate[counterexample]:
        fail("exists-not-forall counterexample_element unexpectedly satisfies P")
    if not any(predicate[element] for element in universe):
        fail("exists-not-forall predicate table does not satisfy exists x. P(x)")
    if all(predicate[element] for element in universe):
        fail("exists-not-forall predicate table unexpectedly satisfies forall x. P(x)")

    asymmetry = checks["binary-relation-symmetry-counterexample"]
    if asymmetry["expected_result"] != "sat":
        fail("binary-relation-symmetry-counterexample must expect sat")
    values = single_witness_values(asymmetry, witnesses)
    universe = require_string_list("binary relation universe", values.get("universe"))
    pairs = require_pair_set("binary relation pairs", values.get("pairs"), set(universe), set(universe))
    pair_value = values.get("counterexample_pair")
    if not isinstance(pair_value, list) or len(pair_value) != 2:
        fail("binary relation counterexample_pair must be a two-element list")
    left, right = pair_value
    require_string("binary relation counterexample_pair[0]", left)
    require_string("binary relation counterexample_pair[1]", right)
    if left not in universe or right not in universe:
        fail("binary relation counterexample_pair references an element outside the universe")
    if (left, right) not in pairs:
        fail("binary-relation-symmetry-counterexample pair is not present")
    if (right, left) in pairs:
        fail("binary-relation-symmetry-counterexample reverse pair is present")

    horizon = checks["general-first-order-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-first-order-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-first-order-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general-first-order target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general-first-order future_checker", data.get("future_checker"))


def validate_logic_basics(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    and_witness = checks["and-formula-sat-witness"]
    if and_witness["expected_result"] != "sat":
        fail("and-formula-sat-witness must expect sat")
    values = single_witness_values(and_witness, witnesses)
    assignment = require_bool_assignment("and witness assignment", values.get("assignment"), ["p", "q"])
    if not (assignment["p"] and assignment["q"]):
        fail("and-formula-sat-witness assignment does not satisfy p and q")

    excluded_middle = checks["excluded-middle-no-counterexample"]
    if excluded_middle["expected_result"] != "unsat":
        fail("excluded-middle-no-counterexample must expect unsat")
    variables = require_boolean_variables("excluded-middle-no-counterexample", excluded_middle.get("data", {}), ["p"])
    for assignment in boolean_assignments(variables):
        if not (assignment["p"] or not assignment["p"]):
            fail("excluded-middle-no-counterexample found a counterexample")

    contradiction = checks["contradiction-unsat"]
    if contradiction["expected_result"] != "unsat":
        fail("contradiction-unsat must expect unsat")
    variables = require_boolean_variables("contradiction-unsat", contradiction.get("data", {}), ["p"])
    for assignment in boolean_assignments(variables):
        if assignment["p"] and not assignment["p"]:
            fail("contradiction-unsat found a satisfying assignment")

    demorgan = checks["demorgan-equivalence-no-counterexample"]
    if demorgan["expected_result"] != "unsat":
        fail("demorgan-equivalence-no-counterexample must expect unsat")
    variables = require_boolean_variables("demorgan-equivalence-no-counterexample", demorgan.get("data", {}), ["p", "q"])
    for assignment in boolean_assignments(variables):
        left = not (assignment["p"] and assignment["q"])
        right = (not assignment["p"]) or (not assignment["q"])
        if left != right:
            fail("demorgan-equivalence-no-counterexample found a counterexample")

    cnf = checks["tiny-cnf-refutation"]
    if cnf["expected_result"] != "unsat":
        fail("tiny-cnf-refutation must expect unsat")
    data = cnf.get("data", {})
    variables = require_boolean_variables("tiny-cnf-refutation", data, ["p", "q"])
    clauses = require_cnf_clauses("tiny-cnf-refutation.clauses", data.get("clauses"))
    expected_clauses = [["p"], ["!p", "q"], ["!q"]]
    if clauses != expected_clauses:
        fail("tiny-cnf-refutation clauses must match the documented CNF")
    for assignment in boolean_assignments(variables):
        if cnf_satisfied(clauses, assignment):
            fail("tiny-cnf-refutation found a satisfying assignment")


def require_fraction(context: str, value: Any) -> Fraction:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a non-empty fraction string")
    try:
        return Fraction(value)
    except ValueError as error:
        fail(f"{context} is not a valid exact fraction: {error}")


def require_fraction_vector(context: str, value: Any) -> list[Fraction]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty vector")
    return [require_fraction(f"{context}[{index}]", item) for index, item in enumerate(value)]


def normalize_polynomial(polynomial: list[Fraction]) -> list[Fraction]:
    normalized = list(polynomial)
    while len(normalized) > 1 and normalized[-1] == 0:
        normalized.pop()
    return normalized


def require_polynomial(context: str, value: Any) -> list[Fraction]:
    return normalize_polynomial(require_fraction_vector(context, value))


def polynomial_mul(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    result = [Fraction(0) for _ in range(len(left) + len(right) - 1)]
    for left_index, left_coeff in enumerate(left):
        for right_index, right_coeff in enumerate(right):
            result[left_index + right_index] += left_coeff * right_coeff
    return normalize_polynomial(result)


def polynomial_add(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    width = max(len(left), len(right))
    result = [Fraction(0) for _ in range(width)]
    for index, coefficient in enumerate(left):
        result[index] += coefficient
    for index, coefficient in enumerate(right):
        result[index] += coefficient
    return normalize_polynomial(result)


def polynomial_derivative(polynomial: list[Fraction]) -> list[Fraction]:
    if len(polynomial) == 1:
        return [Fraction(0)]
    return normalize_polynomial([
        coefficient * index
        for index, coefficient in enumerate(polynomial[1:], start=1)
    ])


def polynomial_eval(polynomial: list[Fraction], point: Fraction) -> Fraction:
    value = Fraction(0)
    for coefficient in reversed(polynomial):
        value = value * point + coefficient
    return value


def validate_polynomial_identities(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    binomial = checks["binomial-square-identity"]
    if binomial["expected_result"] != "sat":
        fail("binomial-square-identity must expect sat")
    values = single_witness_values(binomial, witnesses)
    factor = require_polynomial("binomial factor", values.get("factor"))
    expanded = require_polynomial("binomial expanded", values.get("expanded"))
    if polynomial_mul(factor, factor) != expanded:
        fail("binomial-square-identity expansion does not match factor * factor")

    factor_theorem = checks["factor-theorem-root-witness"]
    if factor_theorem["expected_result"] != "sat":
        fail("factor-theorem-root-witness must expect sat")
    values = single_witness_values(factor_theorem, witnesses)
    polynomial = require_polynomial("factor theorem polynomial", values.get("polynomial"))
    root = require_fraction("factor theorem root", values.get("root"))
    factor = require_polynomial("factor theorem factor", values.get("factor"))
    quotient = require_polynomial("factor theorem quotient", values.get("quotient"))
    if polynomial_eval(polynomial, root) != 0:
        fail("factor-theorem-root-witness root does not evaluate to zero")
    expected_linear_factor = normalize_polynomial([-root, Fraction(1)])
    if factor != expected_linear_factor:
        fail("factor-theorem-root-witness factor must be x - root")
    if polynomial_mul(factor, quotient) != polynomial:
        fail("factor-theorem-root-witness factor * quotient does not reconstruct polynomial")

    false_root = checks["false-rational-root-rejected"]
    if false_root["expected_result"] != "unsat":
        fail("false-rational-root-rejected must expect unsat")
    values = single_witness_values(false_root, witnesses)
    polynomial = require_polynomial("false root polynomial", values.get("polynomial"))
    candidate = require_fraction("false root candidate", values.get("candidate_root"))
    if polynomial_eval(polynomial, candidate) == 0:
        fail("false-rational-root-rejected candidate unexpectedly is a root")


def require_fraction_matrix(context: str, value: Any) -> list[list[Fraction]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty matrix")
    matrix = [
        require_fraction_vector(f"{context}[{row_index}]", row)
        for row_index, row in enumerate(value)
    ]
    width = len(matrix[0])
    for row_index, row in enumerate(matrix):
        if len(row) != width:
            fail(f"{context}[{row_index}] must have width {width}")
    return matrix


def require_mat_vec_shape(context: str, matrix: list[list[Fraction]], vector: list[Fraction]) -> None:
    if len(matrix[0]) != len(vector):
        fail(f"{context} matrix width must match vector length")


def require_mat_mul_shape(
    context: str,
    left: list[list[Fraction]],
    right: list[list[Fraction]],
) -> None:
    if len(left[0]) != len(right):
        fail(f"{context} left width must match right height")


def mat_vec(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((coefficient * vector[index] for index, coefficient in enumerate(row)), Fraction(0))
        for row in matrix
    ]


def mat_mul(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    columns = list(zip(*right))
    return [
        [sum((a * b for a, b in zip(row, column)), Fraction(0)) for column in columns]
        for row in left
    ]


def require_square_matrix(context: str, matrix: list[list[Fraction]]) -> None:
    if len(matrix) != len(matrix[0]):
        fail(f"{context} must be square")


def validate_lu_shape(l_matrix: list[list[Fraction]], u_matrix: list[list[Fraction]]) -> None:
    require_square_matrix("L matrix", l_matrix)
    require_square_matrix("U matrix", u_matrix)
    if len(l_matrix) != len(u_matrix):
        fail("L and U matrices must have the same dimension")
    dimension = len(l_matrix)
    for row_index in range(dimension):
        if l_matrix[row_index][row_index] != 1:
            fail("L matrix must have unit diagonal")
        for col_index in range(row_index + 1, dimension):
            if l_matrix[row_index][col_index] != 0:
                fail("L matrix must be lower triangular")
        for col_index in range(row_index):
            if u_matrix[row_index][col_index] != 0:
                fail("U matrix must be upper triangular")


def validate_rationals_lra(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    density = checks["density-between-witness"]
    if density["expected_result"] != "sat":
        fail("density-between-witness must expect sat")
    values = single_witness_values(density, witnesses)
    a = require_fraction("density a", values.get("a"))
    b = require_fraction("density b", values.get("b"))
    midpoint = require_fraction("density midpoint", values.get("midpoint"))
    if not a < midpoint < b:
        fail("density witness must satisfy a < midpoint < b")
    if midpoint != (a + b) / 2:
        fail("density midpoint must be exactly (a + b) / 2")

    inverse = checks["additive-inverse-witness"]
    if inverse["expected_result"] != "sat":
        fail("additive-inverse-witness must expect sat")
    values = single_witness_values(inverse, witnesses)
    x = require_fraction("inverse x", values.get("x"))
    neg_x = require_fraction("inverse inverse", values.get("inverse"))
    total = require_fraction("inverse sum", values.get("sum"))
    if x + neg_x != total or total != 0:
        fail("additive inverse witness must sum to exactly zero")

    trichotomy = checks["trichotomy-fixed-unsat"]
    if trichotomy["expected_result"] != "unsat":
        fail("trichotomy-fixed-unsat must expect unsat")
    data = trichotomy.get("data", {})
    left = require_fraction("trichotomy left", data.get("left"))
    right = require_fraction("trichotomy right", data.get("right"))
    relations = [left < right, left == right, left > right]
    if sum(1 for relation in relations if relation) != 1:
        fail("trichotomy fixed pair must satisfy exactly one relation")

    transitivity = checks["order-transitivity-fixed-unsat"]
    if transitivity["expected_result"] != "unsat":
        fail("order-transitivity-fixed-unsat must expect unsat")
    data = transitivity.get("data", {})
    lower = require_fraction("transitivity a", data.get("a"))
    middle = require_fraction("transitivity b", data.get("b"))
    upper = require_fraction("transitivity c", data.get("c"))
    if not (lower < middle and middle < upper):
        fail("transitivity fixed data must satisfy a < b < c")
    if not lower < upper:
        fail("transitivity fixed data unexpectedly violates a < c")


def require_quadratic(context: str, value: Any) -> list[Fraction]:
    polynomial = require_polynomial(context, value)
    if len(polynomial) != 3:
        fail(f"{context} must be a quadratic polynomial with three coefficients")
    if polynomial[2] == 0:
        fail(f"{context} quadratic coefficient must be nonzero")
    return polynomial


def quadratic_discriminant(polynomial: list[Fraction]) -> Fraction:
    constant, linear, quadratic = polynomial
    return linear * linear - 4 * quadratic * constant


def validate_reals_rcf_shadow(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    midpoint_check = checks["ordered-field-midpoint-witness"]
    if midpoint_check["expected_result"] != "sat":
        fail("ordered-field-midpoint-witness must expect sat")
    values = single_witness_values(midpoint_check, witnesses)
    left = require_fraction("real midpoint left", values.get("left"))
    right = require_fraction("real midpoint right", values.get("right"))
    midpoint = require_fraction("real midpoint midpoint", values.get("midpoint"))
    if not left < midpoint < right:
        fail("ordered-field-midpoint-witness must satisfy left < midpoint < right")
    if midpoint != (left + right) / 2:
        fail("ordered-field-midpoint-witness midpoint must equal (left + right) / 2")

    product_check = checks["nra-product-threshold-witness"]
    if product_check["expected_result"] != "sat":
        fail("nra-product-threshold-witness must expect sat")
    values = single_witness_values(product_check, witnesses)
    x_value = require_fraction("product witness x", values.get("x"))
    y_value = require_fraction("product witness y", values.get("y"))
    lower_bound = require_fraction("product witness lower_bound", values.get("lower_bound"))
    product_value = require_fraction("product witness product", values.get("product"))
    if product_value != x_value * y_value:
        fail("nra-product-threshold-witness product does not equal x * y")
    if x_value < lower_bound or y_value < lower_bound:
        fail("nra-product-threshold-witness violates the lower-bound assumptions")
    if lower_bound != 1:
        fail("nra-product-threshold-witness currently documents the fixed lower bound 1")
    if product_value < lower_bound:
        fail("nra-product-threshold-witness product violates the threshold")

    root_check = checks["quadratic-root-real-witness"]
    if root_check["expected_result"] != "sat":
        fail("quadratic-root-real-witness must expect sat")
    values = single_witness_values(root_check, witnesses)
    polynomial = require_quadratic("real quadratic root polynomial", values.get("polynomial"))
    root = require_fraction("real quadratic root", values.get("root"))
    if polynomial_eval(polynomial, root) != 0:
        fail("quadratic-root-real-witness root does not evaluate to zero")

    square_check = checks["square-nonnegative-unsat"]
    if square_check["expected_result"] != "unsat":
        fail("square-nonnegative-unsat must expect unsat")
    data = square_check.get("data", {})
    polynomial = require_quadratic("square-nonnegative polynomial", data.get("polynomial"))
    relation = data.get("relation")
    certificate = data.get("certificate")
    require_string("square-nonnegative relation", relation)
    require_string("square-nonnegative certificate", certificate)
    bound = require_fraction("square-nonnegative bound", data.get("bound"))
    if polynomial != [Fraction(0), Fraction(0), Fraction(1)]:
        fail("square-nonnegative-unsat must use the fixed polynomial x^2")
    if relation != "lt" or bound != 0 or certificate != "square_nonnegative":
        fail("square-nonnegative-unsat must document the fixed x^2 < 0 certificate")

    discriminant_check = checks["negative-discriminant-no-real-root"]
    if discriminant_check["expected_result"] != "unsat":
        fail("negative-discriminant-no-real-root must expect unsat")
    data = discriminant_check.get("data", {})
    polynomial = require_quadratic("negative-discriminant polynomial", data.get("polynomial"))
    relation = data.get("relation")
    require_string("negative-discriminant relation", relation)
    bound = require_fraction("negative-discriminant bound", data.get("bound"))
    expected_discriminant = require_fraction(
        "negative-discriminant expected_discriminant",
        data.get("expected_discriminant"),
    )
    actual_discriminant = quadratic_discriminant(polynomial)
    if relation != "eq" or bound != 0:
        fail("negative-discriminant-no-real-root must document a polynomial = 0 row")
    if actual_discriminant != expected_discriminant:
        fail("negative-discriminant-no-real-root discriminant does not match expected value")
    if actual_discriminant >= 0:
        fail("negative-discriminant-no-real-root requires a negative discriminant")

    horizon = checks["real-completeness-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("real-completeness-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("real-completeness-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("real completeness target_theorem_shape", data.get("target_theorem_shape"))
    require_string("real completeness future_checker", data.get("future_checker"))


def require_fraction_sequence(context: str, value: Any) -> list[Fraction]:
    return require_fraction_vector(context, value)


def require_nonnegative_int(context: str, value: Any) -> int:
    number = require_int(context, value)
    if number < 0:
        fail(f"{context} must be nonnegative")
    return number


def validate_sequence_limit_shadow(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    reciprocal = checks["reciprocal-tail-bounded-epsilon"]
    if reciprocal["expected_result"] != "sat":
        fail("reciprocal-tail-bounded-epsilon must expect sat")
    values = single_witness_values(reciprocal, witnesses)
    limit = require_fraction("reciprocal tail limit", values.get("limit"))
    epsilon = require_fraction("reciprocal tail epsilon", values.get("epsilon"))
    start_index = require_nonnegative_int("reciprocal tail start_index", values.get("start_index"))
    horizon = require_nonnegative_int("reciprocal tail horizon", values.get("horizon"))
    sequence = require_fraction_sequence("reciprocal tail values", values.get("values"))
    if epsilon <= 0:
        fail("reciprocal-tail-bounded-epsilon epsilon must be positive")
    if start_index > horizon:
        fail("reciprocal-tail-bounded-epsilon start_index must be <= horizon")
    if len(sequence) != horizon + 1:
        fail("reciprocal-tail-bounded-epsilon values must cover indices 0..horizon")
    for index, value in enumerate(sequence):
        expected_value = Fraction(1, index + 1)
        if value != expected_value:
            fail(f"reciprocal-tail-bounded-epsilon value {index} does not equal 1/(n+1)")
    for value in sequence[start_index : horizon + 1]:
        if abs(value - limit) >= epsilon:
            fail("reciprocal-tail-bounded-epsilon found a finite tail counterexample")

    counterexample = checks["constant-one-limit-counterexample"]
    if counterexample["expected_result"] != "sat":
        fail("constant-one-limit-counterexample must expect sat")
    values = single_witness_values(counterexample, witnesses)
    limit = require_fraction("constant counterexample limit", values.get("limit"))
    epsilon = require_fraction("constant counterexample epsilon", values.get("epsilon"))
    index = require_nonnegative_int("constant counterexample index", values.get("index"))
    value = require_fraction("constant counterexample value", values.get("value"))
    if epsilon <= 0:
        fail("constant-one-limit-counterexample epsilon must be positive")
    if value != 1:
        fail("constant-one-limit-counterexample documents the fixed constant-one sequence")
    if abs(value - limit) < epsilon:
        fail("constant-one-limit-counterexample is unexpectedly within epsilon")

    monotone = checks["monotone-bounded-prefix"]
    if monotone["expected_result"] != "sat":
        fail("monotone-bounded-prefix must expect sat")
    values = single_witness_values(monotone, witnesses)
    upper_bound = require_fraction("monotone prefix upper_bound", values.get("upper_bound"))
    sequence = require_fraction_sequence("monotone prefix values", values.get("values"))
    if len(sequence) < 2:
        fail("monotone-bounded-prefix requires at least two values")
    for index, value in enumerate(sequence):
        expected_value = Fraction(index, index + 1)
        if value != expected_value:
            fail(f"monotone-bounded-prefix value {index} does not equal n/(n+1)")
        if value >= upper_bound:
            fail("monotone-bounded-prefix value violates the upper bound")
    for left, right in zip(sequence, sequence[1:]):
        if not left < right:
            fail("monotone-bounded-prefix is not strictly increasing")

    geometric = checks["geometric-partial-sum-identity"]
    if geometric["expected_result"] != "sat":
        fail("geometric-partial-sum-identity must expect sat")
    values = single_witness_values(geometric, witnesses)
    ratio = require_fraction("geometric ratio", values.get("ratio"))
    n_value = require_nonnegative_int("geometric n", values.get("n"))
    partial_sum = require_fraction("geometric partial_sum", values.get("partial_sum"))
    closed_form = require_fraction("geometric closed_form", values.get("closed_form"))
    if ratio == 1:
        fail("geometric-partial-sum-identity requires ratio != 1")
    computed_sum = sum((ratio**index for index in range(n_value + 1)), Fraction(0))
    computed_closed = (1 - ratio ** (n_value + 1)) / (1 - ratio)
    if partial_sum != computed_sum:
        fail("geometric-partial-sum-identity partial_sum is incorrect")
    if closed_form != computed_closed:
        fail("geometric-partial-sum-identity closed_form is incorrect")
    if partial_sum != closed_form:
        fail("geometric-partial-sum-identity partial_sum and closed_form differ")

    cauchy = checks["bounded-cauchy-tail-no-counterexample"]
    if cauchy["expected_result"] != "unsat":
        fail("bounded-cauchy-tail-no-counterexample must expect unsat")
    data = cauchy.get("data", {})
    epsilon = require_fraction("bounded cauchy epsilon", data.get("epsilon"))
    sequence = require_fraction_sequence("bounded cauchy values", data.get("values"))
    if epsilon <= 0:
        fail("bounded-cauchy-tail-no-counterexample epsilon must be positive")
    for left in sequence:
        for right in sequence:
            if abs(left - right) >= epsilon:
                fail("bounded-cauchy-tail-no-counterexample found a finite pairwise counterexample")

    horizon = checks["general-limit-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-limit-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-limit-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general limit target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general limit future_checker", data.get("future_checker"))


def validate_calculus_algebraic_shadow(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    derivative_check = checks["polynomial-derivative-coefficients"]
    if derivative_check["expected_result"] != "sat":
        fail("polynomial-derivative-coefficients must expect sat")
    values = single_witness_values(derivative_check, witnesses)
    polynomial = require_polynomial("calculus derivative polynomial", values.get("polynomial"))
    derivative = require_polynomial("calculus derivative coefficients", values.get("derivative"))
    if polynomial_derivative(polynomial) != derivative:
        fail("polynomial-derivative-coefficients derivative list is incorrect")

    product_rule = checks["product-rule-polynomial-identity"]
    if product_rule["expected_result"] != "sat":
        fail("product-rule-polynomial-identity must expect sat")
    values = single_witness_values(product_rule, witnesses)
    f_poly = require_polynomial("product rule f", values.get("f"))
    g_poly = require_polynomial("product rule g", values.get("g"))
    product_derivative = require_polynomial(
        "product rule product_derivative",
        values.get("product_derivative"),
    )
    product_rule_rhs = require_polynomial(
        "product rule product_rule_rhs",
        values.get("product_rule_rhs"),
    )
    actual_product_derivative = polynomial_derivative(polynomial_mul(f_poly, g_poly))
    actual_rhs = polynomial_add(
        polynomial_mul(polynomial_derivative(f_poly), g_poly),
        polynomial_mul(f_poly, polynomial_derivative(g_poly)),
    )
    if product_derivative != actual_product_derivative:
        fail("product-rule-polynomial-identity product_derivative is incorrect")
    if product_rule_rhs != actual_rhs:
        fail("product-rule-polynomial-identity product_rule_rhs is incorrect")
    if product_derivative != product_rule_rhs:
        fail("product-rule-polynomial-identity sides differ")

    tangent = checks["tangent-line-value-witness"]
    if tangent["expected_result"] != "sat":
        fail("tangent-line-value-witness must expect sat")
    values = single_witness_values(tangent, witnesses)
    polynomial = require_polynomial("tangent polynomial", values.get("polynomial"))
    point = require_fraction("tangent point", values.get("point"))
    target_x = require_fraction("tangent target_x", values.get("target_x"))
    derivative_at_point = require_fraction("tangent derivative_at_point", values.get("derivative_at_point"))
    tangent_value = require_fraction("tangent tangent_value", values.get("tangent_value"))
    actual_derivative_at_point = polynomial_eval(polynomial_derivative(polynomial), point)
    if derivative_at_point != actual_derivative_at_point:
        fail("tangent-line-value-witness derivative_at_point is incorrect")
    expected_tangent = polynomial_eval(polynomial, point) + derivative_at_point * (target_x - point)
    if tangent_value != expected_tangent:
        fail("tangent-line-value-witness tangent_value is incorrect")

    critical = checks["convex-quadratic-critical-point"]
    if critical["expected_result"] != "sat":
        fail("convex-quadratic-critical-point must expect sat")
    values = single_witness_values(critical, witnesses)
    polynomial = require_quadratic("convex critical polynomial", values.get("polynomial"))
    critical_point = require_fraction("convex critical_point", values.get("critical_point"))
    value = require_fraction("convex value", values.get("value"))
    second_derivative = require_fraction("convex second_derivative", values.get("second_derivative"))
    derivative = polynomial_derivative(polynomial)
    actual_second = polynomial_derivative(derivative)
    if polynomial_eval(derivative, critical_point) != 0:
        fail("convex-quadratic-critical-point derivative is not zero at critical_point")
    if polynomial_eval(polynomial, critical_point) != value:
        fail("convex-quadratic-critical-point value is incorrect")
    if polynomial_eval(actual_second, critical_point) != second_derivative:
        fail("convex-quadratic-critical-point second_derivative is incorrect")
    if second_derivative <= 0:
        fail("convex-quadratic-critical-point must have positive second derivative")

    false_derivative = checks["false-derivative-value-rejected"]
    if false_derivative["expected_result"] != "unsat":
        fail("false-derivative-value-rejected must expect unsat")
    data = false_derivative.get("data", {})
    polynomial = require_polynomial("false derivative polynomial", data.get("polynomial"))
    point = require_fraction("false derivative point", data.get("point"))
    claimed = require_fraction("false derivative claimed_derivative", data.get("claimed_derivative"))
    actual = polynomial_eval(polynomial_derivative(polynomial), point)
    if actual == claimed:
        fail("false-derivative-value-rejected claimed derivative unexpectedly matches")

    horizon = checks["general-calculus-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-calculus-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-calculus-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general calculus target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general calculus future_checker", data.get("future_checker"))


def validate_linear_algebra_rational(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    solution = checks["matrix-vector-solution"]
    if solution["expected_result"] != "sat":
        fail("matrix-vector-solution must expect sat")
    values = single_witness_values(solution, witnesses)
    matrix = require_fraction_matrix("matrix-vector matrix", values.get("matrix"))
    vector = require_fraction_vector("matrix-vector solution", values.get("solution"))
    rhs = require_fraction_vector("matrix-vector rhs", values.get("rhs"))
    require_mat_vec_shape("matrix-vector solution", matrix, vector)
    if len(matrix) != len(rhs):
        fail("matrix-vector matrix height must match rhs length")
    if mat_vec(matrix, vector) != rhs:
        fail("matrix-vector witness does not satisfy Ax = b")

    lu = checks["lu-factorization-witness"]
    if lu["expected_result"] != "sat":
        fail("lu-factorization-witness must expect sat")
    values = single_witness_values(lu, witnesses)
    matrix = require_fraction_matrix("LU matrix", values.get("matrix"))
    l_matrix = require_fraction_matrix("L matrix", values.get("l"))
    u_matrix = require_fraction_matrix("U matrix", values.get("u"))
    require_square_matrix("LU target matrix", matrix)
    validate_lu_shape(l_matrix, u_matrix)
    require_mat_mul_shape("LU factorization", l_matrix, u_matrix)
    if mat_mul(l_matrix, u_matrix) != matrix:
        fail("LU witness does not satisfy L*U = A")

    inconsistent = checks["singular-system-inconsistent"]
    if inconsistent["expected_result"] != "unsat":
        fail("singular-system-inconsistent must expect unsat")
    data = inconsistent.get("data", {})
    row = require_fraction_vector("inconsistent row", data.get("row"))
    rhs = require_fraction("inconsistent rhs", data.get("rhs"))
    multiple = require_fraction("inconsistent multiple", data.get("multiple"))
    scaled_row = require_fraction_vector("inconsistent scaled row", data.get("scaled_row"))
    scaled_rhs = require_fraction("inconsistent scaled rhs", data.get("scaled_rhs"))
    if len(row) != len(scaled_row):
        fail("inconsistent row and scaled row must have the same width")
    if scaled_row != [multiple * item for item in row]:
        fail("inconsistent scaled row must equal multiple times the original row")
    if scaled_rhs == multiple * rhs:
        fail("inconsistent scaled rhs must contradict the scaled original rhs")


def l1_norm(vector: list[Fraction]) -> Fraction:
    return sum((abs(item) for item in vector), Fraction(0))


def linf_norm(vector: list[Fraction]) -> Fraction:
    return max(abs(item) for item in vector)


def require_same_vector_length(context: str, left: list[Fraction], right: list[Fraction]) -> None:
    if len(left) != len(right):
        fail(f"{context} vectors must have the same length")


def vector_sub(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    require_same_vector_length("vector subtraction", left, right)
    return [left_item - right_item for left_item, right_item in zip(left, right)]


def row_sum_norm(matrix: list[list[Fraction]]) -> Fraction:
    return max(sum((abs(item) for item in row), Fraction(0)) for row in matrix)


def validate_finite_operator(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    triangle = checks["l1-triangle-witness"]
    if triangle["expected_result"] != "sat":
        fail("l1-triangle-witness must expect sat")
    values = single_witness_values(triangle, witnesses)
    u_vector = require_fraction_vector("l1 triangle u", values.get("u"))
    v_vector = require_fraction_vector("l1 triangle v", values.get("v"))
    sum_vector = require_fraction_vector("l1 triangle sum", values.get("sum"))
    require_same_vector_length("l1 triangle u/v", u_vector, v_vector)
    require_same_vector_length("l1 triangle u/sum", u_vector, sum_vector)
    if [u + v for u, v in zip(u_vector, v_vector)] != sum_vector:
        fail("l1 triangle sum vector does not equal u + v")
    norm_u = require_fraction("l1 triangle norm_u", values.get("norm_u"))
    norm_v = require_fraction("l1 triangle norm_v", values.get("norm_v"))
    norm_sum = require_fraction("l1 triangle norm_sum", values.get("norm_sum"))
    if l1_norm(u_vector) != norm_u:
        fail("l1 triangle norm_u does not match u")
    if l1_norm(v_vector) != norm_v:
        fail("l1 triangle norm_v does not match v")
    if l1_norm(sum_vector) != norm_sum:
        fail("l1 triangle norm_sum does not match u + v")
    if norm_sum > norm_u + norm_v:
        fail("l1 triangle witness violates the triangle inequality")

    operator = checks["matrix-operator-bound"]
    if operator["expected_result"] != "sat":
        fail("matrix-operator-bound must expect sat")
    values = single_witness_values(operator, witnesses)
    matrix = require_fraction_matrix("operator matrix", values.get("matrix"))
    vector = require_fraction_vector("operator vector", values.get("vector"))
    image = require_fraction_vector("operator image", values.get("image"))
    require_mat_vec_shape("matrix operator", matrix, vector)
    if len(matrix) != len(image):
        fail("operator image length must match matrix height")
    if mat_vec(matrix, vector) != image:
        fail("operator image does not equal A*x")
    vector_norm = require_fraction("operator vector_norm", values.get("vector_norm"))
    operator_norm = require_fraction("operator operator_norm", values.get("operator_norm"))
    image_norm = require_fraction("operator image_norm", values.get("image_norm"))
    bound = require_fraction("operator bound", values.get("bound"))
    if linf_norm(vector) != vector_norm:
        fail("operator vector_norm does not match infinity norm")
    if row_sum_norm(matrix) != operator_norm:
        fail("operator operator_norm does not match row-sum norm")
    if linf_norm(image) != image_norm:
        fail("operator image_norm does not match infinity norm")
    if bound != operator_norm * vector_norm:
        fail("operator bound must equal operator_norm * vector_norm")
    if image_norm > bound:
        fail("matrix operator witness violates the claimed norm bound")

    chebyshev = checks["chebyshev-recurrence-witness"]
    if chebyshev["expected_result"] != "sat":
        fail("chebyshev-recurrence-witness must expect sat")
    values = single_witness_values(chebyshev, witnesses)
    x_value = require_fraction("chebyshev x", values.get("x"))
    chebyshev_values = require_fraction_vector(
        "chebyshev values",
        values.get("chebyshev_values"),
    )
    if len(chebyshev_values) < 2:
        fail("chebyshev values must contain at least T0 and T1")
    if chebyshev_values[0] != 1:
        fail("chebyshev T0 must be 1")
    if chebyshev_values[1] != x_value:
        fail("chebyshev T1 must equal x")
    for index in range(1, len(chebyshev_values) - 1):
        expected_next = 2 * x_value * chebyshev_values[index] - chebyshev_values[index - 1]
        if chebyshev_values[index + 1] != expected_next:
            fail(f"chebyshev T{index + 1} does not match the recurrence")


def jacobi_step(matrix: list[list[Fraction]], rhs: list[Fraction], point: list[Fraction]) -> list[Fraction]:
    require_square_matrix("Jacobi matrix", matrix)
    require_mat_vec_shape("Jacobi point", matrix, point)
    if len(matrix) != len(rhs):
        fail("Jacobi matrix height must match rhs length")
    result: list[Fraction] = []
    for row_index, row in enumerate(matrix):
        diagonal = row[row_index]
        if diagonal == 0:
            fail("Jacobi matrix diagonal entries must be nonzero")
        off_diagonal = sum(
            (coefficient * point[col_index] for col_index, coefficient in enumerate(row) if col_index != row_index),
            Fraction(0),
        )
        result.append((rhs[row_index] - off_diagonal) / diagonal)
    return result


def jacobi_contraction_bound(matrix: list[list[Fraction]]) -> Fraction:
    require_square_matrix("Jacobi contraction matrix", matrix)
    bounds: list[Fraction] = []
    for row_index, row in enumerate(matrix):
        diagonal = row[row_index]
        if diagonal == 0:
            fail("Jacobi contraction diagonal entries must be nonzero")
        bounds.append(
            sum(
                (abs(coefficient / diagonal) for col_index, coefficient in enumerate(row) if col_index != row_index),
                Fraction(0),
            )
        )
    return max(bounds)


def validate_numerical_linear_algebra(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    residual_bound = checks["residual-norm-bound-witness"]
    if residual_bound["expected_result"] != "sat":
        fail("residual-norm-bound-witness must expect sat")
    values = single_witness_values(residual_bound, witnesses)
    matrix = require_fraction_matrix("residual matrix", values.get("matrix"))
    candidate = require_fraction_vector("residual candidate", values.get("candidate"))
    rhs = require_fraction_vector("residual rhs", values.get("rhs"))
    residual = require_fraction_vector("residual vector", values.get("residual"))
    require_mat_vec_shape("residual system", matrix, candidate)
    if len(matrix) != len(rhs):
        fail("residual matrix height must match rhs length")
    computed_residual = vector_sub(mat_vec(matrix, candidate), rhs)
    if residual != computed_residual:
        fail("residual vector does not equal A*x_hat - b")
    residual_norm = require_fraction("residual infinity norm", values.get("residual_inf_norm"))
    claimed_bound = require_fraction("residual claimed bound", values.get("claimed_bound"))
    if linf_norm(residual) != residual_norm:
        fail("residual infinity norm does not match the listed residual")
    if residual_norm > claimed_bound:
        fail("residual-norm-bound-witness violates the claimed residual bound")

    solution_box = checks["solution-box-replay"]
    if solution_box["expected_result"] != "sat":
        fail("solution-box-replay must expect sat")
    values = single_witness_values(solution_box, witnesses)
    matrix = require_fraction_matrix("solution box matrix", values.get("matrix"))
    solution = require_fraction_vector("solution box exact_solution", values.get("exact_solution"))
    rhs = require_fraction_vector("solution box rhs", values.get("rhs"))
    lower_bounds = require_fraction_vector("solution box lower_bounds", values.get("lower_bounds"))
    upper_bounds = require_fraction_vector("solution box upper_bounds", values.get("upper_bounds"))
    residual = require_fraction_vector("solution box residual", values.get("residual"))
    require_mat_vec_shape("solution box system", matrix, solution)
    if len(matrix) != len(rhs):
        fail("solution box matrix height must match rhs length")
    require_same_vector_length("solution box lower/exact", lower_bounds, solution)
    require_same_vector_length("solution box upper/exact", upper_bounds, solution)
    computed_residual = vector_sub(mat_vec(matrix, solution), rhs)
    if computed_residual != residual:
        fail("solution-box-replay residual does not equal A*x - b")
    if any(item != 0 for item in residual):
        fail("solution-box-replay must use an exact zero residual")
    for index, item in enumerate(solution):
        if not lower_bounds[index] <= item <= upper_bounds[index]:
            fail("solution-box-replay exact solution lies outside the listed box")

    jacobi = checks["jacobi-contraction-witness"]
    if jacobi["expected_result"] != "sat":
        fail("jacobi-contraction-witness must expect sat")
    values = single_witness_values(jacobi, witnesses)
    matrix = require_fraction_matrix("Jacobi matrix", values.get("matrix"))
    rhs = require_fraction_vector("Jacobi rhs", values.get("rhs"))
    initial = require_fraction_vector("Jacobi initial", values.get("initial"))
    first_step = require_fraction_vector("Jacobi first_step", values.get("first_step"))
    exact_solution = require_fraction_vector("Jacobi exact_solution", values.get("exact_solution"))
    error0_norm = require_fraction("Jacobi error0_inf_norm", values.get("error0_inf_norm"))
    error1_norm = require_fraction("Jacobi error1_inf_norm", values.get("error1_inf_norm"))
    contraction_bound = require_fraction("Jacobi contraction_bound", values.get("contraction_bound"))
    if jacobi_step(matrix, rhs, initial) != first_step:
        fail("jacobi-contraction-witness first_step is not the Jacobi update")
    if mat_vec(matrix, exact_solution) != rhs:
        fail("jacobi-contraction-witness exact_solution does not solve A*x = b")
    if linf_norm(vector_sub(initial, exact_solution)) != error0_norm:
        fail("jacobi-contraction-witness error0_inf_norm is incorrect")
    if linf_norm(vector_sub(first_step, exact_solution)) != error1_norm:
        fail("jacobi-contraction-witness error1_inf_norm is incorrect")
    if jacobi_contraction_bound(matrix) != contraction_bound:
        fail("jacobi-contraction-witness contraction_bound is incorrect")
    if contraction_bound >= 1:
        fail("jacobi-contraction-witness requires a strict contraction bound")
    if error1_norm > contraction_bound * error0_norm:
        fail("jacobi-contraction-witness violates the claimed contraction inequality")

    bad_bound = checks["bad-residual-bound-rejected"]
    if bad_bound["expected_result"] != "unsat":
        fail("bad-residual-bound-rejected must expect unsat")
    data = bad_bound.get("data", {})
    matrix = require_fraction_matrix("bad residual matrix", data.get("matrix"))
    candidate = require_fraction_vector("bad residual candidate", data.get("candidate"))
    rhs = require_fraction_vector("bad residual rhs", data.get("rhs"))
    claimed_bound = require_fraction("bad residual claimed_bound", data.get("claimed_bound"))
    actual_norm = require_fraction("bad residual actual_residual_inf_norm", data.get("actual_residual_inf_norm"))
    require_mat_vec_shape("bad residual system", matrix, candidate)
    if len(matrix) != len(rhs):
        fail("bad residual matrix height must match rhs length")
    if linf_norm(vector_sub(mat_vec(matrix, candidate), rhs)) != actual_norm:
        fail("bad-residual-bound-rejected actual norm is incorrect")
    if actual_norm <= claimed_bound:
        fail("bad-residual-bound-rejected claimed bound unexpectedly holds")


def require_fraction_vector_list(context: str, value: Any) -> list[list[Fraction]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty list of vectors")
    vectors = [
        require_fraction_vector(f"{context}[{index}]", item)
        for index, item in enumerate(value)
    ]
    width = len(vectors[0])
    for index, vector in enumerate(vectors):
        if len(vector) != width:
            fail(f"{context}[{index}] must have width {width}")
    return vectors


def dot_product(left: list[Fraction], right: list[Fraction]) -> Fraction:
    require_same_vector_length("dot product", left, right)
    return sum((left_item * right_item for left_item, right_item in zip(left, right)), Fraction(0))


def scalar_vec(scalar: Fraction, vector: list[Fraction]) -> list[Fraction]:
    return [scalar * item for item in vector]


def require_same_matrix_shape(
    context: str,
    left: list[list[Fraction]],
    right: list[list[Fraction]],
) -> None:
    if len(left) != len(right) or len(left[0]) != len(right[0]):
        fail(f"{context} matrices must have the same shape")


def matrix_scale(scalar: Fraction, matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    return [[scalar * item for item in row] for row in matrix]


def matrix_add(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    require_same_matrix_shape("matrix addition", left, right)
    return [
        [left_item + right_item for left_item, right_item in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def matrix_sub(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    return matrix_add(left, matrix_scale(Fraction(-1), right))


def identity_matrix(size: int) -> list[list[Fraction]]:
    return [
        [Fraction(1) if row_index == col_index else Fraction(0) for col_index in range(size)]
        for row_index in range(size)
    ]


def zero_matrix(height: int, width: int) -> list[list[Fraction]]:
    return [[Fraction(0) for _ in range(width)] for _ in range(height)]


def characteristic_polynomial_2x2(matrix: list[list[Fraction]]) -> list[Fraction]:
    require_square_matrix("characteristic polynomial matrix", matrix)
    if len(matrix) != 2:
        fail("characteristic polynomial validator currently expects 2x2 matrices")
    return normalize_polynomial([matrix_det_2x2(matrix), -matrix_trace(matrix), Fraction(1)])


def validate_matrix_invariants(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    invariants = checks["trace-determinant-characteristic-polynomial"]
    if invariants["expected_result"] != "sat":
        fail("trace-determinant-characteristic-polynomial must expect sat")
    values = single_witness_values(invariants, witnesses)
    matrix = require_fraction_matrix("matrix invariants matrix", values.get("matrix"))
    trace = require_fraction("matrix invariants trace", values.get("trace"))
    determinant = require_fraction("matrix invariants determinant", values.get("determinant"))
    characteristic = require_polynomial(
        "matrix invariants characteristic_polynomial",
        values.get("characteristic_polynomial"),
    )
    if matrix_trace(matrix) != trace:
        fail("trace-determinant-characteristic-polynomial trace is incorrect")
    if matrix_det_2x2(matrix) != determinant:
        fail("trace-determinant-characteristic-polynomial determinant is incorrect")
    if characteristic_polynomial_2x2(matrix) != characteristic:
        fail("trace-determinant-characteristic-polynomial characteristic polynomial is incorrect")

    roots = checks["characteristic-roots-witness"]
    if roots["expected_result"] != "sat":
        fail("characteristic-roots-witness must expect sat")
    values = single_witness_values(roots, witnesses)
    matrix = require_fraction_matrix("characteristic roots matrix", values.get("matrix"))
    characteristic = require_polynomial(
        "characteristic roots characteristic_polynomial",
        values.get("characteristic_polynomial"),
    )
    eigenvalues = require_fraction_vector("characteristic roots eigenvalues", values.get("eigenvalues"))
    if characteristic_polynomial_2x2(matrix) != characteristic:
        fail("characteristic-roots-witness characteristic polynomial is incorrect")
    for eigenvalue in eigenvalues:
        if polynomial_eval(characteristic, eigenvalue) != 0:
            fail("characteristic-roots-witness listed eigenvalue is not a polynomial root")

    cayley = checks["cayley-hamilton-replay"]
    if cayley["expected_result"] != "sat":
        fail("cayley-hamilton-replay must expect sat")
    values = single_witness_values(cayley, witnesses)
    matrix = require_fraction_matrix("Cayley-Hamilton matrix", values.get("matrix"))
    matrix_square = require_fraction_matrix("Cayley-Hamilton matrix_square", values.get("matrix_square"))
    identity = require_fraction_matrix("Cayley-Hamilton identity", values.get("identity"))
    cayley_value = require_fraction_matrix("Cayley-Hamilton value", values.get("cayley_hamilton_value"))
    trace = require_fraction("Cayley-Hamilton trace", values.get("trace"))
    determinant = require_fraction("Cayley-Hamilton determinant", values.get("determinant"))
    require_square_matrix("Cayley-Hamilton matrix", matrix)
    if identity != identity_matrix(len(matrix)):
        fail("cayley-hamilton-replay identity matrix is incorrect")
    if mat_mul(matrix, matrix) != matrix_square:
        fail("cayley-hamilton-replay matrix_square is incorrect")
    computed = matrix_add(
        matrix_sub(matrix_square, matrix_scale(trace, matrix)),
        matrix_scale(determinant, identity),
    )
    if computed != cayley_value:
        fail("cayley-hamilton-replay value is incorrect")
    if cayley_value != zero_matrix(len(matrix), len(matrix[0])):
        fail("cayley-hamilton-replay must evaluate to the zero matrix")

    gershgorin = checks["gershgorin-interval-witness"]
    if gershgorin["expected_result"] != "sat":
        fail("gershgorin-interval-witness must expect sat")
    values = single_witness_values(gershgorin, witnesses)
    matrix = require_fraction_matrix("Gershgorin matrix", values.get("matrix"))
    centers = require_fraction_vector("Gershgorin centers", values.get("gershgorin_centers"))
    radii = require_fraction_vector("Gershgorin radii", values.get("gershgorin_radii"))
    intervals = require_fraction_vector_list("Gershgorin intervals", values.get("gershgorin_intervals"))
    eigenvalues = require_fraction_vector("Gershgorin eigenvalues", values.get("eigenvalues"))
    require_square_matrix("Gershgorin matrix", matrix)
    actual_centers = [matrix[index][index] for index in range(len(matrix))]
    actual_radii = [
        sum(
            (abs(entry) for col_index, entry in enumerate(row) if col_index != row_index),
            Fraction(0),
        )
        for row_index, row in enumerate(matrix)
    ]
    if centers != actual_centers:
        fail("gershgorin-interval-witness centers are incorrect")
    if radii != actual_radii:
        fail("gershgorin-interval-witness radii are incorrect")
    actual_intervals = [
        [center - radius, center + radius]
        for center, radius in zip(actual_centers, actual_radii)
    ]
    if intervals != actual_intervals:
        fail("gershgorin-interval-witness intervals are incorrect")
    for eigenvalue in eigenvalues:
        if not any(lower <= eigenvalue <= upper for lower, upper in intervals):
            fail("gershgorin-interval-witness eigenvalue lies outside all intervals")

    bad = checks["bad-characteristic-polynomial-rejected"]
    if bad["expected_result"] != "unsat":
        fail("bad-characteristic-polynomial-rejected must expect unsat")
    data = bad.get("data", {})
    matrix = require_fraction_matrix("bad characteristic matrix", data.get("matrix"))
    claimed = require_polynomial("bad characteristic claimed", data.get("claimed_characteristic_polynomial"))
    actual = require_polynomial("bad characteristic actual", data.get("actual_characteristic_polynomial"))
    witness_root = require_fraction("bad characteristic witness_root", data.get("witness_root"))
    claimed_value = require_fraction("bad characteristic claimed_value_at_witness", data.get("claimed_value_at_witness"))
    computed = characteristic_polynomial_2x2(matrix)
    if computed != actual:
        fail("bad-characteristic-polynomial-rejected actual polynomial is incorrect")
    if claimed == actual:
        fail("bad-characteristic-polynomial-rejected claimed polynomial unexpectedly matches actual")
    if polynomial_eval(actual, witness_root) != 0:
        fail("bad-characteristic-polynomial-rejected witness_root must be an actual root")
    if polynomial_eval(claimed, witness_root) != claimed_value:
        fail("bad-characteristic-polynomial-rejected claimed value is incorrect")
    if claimed_value == 0:
        fail("bad-characteristic-polynomial-rejected claimed polynomial unexpectedly vanishes at witness")


def validate_spectral_linear_algebra(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    eigenpair = checks["symmetric-eigenpair-witness"]
    if eigenpair["expected_result"] != "sat":
        fail("symmetric-eigenpair-witness must expect sat")
    values = single_witness_values(eigenpair, witnesses)
    matrix = require_fraction_matrix("eigenpair matrix", values.get("matrix"))
    eigenvalue = require_fraction("eigenpair eigenvalue", values.get("eigenvalue"))
    eigenvector = require_fraction_vector("eigenpair eigenvector", values.get("eigenvector"))
    image = require_fraction_vector("eigenpair image", values.get("image"))
    require_mat_vec_shape("eigenpair", matrix, eigenvector)
    if mat_vec(matrix, eigenvector) != image:
        fail("symmetric-eigenpair-witness image does not equal A*v")
    if scalar_vec(eigenvalue, eigenvector) != image:
        fail("symmetric-eigenpair-witness image does not equal lambda*v")

    basis = checks["orthogonal-eigenbasis-witness"]
    if basis["expected_result"] != "sat":
        fail("orthogonal-eigenbasis-witness must expect sat")
    values = single_witness_values(basis, witnesses)
    matrix = require_fraction_matrix("orthogonal basis matrix", values.get("matrix"))
    eigenvalues = require_fraction_vector("orthogonal basis eigenvalues", values.get("eigenvalues"))
    eigenvectors = require_fraction_vector_list("orthogonal basis eigenvectors", values.get("eigenvectors"))
    norm_squared = require_fraction_vector("orthogonal basis norm_squared", values.get("norm_squared"))
    dot_products = require_fraction_vector("orthogonal basis dot_products", values.get("dot_products"))
    if len(eigenvalues) != len(eigenvectors):
        fail("orthogonal-eigenbasis-witness eigenvalue/vector counts differ")
    if len(norm_squared) != len(eigenvectors):
        fail("orthogonal-eigenbasis-witness norm_squared count differs")
    require_square_matrix("orthogonal basis matrix", matrix)
    for index, vector in enumerate(eigenvectors):
        require_mat_vec_shape("orthogonal eigenvector", matrix, vector)
        if mat_vec(matrix, vector) != scalar_vec(eigenvalues[index], vector):
            fail(f"orthogonal-eigenbasis-witness vector {index} is not an eigenvector")
        if dot_product(vector, vector) != norm_squared[index]:
            fail(f"orthogonal-eigenbasis-witness norm_squared {index} is incorrect")
    actual_dots: list[Fraction] = []
    for left_index in range(len(eigenvectors)):
        for right_index in range(left_index + 1, len(eigenvectors)):
            actual_dots.append(dot_product(eigenvectors[left_index], eigenvectors[right_index]))
    if actual_dots != dot_products:
        fail("orthogonal-eigenbasis-witness dot_products are incorrect")
    if any(dot != 0 for dot in actual_dots):
        fail("orthogonal-eigenbasis-witness eigenvectors must be pairwise orthogonal")

    rayleigh = checks["rayleigh-quotient-witness"]
    if rayleigh["expected_result"] != "sat":
        fail("rayleigh-quotient-witness must expect sat")
    values = single_witness_values(rayleigh, witnesses)
    matrix = require_fraction_matrix("Rayleigh matrix", values.get("matrix"))
    vector = require_fraction_vector("Rayleigh vector", values.get("rayleigh_vector"))
    numerator = require_fraction("Rayleigh numerator", values.get("rayleigh_numerator"))
    denominator = require_fraction("Rayleigh denominator", values.get("rayleigh_denominator"))
    quotient = require_fraction("Rayleigh quotient", values.get("rayleigh_quotient"))
    require_mat_vec_shape("Rayleigh", matrix, vector)
    image = mat_vec(matrix, vector)
    if dot_product(vector, image) != numerator:
        fail("rayleigh-quotient-witness numerator is incorrect")
    if dot_product(vector, vector) != denominator:
        fail("rayleigh-quotient-witness denominator is incorrect")
    if denominator == 0:
        fail("rayleigh-quotient-witness denominator must be nonzero")
    if numerator / denominator != quotient:
        fail("rayleigh-quotient-witness quotient is incorrect")

    decomposition = checks["spectral-decomposition-witness"]
    if decomposition["expected_result"] != "sat":
        fail("spectral-decomposition-witness must expect sat")
    values = single_witness_values(decomposition, witnesses)
    matrix = require_fraction_matrix("spectral target matrix", values.get("matrix"))
    eigenvector_matrix = require_fraction_matrix("spectral eigenvector_matrix", values.get("eigenvector_matrix"))
    diagonal = require_fraction_matrix("spectral diagonal", values.get("diagonal"))
    inverse = require_fraction_matrix("spectral inverse_eigenvector_matrix", values.get("inverse_eigenvector_matrix"))
    require_mat_mul_shape("spectral P*D", eigenvector_matrix, diagonal)
    require_mat_mul_shape("spectral P*D*P^-1", mat_mul(eigenvector_matrix, diagonal), inverse)
    if mat_mul(mat_mul(eigenvector_matrix, diagonal), inverse) != matrix:
        fail("spectral-decomposition-witness P*D*P^-1 does not reconstruct A")
    identity = values.get("identity_check")
    if identity is not None:
        identity_matrix = require_fraction_matrix("spectral identity_check", identity)
        if mat_mul(eigenvector_matrix, inverse) != identity_matrix:
            fail("spectral-decomposition-witness P*P^-1 identity_check is incorrect")

    bad = checks["bad-eigenpair-rejected"]
    if bad["expected_result"] != "unsat":
        fail("bad-eigenpair-rejected must expect unsat")
    data = bad.get("data", {})
    matrix = require_fraction_matrix("bad eigenpair matrix", data.get("matrix"))
    eigenvalue = require_fraction("bad eigenpair claimed_eigenvalue", data.get("claimed_eigenvalue"))
    eigenvector = require_fraction_vector("bad eigenpair eigenvector", data.get("eigenvector"))
    image = require_fraction_vector("bad eigenpair actual_image", data.get("actual_image"))
    claimed_scaled = require_fraction_vector("bad eigenpair claimed_scaled", data.get("claimed_scaled"))
    require_mat_vec_shape("bad eigenpair", matrix, eigenvector)
    if mat_vec(matrix, eigenvector) != image:
        fail("bad-eigenpair-rejected actual_image is incorrect")
    if scalar_vec(eigenvalue, eigenvector) != claimed_scaled:
        fail("bad-eigenpair-rejected claimed_scaled is incorrect")
    if image == claimed_scaled:
        fail("bad-eigenpair-rejected claimed eigenpair unexpectedly holds")


def require_complex_pair(context: str, value: Any) -> tuple[Fraction, Fraction]:
    pair = require_fraction_vector(context, value)
    if len(pair) != 2:
        fail(f"{context} must be a two-element real/imaginary pair")
    return pair[0], pair[1]


def complex_add(
    left: tuple[Fraction, Fraction],
    right: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    return left[0] + right[0], left[1] + right[1]


def complex_mul(
    left: tuple[Fraction, Fraction],
    right: tuple[Fraction, Fraction],
) -> tuple[Fraction, Fraction]:
    return left[0] * right[0] - left[1] * right[1], left[0] * right[1] + left[1] * right[0]


def complex_conjugate(value: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return value[0], -value[1]


def complex_norm_squared(value: tuple[Fraction, Fraction]) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def validate_complex_algebraic(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    arithmetic = checks["complex-arithmetic-replay"]
    if arithmetic["expected_result"] != "sat":
        fail("complex-arithmetic-replay must expect sat")
    values = single_witness_values(arithmetic, witnesses)
    z_value = require_complex_pair("complex arithmetic z", values.get("z"))
    w_value = require_complex_pair("complex arithmetic w", values.get("w"))
    sum_value = require_complex_pair("complex arithmetic sum", values.get("sum"))
    product_value = require_complex_pair("complex arithmetic product", values.get("product"))
    if complex_add(z_value, w_value) != sum_value:
        fail("complex arithmetic sum does not match z + w")
    if complex_mul(z_value, w_value) != product_value:
        fail("complex arithmetic product does not match z * w")

    conjugate = checks["conjugate-norm-replay"]
    if conjugate["expected_result"] != "sat":
        fail("conjugate-norm-replay must expect sat")
    values = single_witness_values(conjugate, witnesses)
    z_value = require_complex_pair("conjugate norm z", values.get("z"))
    conjugate_value = require_complex_pair("conjugate norm conjugate", values.get("conjugate"))
    product_value = require_complex_pair("conjugate norm product", values.get("product"))
    norm_squared = require_fraction("conjugate norm norm_squared", values.get("norm_squared"))
    if complex_conjugate(z_value) != conjugate_value:
        fail("conjugate norm conjugate does not match z")
    if complex_norm_squared(z_value) != norm_squared:
        fail("conjugate norm norm_squared does not match z")
    if complex_mul(z_value, conjugate_value) != product_value:
        fail("conjugate norm product does not match z * conjugate(z)")
    if product_value != (norm_squared, Fraction(0)):
        fail("conjugate norm product must be norm_squared + 0i")

    root = checks["quadratic-root-witness"]
    if root["expected_result"] != "sat":
        fail("quadratic-root-witness must expect sat")
    values = single_witness_values(root, witnesses)
    z_value = require_complex_pair("quadratic root z", values.get("z"))
    z_squared = require_complex_pair("quadratic root z_squared", values.get("z_squared"))
    polynomial_value = require_complex_pair(
        "quadratic root polynomial_value",
        values.get("polynomial_value"),
    )
    if complex_mul(z_value, z_value) != z_squared:
        fail("quadratic root z_squared does not match z * z")
    if complex_add(z_squared, (Fraction(1), Fraction(0))) != polynomial_value:
        fail("quadratic root polynomial_value does not match z^2 + 1")
    if polynomial_value != (Fraction(0), Fraction(0)):
        fail("quadratic root polynomial_value must be exactly 0 + 0i")


def require_linear_variables(context: str, value: Any) -> list[str]:
    return require_string_list(context, value)


def require_linear_coefficients(
    context: str,
    value: Any,
    variables: list[str],
) -> dict[str, Fraction]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    variable_set = set(variables)
    if set(value) != variable_set:
        missing = sorted(variable_set - set(value))
        extra = sorted(set(value) - variable_set)
        fail(f"{context} must cover exactly the variables; missing={missing} extra={extra}")
    return {
        variable: require_fraction(f"{context}.{variable}", value[variable])
        for variable in variables
    }


def require_linear_constraint(
    context: str,
    value: Any,
    variables: list[str],
) -> tuple[str, dict[str, Fraction], Fraction]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    constraint_id = value.get("id")
    require_string(f"{context}.id", constraint_id)
    coefficients = require_linear_coefficients(
        f"{context}.coefficients",
        value.get("coefficients"),
        variables,
    )
    bound = require_fraction(f"{context}.bound", value.get("bound"))
    return constraint_id, coefficients, bound


def require_linear_constraints(
    context: str,
    value: Any,
    variables: list[str],
) -> list[tuple[str, dict[str, Fraction], Fraction]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty constraint list")
    constraints = [
        require_linear_constraint(f"{context}[{index}]", item, variables)
        for index, item in enumerate(value)
    ]
    ids = [constraint_id for constraint_id, _, _ in constraints]
    if len(set(ids)) != len(ids):
        fail(f"{context} repeats constraint ids")
    return constraints


def require_linear_assignment(
    context: str,
    value: Any,
    variables: list[str],
) -> dict[str, Fraction]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    variable_set = set(variables)
    if set(value) != variable_set:
        missing = sorted(variable_set - set(value))
        extra = sorted(set(value) - variable_set)
        fail(f"{context} must cover exactly the variables; missing={missing} extra={extra}")
    return {
        variable: require_fraction(f"{context}.{variable}", value[variable])
        for variable in variables
    }


def linear_value(coefficients: dict[str, Fraction], assignment: dict[str, Fraction]) -> Fraction:
    return sum((coefficient * assignment[variable] for variable, coefficient in coefficients.items()), Fraction(0))


def validate_constraints_hold(
    context: str,
    constraints: list[tuple[str, dict[str, Fraction], Fraction]],
    assignment: dict[str, Fraction],
) -> None:
    for constraint_id, coefficients, bound in constraints:
        if linear_value(coefficients, assignment) > bound:
            fail(f"{context} violates linear constraint {constraint_id}")


def validate_linear_optimization(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    feasible = checks["lp-feasible-point"]
    if feasible["expected_result"] != "sat":
        fail("lp-feasible-point must expect sat")
    values = single_witness_values(feasible, witnesses)
    variables = require_linear_variables("lp variables", values.get("variables"))
    constraints = require_linear_constraints("lp constraints", values.get("constraints"), variables)
    assignment = require_linear_assignment("lp assignment", values.get("assignment"), variables)
    validate_constraints_hold("lp-feasible-point", constraints, assignment)

    threshold = checks["objective-threshold-witness"]
    if threshold["expected_result"] != "sat":
        fail("objective-threshold-witness must expect sat")
    values = single_witness_values(threshold, witnesses)
    variables = require_linear_variables("threshold variables", values.get("variables"))
    constraints = require_linear_constraints("threshold constraints", values.get("constraints"), variables)
    assignment = require_linear_assignment("threshold assignment", values.get("assignment"), variables)
    validate_constraints_hold("objective-threshold-witness", constraints, assignment)
    threshold_data = values.get("threshold")
    if not isinstance(threshold_data, dict):
        fail("threshold data must be an object")
    threshold_coefficients = require_linear_coefficients(
        "threshold coefficients",
        threshold_data.get("coefficients"),
        variables,
    )
    lower_bound = require_fraction("threshold lower_bound", threshold_data.get("lower_bound"))
    if linear_value(threshold_coefficients, assignment) < lower_bound:
        fail("objective-threshold-witness assignment does not reach threshold")

    infeasible = checks["objective-threshold-farkas-infeasible"]
    if infeasible["expected_result"] != "unsat":
        fail("objective-threshold-farkas-infeasible must expect unsat")
    data = infeasible.get("data", {})
    variables = require_linear_variables("farkas variables", data.get("variables"))
    constraints = require_linear_constraints("farkas constraints", data.get("constraints"), variables)
    multipliers = data.get("multipliers")
    if not isinstance(multipliers, dict):
        fail("farkas multipliers must be an object")
    constraint_by_id = {
        constraint_id: (coefficients, bound)
        for constraint_id, coefficients, bound in constraints
    }
    if set(multipliers) != set(constraint_by_id):
        missing = sorted(set(constraint_by_id) - set(multipliers))
        extra = sorted(set(multipliers) - set(constraint_by_id))
        fail(f"farkas multipliers must cover constraints exactly; missing={missing} extra={extra}")
    combined_coefficients = {variable: Fraction(0) for variable in variables}
    combined_bound = Fraction(0)
    for constraint_id, raw_multiplier in multipliers.items():
        multiplier = require_fraction(f"farkas multiplier {constraint_id}", raw_multiplier)
        if multiplier < 0:
            fail(f"farkas multiplier {constraint_id} must be nonnegative")
        coefficients, bound = constraint_by_id[constraint_id]
        for variable in variables:
            combined_coefficients[variable] += multiplier * coefficients[variable]
        combined_bound += multiplier * bound
    expected_combination = data.get("expected_combination")
    if not isinstance(expected_combination, dict):
        fail("farkas expected_combination must be an object")
    expected_coefficients = require_linear_coefficients(
        "farkas expected coefficients",
        expected_combination.get("coefficients"),
        variables,
    )
    expected_bound = require_fraction("farkas expected bound", expected_combination.get("bound"))
    if combined_coefficients != expected_coefficients:
        fail("farkas combined coefficients do not match expected combination")
    if combined_bound != expected_bound:
        fail("farkas combined bound does not match expected combination")
    if any(coefficient != 0 for coefficient in combined_coefficients.values()):
        fail("farkas certificate must cancel all variables")
    if combined_bound >= 0:
        fail("farkas certificate must derive 0 <= negative bound")


def require_point2(context: str, value: Any) -> tuple[Fraction, Fraction]:
    vector = require_fraction_vector(context, value)
    if len(vector) != 2:
        fail(f"{context} must be a two-dimensional point")
    return vector[0], vector[1]


def validate_coordinate_geometry(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    midpoint = checks["midpoint-witness"]
    if midpoint["expected_result"] != "sat":
        fail("midpoint-witness must expect sat")
    values = single_witness_values(midpoint, witnesses)
    ax, ay = require_point2("midpoint a", values.get("a"))
    bx, by = require_point2("midpoint b", values.get("b"))
    mx, my = require_point2("midpoint midpoint", values.get("midpoint"))
    if mx != (ax + bx) / 2 or my != (ay + by) / 2:
        fail("midpoint witness does not match segment endpoints")

    collinearity = checks["collinearity-witness"]
    if collinearity["expected_result"] != "sat":
        fail("collinearity-witness must expect sat")
    values = single_witness_values(collinearity, witnesses)
    ax, ay = require_point2("collinearity a", values.get("a"))
    bx, by = require_point2("collinearity b", values.get("b"))
    cx, cy = require_point2("collinearity c", values.get("c"))
    determinant = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    if determinant != 0:
        fail("collinearity witness determinant is not zero")

    distance = checks["distance-squared-witness"]
    if distance["expected_result"] != "sat":
        fail("distance-squared-witness must expect sat")
    values = single_witness_values(distance, witnesses)
    px, py = require_point2("distance p", values.get("p"))
    qx, qy = require_point2("distance q", values.get("q"))
    claimed = require_fraction("distance squared", values.get("distance_squared"))
    if (qx - px) * (qx - px) + (qy - py) * (qy - py) != claimed:
        fail("distance-squared witness does not match point coordinates")


def require_subset(context: str, value: Any, universe: list[str]) -> frozenset[str]:
    subset = set(require_string_list(context, value, nonempty=False))
    universe_set = set(universe)
    missing = sorted(subset - universe_set)
    if missing:
        fail(f"{context} contains elements outside universe: {missing}")
    return frozenset(subset)


def require_set_family(
    context: str,
    value: Any,
    universe: list[str],
) -> set[frozenset[str]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty set family")
    family: set[frozenset[str]] = set()
    for index, subset in enumerate(value):
        normalized = require_subset(f"{context}[{index}]", subset, universe)
        if normalized in family:
            fail(f"{context} repeats subset {sorted(normalized)}")
        family.add(normalized)
    return family


def require_topology_data(context: str, values: dict[str, Any]) -> tuple[list[str], set[frozenset[str]]]:
    universe = require_string_list(f"{context}.universe", values.get("universe"))
    open_sets = require_set_family(f"{context}.open_sets", values.get("open_sets"), universe)
    validate_topology_axioms(context, universe, open_sets)
    return universe, open_sets


def validate_topology_axioms(context: str, universe: list[str], open_sets: set[frozenset[str]]) -> None:
    empty = frozenset()
    full = frozenset(universe)
    if empty not in open_sets:
        fail(f"{context} open sets must include the empty set")
    if full not in open_sets:
        fail(f"{context} open sets must include the universe")
    for left in open_sets:
        for right in open_sets:
            if frozenset(left | right) not in open_sets:
                fail(f"{context} open sets are not closed under pairwise union")
            if frozenset(left & right) not in open_sets:
                fail(f"{context} open sets are not closed under pairwise intersection")


def topology_interior(subset: frozenset[str], open_sets: set[frozenset[str]]) -> frozenset[str]:
    result: set[str] = set()
    for open_set in open_sets:
        if open_set <= subset:
            result.update(open_set)
    return frozenset(result)


def topology_closure(
    subset: frozenset[str],
    universe: list[str],
    open_sets: set[frozenset[str]],
) -> frozenset[str]:
    universe_set = frozenset(universe)
    complement = universe_set - subset
    return frozenset(universe_set - topology_interior(frozenset(complement), open_sets))


def all_subsets(universe: list[str]) -> set[frozenset[str]]:
    subsets: set[frozenset[str]] = set()
    for size in range(len(universe) + 1):
        for candidate in combinations(universe, size):
            subsets.add(frozenset(candidate))
    return subsets


def topology_clopen_subsets(
    universe: list[str],
    open_sets: set[frozenset[str]],
) -> set[frozenset[str]]:
    universe_set = frozenset(universe)
    closed_sets = {frozenset(universe_set - open_set) for open_set in open_sets}
    return {
        subset
        for subset in all_subsets(universe)
        if subset in open_sets and subset in closed_sets
    }


def topology_separations(
    universe: list[str],
    open_sets: set[frozenset[str]],
) -> set[tuple[frozenset[str], frozenset[str]]]:
    universe_set = frozenset(universe)
    separations: set[tuple[frozenset[str], frozenset[str]]] = set()
    for left in open_sets:
        for right in open_sets:
            if not left or not right:
                continue
            if left & right:
                continue
            if frozenset(left | right) != universe_set:
                continue
            separations.add((left, right))
    return separations


def set_family_union(family: set[frozenset[str]]) -> frozenset[str]:
    result: set[str] = set()
    for subset in family:
        result.update(subset)
    return frozenset(result)


def set_family_intersection(family: set[frozenset[str]], universe: list[str]) -> frozenset[str]:
    iterator = iter(family)
    try:
        result = set(next(iterator))
    except StopIteration:
        return frozenset(universe)
    for subset in iterator:
        result.intersection_update(subset)
    return frozenset(result)


def require_metric_distances(
    context: str,
    values: Any,
    points: list[str],
) -> dict[frozenset[str], Fraction]:
    if not isinstance(values, list) or not values:
        fail(f"{context} must be a non-empty distance list")
    point_set = set(points)
    distances: dict[frozenset[str], Fraction] = {}
    for index, item in enumerate(values):
        if not isinstance(item, dict):
            fail(f"{context}[{index}] must be an object")
        pair = item.get("pair")
        if not isinstance(pair, list) or len(pair) != 2:
            fail(f"{context}[{index}].pair must be a two-element list")
        left, right = pair
        require_string(f"{context}[{index}].pair[0]", left)
        require_string(f"{context}[{index}].pair[1]", right)
        if left == right:
            fail(f"{context}[{index}].pair must contain distinct points")
        if left not in point_set or right not in point_set:
            fail(f"{context}[{index}].pair references a missing point")
        key = frozenset((left, right))
        if key in distances:
            fail(f"{context} repeats distance pair {sorted(key)}")
        distance = require_fraction(f"{context}[{index}].distance", item.get("distance"))
        if distance <= 0:
            fail(f"{context}[{index}].distance must be positive for distinct points")
        distances[key] = distance
    for left_index, left in enumerate(points):
        for right in points[left_index + 1 :]:
            key = frozenset((left, right))
            if key not in distances:
                fail(f"{context} missing distance pair {sorted(key)}")
    for x in points:
        for y in points:
            for z in points:
                xy = Fraction(0) if x == y else distances[frozenset((x, y))]
                yz = Fraction(0) if y == z else distances[frozenset((y, z))]
                xz = Fraction(0) if x == z else distances[frozenset((x, z))]
                if xz > xy + yz:
                    fail(f"{context} violates triangle inequality for {x}, {y}, {z}")
    return distances


def finite_metric_distance(
    distances: dict[frozenset[str], Fraction],
    left: str,
    right: str,
) -> Fraction:
    if left == right:
        return Fraction(0)
    return distances[frozenset((left, right))]


def require_point_values(
    context: str,
    value: Any,
    points: list[str],
) -> dict[str, Fraction]:
    if not isinstance(value, dict):
        fail(f"{context} must be an object")
    point_set = set(points)
    if set(value) != point_set:
        missing = sorted(point_set - set(value))
        extra = sorted(set(value) - point_set)
        fail(f"{context} must cover exactly the points; missing={missing} extra={extra}")
    return {
        point: require_fraction(f"{context}.{point}", value[point])
        for point in points
    }


def finite_function_output_distance(
    function_values: dict[str, Fraction],
    left: str,
    right: str,
) -> Fraction:
    return abs(function_values[left] - function_values[right])


def validate_finite_topology(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    axioms = checks["finite-topology-axioms"]
    if axioms["expected_result"] != "sat":
        fail("finite-topology-axioms must expect sat")
    values = single_witness_values(axioms, witnesses)
    require_topology_data("finite topology", values)

    closure_interior = checks["closure-interior-witness"]
    if closure_interior["expected_result"] != "sat":
        fail("closure-interior-witness must expect sat")
    values = single_witness_values(closure_interior, witnesses)
    universe, open_sets = require_topology_data("closure/interior topology", values)
    subset = require_subset("closure/interior subset", values.get("subset"), universe)
    expected_interior = require_subset("closure/interior interior", values.get("interior"), universe)
    expected_closure = require_subset("closure/interior closure", values.get("closure"), universe)
    if topology_interior(subset, open_sets) != expected_interior:
        fail("closure-interior witness interior does not match topology")
    if topology_closure(subset, universe, open_sets) != expected_closure:
        fail("closure-interior witness closure does not match topology")

    metric_ball = checks["metric-ball-witness"]
    if metric_ball["expected_result"] != "sat":
        fail("metric-ball-witness must expect sat")
    values = single_witness_values(metric_ball, witnesses)
    points = require_string_list("metric points", values.get("points"))
    distances = require_metric_distances("metric distances", values.get("distances"), points)
    center = values.get("center")
    require_string("metric center", center)
    if center not in set(points):
        fail("metric center must be one of the points")
    radius = require_fraction("metric radius", values.get("radius"))
    if radius <= 0:
        fail("metric radius must be positive")
    expected_ball = require_subset("metric ball", values.get("ball"), points)
    computed_ball = frozenset(
        point
        for point in points
        if finite_metric_distance(distances, center, point) < radius
    )
    if computed_ball != expected_ball:
        fail("metric-ball witness does not match finite metric")


def validate_finite_compactness(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    cover_check = checks["finite-open-cover-subcover"]
    if cover_check["expected_result"] != "sat":
        fail("finite-open-cover-subcover must expect sat")
    values = single_witness_values(cover_check, witnesses)
    universe, open_sets = require_topology_data("finite compactness topology", values)
    cover = require_set_family("finite compactness cover", values.get("cover"), universe)
    subcover = require_set_family("finite compactness subcover", values.get("subcover"), universe)
    universe_set = frozenset(universe)
    if not cover <= open_sets:
        fail("finite-open-cover-subcover cover must contain only open sets")
    if not subcover <= cover:
        fail("finite-open-cover-subcover subcover must be drawn from the cover")
    if set_family_union(cover) != universe_set:
        fail("finite-open-cover-subcover cover does not cover the universe")
    if set_family_union(subcover) != universe_set:
        fail("finite-open-cover-subcover subcover does not cover the universe")

    minimal = checks["minimal-subcover-size-witness"]
    if minimal["expected_result"] != "sat":
        fail("minimal-subcover-size-witness must expect sat")
    values = single_witness_values(minimal, witnesses)
    universe, open_sets = require_topology_data("minimal subcover topology", values)
    cover = require_set_family("minimal subcover cover", values.get("cover"), universe)
    subcover = require_set_family("minimal subcover subcover", values.get("subcover"), universe)
    min_size = require_nonnegative_int("minimal subcover min_size", values.get("min_size"))
    universe_set = frozenset(universe)
    if not cover <= open_sets:
        fail("minimal-subcover-size-witness cover must contain only open sets")
    if not subcover <= cover:
        fail("minimal-subcover-size-witness subcover must be drawn from the cover")
    if len(subcover) != min_size:
        fail("minimal-subcover-size-witness listed subcover size does not match min_size")
    if set_family_union(subcover) != universe_set:
        fail("minimal-subcover-size-witness listed subcover does not cover the universe")
    cover_list = list(cover)
    for size in range(min_size):
        for candidate in combinations(cover_list, size):
            if set_family_union(set(candidate)) == universe_set:
                fail("minimal-subcover-size-witness found a smaller covering subfamily")

    intersection = checks["finite-intersection-family-witness"]
    if intersection["expected_result"] != "sat":
        fail("finite-intersection-family-witness must expect sat")
    values = single_witness_values(intersection, witnesses)
    universe, open_sets = require_topology_data("finite intersection topology", values)
    closed_family = require_set_family(
        "finite intersection closed_family",
        values.get("closed_family"),
        universe,
    )
    expected_intersection = require_subset("finite intersection intersection", values.get("intersection"), universe)
    universe_set = frozenset(universe)
    for closed_set in closed_family:
        if frozenset(universe_set - closed_set) not in open_sets:
            fail("finite-intersection-family-witness family contains a non-closed set")
    if set_family_intersection(closed_family, universe) != expected_intersection:
        fail("finite-intersection-family-witness intersection is incorrect")
    family_list = list(closed_family)
    for size in range(1, len(family_list) + 1):
        for candidate in combinations(family_list, size):
            if not set_family_intersection(set(candidate), universe):
                fail("finite-intersection-family-witness violates the finite intersection property")

    bad_cover = checks["bad-open-cover-rejected"]
    if bad_cover["expected_result"] != "unsat":
        fail("bad-open-cover-rejected must expect unsat")
    data = bad_cover.get("data", {})
    universe, open_sets = require_topology_data("bad cover topology", data)
    cover = require_set_family("bad cover cover", data.get("cover"), universe)
    missing_points = require_subset("bad cover missing_points", data.get("missing_points"), universe)
    if not cover <= open_sets:
        fail("bad-open-cover-rejected cover must contain only open sets")
    actual_missing = frozenset(set(universe) - set_family_union(cover))
    if actual_missing != missing_points:
        fail("bad-open-cover-rejected missing_points are incorrect")
    if not actual_missing:
        fail("bad-open-cover-rejected cover unexpectedly covers the universe")

    horizon = checks["general-compactness-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-compactness-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-compactness-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general compactness target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general compactness future_checker", data.get("future_checker"))


def validate_finite_connectedness(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    connected = checks["finite-connected-space-witness"]
    if connected["expected_result"] != "sat":
        fail("finite-connected-space-witness must expect sat")
    values = single_witness_values(connected, witnesses)
    universe, open_sets = require_topology_data("finite connected topology", values)
    expected_clopen = require_set_family(
        "finite connected clopen_subsets",
        values.get("clopen_subsets"),
        universe,
    )
    universe_set = frozenset(universe)
    if expected_clopen != {frozenset(), universe_set}:
        fail("finite-connected-space-witness must list only trivial clopen subsets")
    if topology_clopen_subsets(universe, open_sets) != expected_clopen:
        fail("finite-connected-space-witness clopen subsets are incorrect")
    if topology_separations(universe, open_sets):
        fail("finite-connected-space-witness unexpectedly has a separation")

    disconnected = checks["finite-disconnected-separation-witness"]
    if disconnected["expected_result"] != "sat":
        fail("finite-disconnected-separation-witness must expect sat")
    values = single_witness_values(disconnected, witnesses)
    universe, open_sets = require_topology_data("finite disconnected topology", values)
    left = require_subset("finite disconnected separation_left", values.get("separation_left"), universe)
    right = require_subset("finite disconnected separation_right", values.get("separation_right"), universe)
    universe_set = frozenset(universe)
    if not left or not right:
        fail("finite-disconnected-separation-witness separation parts must be non-empty")
    if left not in open_sets or right not in open_sets:
        fail("finite-disconnected-separation-witness separation parts must be open")
    if left & right:
        fail("finite-disconnected-separation-witness separation parts must be disjoint")
    if frozenset(left | right) != universe_set:
        fail("finite-disconnected-separation-witness separation parts must cover the universe")
    if (left, right) not in topology_separations(universe, open_sets):
        fail("finite-disconnected-separation-witness separation was not rediscovered")

    clopen = checks["clopen-subset-disconnection-witness"]
    if clopen["expected_result"] != "sat":
        fail("clopen-subset-disconnection-witness must expect sat")
    values = single_witness_values(clopen, witnesses)
    universe, open_sets = require_topology_data("clopen disconnection topology", values)
    clopen_subset = require_subset("clopen disconnection clopen_subset", values.get("clopen_subset"), universe)
    universe_set = frozenset(universe)
    if not clopen_subset or clopen_subset == universe_set:
        fail("clopen-subset-disconnection-witness clopen subset must be non-trivial")
    if clopen_subset not in topology_clopen_subsets(universe, open_sets):
        fail("clopen-subset-disconnection-witness subset is not clopen")
    complement = frozenset(universe_set - clopen_subset)
    if not complement:
        fail("clopen-subset-disconnection-witness complement must be non-empty")
    if (clopen_subset, complement) not in topology_separations(universe, open_sets):
        fail("clopen-subset-disconnection-witness clopen subset does not produce a separation")

    bad_connected = checks["bad-connected-claim-rejected"]
    if bad_connected["expected_result"] != "unsat":
        fail("bad-connected-claim-rejected must expect unsat")
    data = bad_connected.get("data", {})
    universe, open_sets = require_topology_data("bad connected topology", data)
    counterexample = require_subset("bad connected counterexample_clopen", data.get("counterexample_clopen"), universe)
    universe_set = frozenset(universe)
    if not counterexample or counterexample == universe_set:
        fail("bad-connected-claim-rejected counterexample must be non-trivial")
    if counterexample not in topology_clopen_subsets(universe, open_sets):
        fail("bad-connected-claim-rejected counterexample is not clopen")
    if not topology_separations(universe, open_sets):
        fail("bad-connected-claim-rejected topology unexpectedly has no separation")

    horizon = checks["general-connectedness-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-connectedness-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-connectedness-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general connectedness target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general connectedness future_checker", data.get("future_checker"))


def validate_metric_continuity(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    lipschitz = checks["finite-lipschitz-witness"]
    if lipschitz["expected_result"] != "sat":
        fail("finite-lipschitz-witness must expect sat")
    values = single_witness_values(lipschitz, witnesses)
    points = require_string_list("Lipschitz points", values.get("points"))
    distances = require_metric_distances("Lipschitz distances", values.get("distances"), points)
    function_values = require_point_values("Lipschitz function_values", values.get("function_values"), points)
    constant = require_fraction("Lipschitz constant", values.get("lipschitz_constant"))
    if constant <= 0:
        fail("finite-lipschitz-witness constant must be positive")
    for left_index, left in enumerate(points):
        for right in points[left_index + 1 :]:
            domain_distance = finite_metric_distance(distances, left, right)
            output_distance = finite_function_output_distance(function_values, left, right)
            if output_distance > constant * domain_distance:
                fail("finite-lipschitz-witness violates the claimed bound")

    continuity = checks["epsilon-delta-continuity-witness"]
    if continuity["expected_result"] != "sat":
        fail("epsilon-delta-continuity-witness must expect sat")
    values = single_witness_values(continuity, witnesses)
    points = require_string_list("epsilon-delta points", values.get("points"))
    distances = require_metric_distances("epsilon-delta distances", values.get("distances"), points)
    function_values = require_point_values("epsilon-delta function_values", values.get("function_values"), points)
    center = values.get("center")
    require_string("epsilon-delta center", center)
    if center not in set(points):
        fail("epsilon-delta-continuity-witness center must be one of the points")
    epsilon = require_fraction("epsilon-delta epsilon", values.get("epsilon"))
    delta = require_fraction("epsilon-delta delta", values.get("delta"))
    if epsilon <= 0 or delta <= 0:
        fail("epsilon-delta-continuity-witness epsilon and delta must be positive")
    expected_domain_ball = require_subset("epsilon-delta domain_ball", values.get("domain_ball"), points)
    expected_output_ball = require_subset("epsilon-delta output_ball", values.get("output_ball"), points)
    domain_ball = frozenset(
        point
        for point in points
        if finite_metric_distance(distances, center, point) < delta
    )
    output_ball = frozenset(
        point
        for point in points
        if finite_function_output_distance(function_values, center, point) < epsilon
    )
    if domain_ball != expected_domain_ball:
        fail("epsilon-delta-continuity-witness domain_ball is incorrect")
    if output_ball != expected_output_ball:
        fail("epsilon-delta-continuity-witness output_ball is incorrect")
    if not domain_ball <= output_ball:
        fail("epsilon-delta-continuity-witness domain ball is not contained in output ball")

    preimage = checks["open-ball-preimage-witness"]
    if preimage["expected_result"] != "sat":
        fail("open-ball-preimage-witness must expect sat")
    values = single_witness_values(preimage, witnesses)
    points = require_string_list("preimage points", values.get("points"))
    distances = require_metric_distances("preimage distances", values.get("distances"), points)
    function_values = require_point_values("preimage function_values", values.get("function_values"), points)
    target_value = require_fraction("preimage target_value", values.get("target_value"))
    epsilon = require_fraction("preimage epsilon", values.get("epsilon"))
    center = values.get("domain_ball_center")
    require_string("preimage domain_ball_center", center)
    if center not in set(points):
        fail("open-ball-preimage-witness domain_ball_center must be one of the points")
    radius = require_fraction("preimage domain_ball_radius", values.get("domain_ball_radius"))
    if epsilon <= 0 or radius <= 0:
        fail("open-ball-preimage-witness epsilon and radius must be positive")
    expected_preimage = require_subset("preimage set", values.get("preimage"), points)
    expected_domain_ball = require_subset("preimage domain_ball", values.get("domain_ball"), points)
    actual_preimage = frozenset(
        point
        for point in points
        if abs(function_values[point] - target_value) < epsilon
    )
    actual_domain_ball = frozenset(
        point
        for point in points
        if finite_metric_distance(distances, center, point) < radius
    )
    if actual_preimage != expected_preimage:
        fail("open-ball-preimage-witness preimage is incorrect")
    if actual_domain_ball != expected_domain_ball:
        fail("open-ball-preimage-witness domain_ball is incorrect")
    if expected_preimage != expected_domain_ball:
        fail("open-ball-preimage-witness preimage should match the listed domain ball")

    bad_delta = checks["bad-delta-rejected"]
    if bad_delta["expected_result"] != "unsat":
        fail("bad-delta-rejected must expect unsat")
    data = bad_delta.get("data", {})
    points = require_string_list("bad delta points", data.get("points"))
    distances = require_metric_distances("bad delta distances", data.get("distances"), points)
    function_values = require_point_values("bad delta function_values", data.get("function_values"), points)
    center = data.get("center")
    counterexample = data.get("counterexample")
    require_string("bad delta center", center)
    require_string("bad delta counterexample", counterexample)
    if center not in set(points) or counterexample not in set(points):
        fail("bad-delta-rejected center and counterexample must be listed points")
    epsilon = require_fraction("bad delta epsilon", data.get("epsilon"))
    claimed_delta = require_fraction("bad delta claimed_delta", data.get("claimed_delta"))
    domain_distance = require_fraction("bad delta domain_distance", data.get("domain_distance"))
    output_distance = require_fraction("bad delta output_distance", data.get("output_distance"))
    if epsilon <= 0 or claimed_delta <= 0:
        fail("bad-delta-rejected epsilon and claimed_delta must be positive")
    if finite_metric_distance(distances, center, counterexample) != domain_distance:
        fail("bad-delta-rejected domain_distance is incorrect")
    if finite_function_output_distance(function_values, center, counterexample) != output_distance:
        fail("bad-delta-rejected output_distance is incorrect")
    if not domain_distance < claimed_delta:
        fail("bad-delta-rejected counterexample is not inside the claimed delta ball")
    if output_distance < epsilon:
        fail("bad-delta-rejected counterexample unexpectedly satisfies epsilon")

    horizon = checks["general-continuity-lean-horizon"]
    if horizon["expected_result"] != "not-run":
        fail("general-continuity-lean-horizon must be not-run")
    if horizon["proof_status"] != "lean-horizon":
        fail("general-continuity-lean-horizon must remain lean-horizon")
    data = horizon.get("data", {})
    require_string("general continuity target_theorem_shape", data.get("target_theorem_shape"))
    require_string("general continuity future_checker", data.get("future_checker"))


def require_sigma_algebra_data(
    context: str,
    values: dict[str, Any],
) -> tuple[list[str], set[frozenset[str]]]:
    universe = require_string_list(f"{context}.universe", values.get("universe"))
    measurable_sets = require_set_family(
        f"{context}.measurable_sets",
        values.get("measurable_sets"),
        universe,
    )
    validate_sigma_algebra_axioms(context, universe, measurable_sets)
    return universe, measurable_sets


def validate_sigma_algebra_axioms(
    context: str,
    universe: list[str],
    measurable_sets: set[frozenset[str]],
) -> None:
    empty = frozenset()
    full = frozenset(universe)
    if empty not in measurable_sets:
        fail(f"{context} measurable sets must include the empty set")
    if full not in measurable_sets:
        fail(f"{context} measurable sets must include the universe")
    for subset in measurable_sets:
        if frozenset(full - subset) not in measurable_sets:
            fail(f"{context} measurable sets are not closed under complement")
    for left in measurable_sets:
        for right in measurable_sets:
            if frozenset(left | right) not in measurable_sets:
                fail(f"{context} measurable sets are not closed under pairwise union")


def require_measure_table(
    context: str,
    value: Any,
    universe: list[str],
    measurable_sets: set[frozenset[str]],
) -> dict[frozenset[str], Fraction]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty measure table")
    measures: dict[frozenset[str], Fraction] = {}
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            fail(f"{context}[{index}] must be an object")
        subset = require_subset(f"{context}[{index}].set", item.get("set"), universe)
        if subset not in measurable_sets:
            fail(f"{context}[{index}].set is not measurable")
        if subset in measures:
            fail(f"{context} repeats measure for set {sorted(subset)}")
        measure = require_fraction(f"{context}[{index}].measure", item.get("measure"))
        if measure < 0:
            fail(f"{context}[{index}].measure must be nonnegative")
        measures[subset] = measure
    if set(measures) != measurable_sets:
        missing = sorted(sorted(subset) for subset in measurable_sets - set(measures))
        extra = sorted(sorted(subset) for subset in set(measures) - measurable_sets)
        fail(f"{context} must cover measurable sets exactly; missing={missing} extra={extra}")
    return measures


def validate_finite_measure_table(
    context: str,
    universe: list[str],
    measurable_sets: set[frozenset[str]],
    measures: dict[frozenset[str], Fraction],
) -> None:
    empty = frozenset()
    full = frozenset(universe)
    if measures[empty] != 0:
        fail(f"{context} must have measure(empty) = 0")
    if measures[full] != 1:
        fail(f"{context} currently expects normalized total measure 1")
    for left in measurable_sets:
        for right in measurable_sets:
            if left & right:
                continue
            union = frozenset(left | right)
            if union in measurable_sets and measures[union] != measures[left] + measures[right]:
                fail(f"{context} violates finite additivity")


def validate_finite_measure(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    sigma = checks["finite-sigma-algebra-axioms"]
    if sigma["expected_result"] != "sat":
        fail("finite-sigma-algebra-axioms must expect sat")
    values = single_witness_values(sigma, witnesses)
    require_sigma_algebra_data("finite sigma algebra", values)

    additivity = checks["finite-measure-additivity"]
    if additivity["expected_result"] != "sat":
        fail("finite-measure-additivity must expect sat")
    values = single_witness_values(additivity, witnesses)
    universe, measurable_sets = require_sigma_algebra_data("finite measure sigma algebra", values)
    measures = require_measure_table("finite measure table", values.get("measures"), universe, measurable_sets)
    validate_finite_measure_table("finite-measure-additivity", universe, measurable_sets, measures)

    complement = checks["event-complement-measure"]
    if complement["expected_result"] != "sat":
        fail("event-complement-measure must expect sat")
    values = single_witness_values(complement, witnesses)
    universe, measurable_sets = require_sigma_algebra_data("event complement sigma algebra", values)
    measures = require_measure_table("event complement measure table", values.get("measures"), universe, measurable_sets)
    validate_finite_measure_table("event-complement-measure", universe, measurable_sets, measures)
    universe_set = frozenset(universe)
    event = require_subset("event complement event", values.get("event"), universe)
    expected_event_measure = require_fraction("event complement event_measure", values.get("event_measure"))
    expected_complement = require_subset("event complement complement", values.get("complement"), universe)
    expected_complement_measure = require_fraction(
        "event complement complement_measure",
        values.get("complement_measure"),
    )
    expected_total_measure = require_fraction("event complement total_measure", values.get("total_measure"))
    actual_complement = frozenset(universe_set - event)
    if actual_complement != expected_complement:
        fail("event-complement witness complement does not match event")
    if measures[event] != expected_event_measure:
        fail("event-complement witness event measure does not match table")
    if measures[actual_complement] != expected_complement_measure:
        fail("event-complement witness complement measure does not match table")
    if measures[event] + measures[actual_complement] != expected_total_measure:
        fail("event-complement witness measures do not sum to total")
    if measures[universe_set] != expected_total_measure:
        fail("event-complement witness total measure does not match universe")


def require_probability(context: str, value: Any) -> Fraction:
    probability = require_fraction(context, value)
    if probability < 0 or probability > 1:
        fail(f"{context} must be in [0, 1]")
    return probability


def require_probability_atoms(
    context: str,
    value: Any,
    *,
    require_events: bool,
) -> list[tuple[str, Fraction, set[str]]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty atom list")
    atoms: list[tuple[str, Fraction, set[str]]] = []
    seen_ids: set[str] = set()
    for index, atom in enumerate(value):
        if not isinstance(atom, dict):
            fail(f"{context}[{index}] must be an object")
        atom_id = atom.get("id")
        require_string(f"{context}[{index}].id", atom_id)
        if atom_id in seen_ids:
            fail(f"{context} repeats atom id {atom_id!r}")
        seen_ids.add(atom_id)
        probability = require_probability(f"{context}[{index}].probability", atom.get("probability"))
        raw_events = atom.get("events", [])
        if require_events and not raw_events:
            fail(f"{context}[{index}].events must be non-empty")
        events = set(require_string_list(f"{context}[{index}].events", raw_events, nonempty=require_events))
        atoms.append((atom_id, probability, events))
    return atoms


def require_normalized_atoms(context: str, atoms: list[tuple[str, Fraction, set[str]]]) -> None:
    total = sum((probability for _, probability, _ in atoms), Fraction(0))
    if total != 1:
        fail(f"{context} atom probabilities must sum to exactly 1")


def event_probability(atoms: list[tuple[str, Fraction, set[str]]], event: str) -> Fraction:
    return sum((probability for _, probability, events in atoms if event in events), Fraction(0))


def joint_event_probability(
    atoms: list[tuple[str, Fraction, set[str]]],
    left_event: str,
    right_event: str,
) -> Fraction:
    return sum(
        (
            probability
            for _, probability, events in atoms
            if left_event in events and right_event in events
        ),
        Fraction(0),
    )


def validate_finite_probability(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    total_mass = checks["pmf-total-mass"]
    if total_mass["expected_result"] != "sat":
        fail("pmf-total-mass must expect sat")
    values = single_witness_values(total_mass, witnesses)
    atoms = require_probability_atoms("pmf atoms", values.get("atoms"), require_events=False)
    require_normalized_atoms("pmf-total-mass", atoms)

    conditional = checks["conditional-probability-witness"]
    if conditional["expected_result"] != "sat":
        fail("conditional-probability-witness must expect sat")
    values = single_witness_values(conditional, witnesses)
    atoms = require_probability_atoms("conditional atoms", values.get("atoms"), require_events=True)
    require_normalized_atoms("conditional-probability-witness", atoms)
    event = values.get("event")
    condition = values.get("condition")
    require_string("conditional event", event)
    require_string("conditional condition", condition)
    claimed = require_probability("conditional probability", values.get("conditional_probability"))
    condition_probability = event_probability(atoms, condition)
    if condition_probability == 0:
        fail("conditional probability condition must have nonzero probability")
    joint_probability = joint_event_probability(atoms, event, condition)
    if joint_probability / condition_probability != claimed:
        fail("conditional probability witness does not match the atom table")

    bayes = checks["bayes-posterior-witness"]
    if bayes["expected_result"] != "sat":
        fail("bayes-posterior-witness must expect sat")
    values = single_witness_values(bayes, witnesses)
    prior = require_probability("bayes prior", values.get("prior"))
    sensitivity = require_probability("bayes sensitivity", values.get("sensitivity"))
    false_positive_rate = require_probability(
        "bayes false_positive_rate",
        values.get("false_positive_rate"),
    )
    posterior = require_probability("bayes posterior", values.get("posterior"))
    numerator = prior * sensitivity
    denominator = numerator + (1 - prior) * false_positive_rate
    if denominator == 0:
        fail("bayes denominator must be nonzero")
    if numerator / denominator != posterior:
        fail("bayes posterior witness does not match Bayes rule")


def require_matrix_distribution(
    context: str,
    value: Any,
) -> list[tuple[str, Fraction, list[list[Fraction]]]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty matrix distribution")
    atoms: list[tuple[str, Fraction, list[list[Fraction]]]] = []
    seen_ids: set[str] = set()
    shape: tuple[int, int] | None = None
    for index, atom in enumerate(value):
        if not isinstance(atom, dict):
            fail(f"{context}[{index}] must be an object")
        atom_id = atom.get("id")
        require_string(f"{context}[{index}].id", atom_id)
        if atom_id in seen_ids:
            fail(f"{context} repeats atom id {atom_id!r}")
        seen_ids.add(atom_id)
        probability = require_probability(f"{context}[{index}].probability", atom.get("probability"))
        matrix = require_fraction_matrix(f"{context}[{index}].matrix", atom.get("matrix"))
        atom_shape = (len(matrix), len(matrix[0]))
        if shape is None:
            shape = atom_shape
        elif atom_shape != shape:
            fail(f"{context} matrices must all have shape {shape}")
        atoms.append((atom_id, probability, matrix))
    total = sum((probability for _, probability, _ in atoms), Fraction(0))
    if total != 1:
        fail(f"{context} probabilities must sum to exactly 1")
    return atoms


def matrix_trace(matrix: list[list[Fraction]]) -> Fraction:
    require_square_matrix("matrix trace", matrix)
    return sum((matrix[index][index] for index in range(len(matrix))), Fraction(0))


def matrix_det_2x2(matrix: list[list[Fraction]]) -> Fraction:
    require_square_matrix("matrix determinant", matrix)
    if len(matrix) != 2:
        fail("matrix determinant currently expects 2x2 matrices")
    return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]


def matrix_transpose(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    return [list(column) for column in zip(*matrix)]


def matrix_rank(matrix: list[list[Fraction]]) -> int:
    rows = [list(row) for row in matrix]
    if not rows:
        return 0
    height = len(rows)
    width = len(rows[0])
    rank = 0
    for col_index in range(width):
        pivot = None
        for row_index in range(rank, height):
            if rows[row_index][col_index] != 0:
                pivot = row_index
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_value = rows[rank][col_index]
        rows[rank] = [entry / pivot_value for entry in rows[rank]]
        for row_index in range(height):
            if row_index == rank:
                continue
            factor = rows[row_index][col_index]
            if factor == 0:
                continue
            rows[row_index] = [
                entry - factor * pivot_entry
                for entry, pivot_entry in zip(rows[row_index], rows[rank])
            ]
        rank += 1
        if rank == height:
            break
    return rank


def expected_scalar(
    atoms: list[tuple[str, Fraction, list[list[Fraction]]]],
    evaluator: Callable[[list[list[Fraction]]], Fraction],
) -> Fraction:
    return sum((probability * evaluator(matrix) for _, probability, matrix in atoms), Fraction(0))


def expected_matrix(
    atoms: list[tuple[str, Fraction, list[list[Fraction]]]],
    evaluator: Callable[[list[list[Fraction]]], list[list[Fraction]]],
) -> list[list[Fraction]]:
    evaluated = [evaluator(matrix) for _, _, matrix in atoms]
    height = len(evaluated[0])
    width = len(evaluated[0][0])
    total = [[Fraction(0) for _ in range(width)] for _ in range(height)]
    for (_, probability, _), matrix in zip(atoms, evaluated):
        if len(matrix) != height or len(matrix[0]) != width:
            fail("expected matrix terms must all have the same shape")
        for row_index, row in enumerate(matrix):
            for col_index, entry in enumerate(row):
                total[row_index][col_index] += probability * entry
    return total


def rank_probabilities(
    atoms: list[tuple[str, Fraction, list[list[Fraction]]]],
) -> dict[int, Fraction]:
    probabilities: dict[int, Fraction] = {}
    for _, probability, matrix in atoms:
        rank = matrix_rank(matrix)
        probabilities[rank] = probabilities.get(rank, Fraction(0)) + probability
    return probabilities


def require_rank_probability_map(context: str, value: Any) -> dict[int, Fraction]:
    if not isinstance(value, dict) or not value:
        fail(f"{context} must be a non-empty rank probability object")
    probabilities: dict[int, Fraction] = {}
    for rank_key, raw_probability in value.items():
        require_string(f"{context} key", rank_key)
        try:
            rank = int(rank_key)
        except ValueError as error:
            fail(f"{context} key {rank_key!r} is not an integer rank: {error}")
        if rank < 0:
            fail(f"{context} rank keys must be nonnegative")
        probabilities[rank] = require_probability(f"{context}.{rank_key}", raw_probability)
    return probabilities


def validate_random_matrix_finite(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    moments = checks["sign-diagonal-moments"]
    if moments["expected_result"] != "sat":
        fail("sign-diagonal-moments must expect sat")
    values = single_witness_values(moments, witnesses)
    atoms = require_matrix_distribution("sign diagonal atoms", values.get("atoms"))
    expected_trace = require_fraction("sign diagonal expected_trace", values.get("expected_trace"))
    expected_trace_square = require_fraction(
        "sign diagonal expected_trace_square",
        values.get("expected_trace_square"),
    )
    expected_determinant = require_fraction(
        "sign diagonal expected_determinant",
        values.get("expected_determinant"),
    )
    invertible_probability = require_probability(
        "sign diagonal invertible_probability",
        values.get("invertible_probability"),
    )
    if expected_scalar(atoms, matrix_trace) != expected_trace:
        fail("sign-diagonal-moments expected_trace is incorrect")
    if expected_scalar(atoms, lambda matrix: matrix_trace(matrix) ** 2) != expected_trace_square:
        fail("sign-diagonal-moments expected_trace_square is incorrect")
    if expected_scalar(atoms, matrix_det_2x2) != expected_determinant:
        fail("sign-diagonal-moments expected_determinant is incorrect")
    actual_invertible_probability = sum(
        (
            probability
            for _, probability, matrix in atoms
            if len(matrix) == len(matrix[0]) and matrix_rank(matrix) == len(matrix)
        ),
        Fraction(0),
    )
    if actual_invertible_probability != invertible_probability:
        fail("sign-diagonal-moments invertible_probability is incorrect")

    gram = checks["expected-gram-matrix"]
    if gram["expected_result"] != "sat":
        fail("expected-gram-matrix must expect sat")
    values = single_witness_values(gram, witnesses)
    atoms = require_matrix_distribution("expected Gram atoms", values.get("atoms"))
    expected_gram = require_fraction_matrix("expected Gram matrix", values.get("expected_gram"))
    computed_gram = expected_matrix(
        atoms,
        lambda matrix: mat_mul(matrix_transpose(matrix), matrix),
    )
    if computed_gram != expected_gram:
        fail("expected-gram-matrix expected_gram is incorrect")

    ranks = checks["rank-mixture-probabilities"]
    if ranks["expected_result"] != "sat":
        fail("rank-mixture-probabilities must expect sat")
    values = single_witness_values(ranks, witnesses)
    atoms = require_matrix_distribution("rank mixture atoms", values.get("atoms"))
    expected_rank = require_fraction("rank mixture expected_rank", values.get("expected_rank"))
    expected_rank_probabilities = require_rank_probability_map(
        "rank mixture probabilities",
        values.get("rank_probabilities"),
    )
    actual_rank_probabilities = rank_probabilities(atoms)
    if actual_rank_probabilities != expected_rank_probabilities:
        fail("rank-mixture-probabilities rank distribution is incorrect")
    actual_expected_rank = sum(
        (Fraction(rank) * probability for rank, probability in actual_rank_probabilities.items()),
        Fraction(0),
    )
    if actual_expected_rank != expected_rank:
        fail("rank-mixture-probabilities expected_rank is incorrect")

    bad_moment = checks["bad-trace-moment-rejected"]
    if bad_moment["expected_result"] != "unsat":
        fail("bad-trace-moment-rejected must expect unsat")
    data = bad_moment.get("data", {})
    atoms = require_matrix_distribution("bad trace atoms", data.get("atoms"))
    claimed = require_fraction("bad trace claimed_expected_trace_square", data.get("claimed_expected_trace_square"))
    actual = require_fraction("bad trace actual_expected_trace_square", data.get("actual_expected_trace_square"))
    computed = expected_scalar(atoms, lambda matrix: matrix_trace(matrix) ** 2)
    if computed != actual:
        fail("bad-trace-moment-rejected actual moment is incorrect")
    if claimed == actual:
        fail("bad-trace-moment-rejected claimed moment unexpectedly matches")


def require_probability_vector(context: str, value: Any) -> list[Fraction]:
    vector = require_fraction_vector(context, value)
    for index, probability in enumerate(vector):
        if probability < 0 or probability > 1:
            fail(f"{context}[{index}] must be in [0, 1]")
    return vector


def require_normalized_probability_vector(context: str, value: Any) -> list[Fraction]:
    vector = require_probability_vector(context, value)
    total = sum(vector, Fraction(0))
    if total != 1:
        fail(f"{context} probabilities must sum to exactly 1")
    return vector


def require_stochastic_matrix(context: str, value: Any) -> list[list[Fraction]]:
    matrix = require_fraction_matrix(context, value)
    require_square_matrix(context, matrix)
    for row_index, row in enumerate(matrix):
        for col_index, probability in enumerate(row):
            if probability < 0 or probability > 1:
                fail(f"{context}[{row_index}][{col_index}] must be in [0, 1]")
        if sum(row, Fraction(0)) != 1:
            fail(f"{context}[{row_index}] probabilities must sum to exactly 1")
    return matrix


def row_vec_mat(vector: list[Fraction], matrix: list[list[Fraction]]) -> list[Fraction]:
    if len(vector) != len(matrix):
        fail("row-vector/matrix multiplication dimension mismatch")
    width = len(matrix[0])
    return [
        sum((vector[row_index] * matrix[row_index][col_index] for row_index in range(len(vector))), Fraction(0))
        for col_index in range(width)
    ]


def stochastic_row_sums(matrix: list[list[Fraction]]) -> list[Fraction]:
    return [sum(row, Fraction(0)) for row in matrix]


def validate_finite_markov_chain(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    stochastic = checks["stochastic-matrix-witness"]
    if stochastic["expected_result"] != "sat":
        fail("stochastic-matrix-witness must expect sat")
    values = single_witness_values(stochastic, witnesses)
    matrix = require_stochastic_matrix("stochastic transition matrix", values.get("transition_matrix"))
    row_sums = require_fraction_vector("stochastic row_sums", values.get("row_sums"))
    if stochastic_row_sums(matrix) != row_sums:
        fail("stochastic-matrix-witness row_sums do not match transition matrix")

    evolution = checks["finite-horizon-distribution-replay"]
    if evolution["expected_result"] != "sat":
        fail("finite-horizon-distribution-replay must expect sat")
    values = single_witness_values(evolution, witnesses)
    matrix = require_stochastic_matrix("finite horizon transition matrix", values.get("transition_matrix"))
    initial = require_normalized_probability_vector("finite horizon initial", values.get("initial"))
    one_step = require_normalized_probability_vector("finite horizon one_step", values.get("one_step"))
    two_step = require_normalized_probability_vector("finite horizon two_step", values.get("two_step"))
    absorbing_index = require_nonnegative_int("finite horizon absorbing_state_index", values.get("absorbing_state_index"))
    absorption_probability = require_probability(
        "finite horizon absorption_probability_after_two",
        values.get("absorption_probability_after_two"),
    )
    if absorbing_index >= len(two_step):
        fail("finite horizon absorbing_state_index is outside the state vector")
    if row_vec_mat(initial, matrix) != one_step:
        fail("finite-horizon-distribution-replay one_step is incorrect")
    if row_vec_mat(one_step, matrix) != two_step:
        fail("finite-horizon-distribution-replay two_step is incorrect")
    if two_step[absorbing_index] != absorption_probability:
        fail("finite-horizon-distribution-replay absorption probability is incorrect")

    stationary = checks["stationary-distribution-witness"]
    if stationary["expected_result"] != "sat":
        fail("stationary-distribution-witness must expect sat")
    values = single_witness_values(stationary, witnesses)
    matrix = require_stochastic_matrix("stationary transition matrix", values.get("transition_matrix"))
    distribution = require_normalized_probability_vector("stationary distribution", values.get("stationary_distribution"))
    if row_vec_mat(distribution, matrix) != distribution:
        fail("stationary-distribution-witness distribution is not stationary")

    bad_row = checks["bad-stochastic-row-rejected"]
    if bad_row["expected_result"] != "unsat":
        fail("bad-stochastic-row-rejected must expect unsat")
    data = bad_row.get("data", {})
    matrix = require_fraction_matrix("bad stochastic transition matrix", data.get("transition_matrix"))
    require_square_matrix("bad stochastic transition matrix", matrix)
    row_sums = require_fraction_vector("bad stochastic row_sums", data.get("row_sums"))
    bad_row_index = require_nonnegative_int("bad stochastic bad_row_index", data.get("bad_row_index"))
    if bad_row_index >= len(matrix):
        fail("bad-stochastic-row-rejected bad_row_index is outside the matrix")
    if stochastic_row_sums(matrix) != row_sums:
        fail("bad-stochastic-row-rejected row_sums do not match matrix")
    if row_sums[bad_row_index] == 1:
        fail("bad-stochastic-row-rejected bad row unexpectedly sums to 1")


def require_nonnegative_int(context: str, value: Any) -> int:
    integer = require_int(context, value)
    if integer < 0:
        fail(f"{context} must be nonnegative")
    return integer


def require_positive_int(context: str, value: Any) -> int:
    integer = require_int(context, value)
    if integer <= 0:
        fail(f"{context} must be positive")
    return integer


def require_nonnegative_int_list(context: str, value: Any) -> list[int]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty integer list")
    return [require_nonnegative_int(f"{context}[{index}]", item) for index, item in enumerate(value)]


def require_count_matrix(context: str, value: Any) -> list[list[int]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty matrix")
    matrix: list[list[int]] = []
    for row_index, row in enumerate(value):
        matrix.append(require_nonnegative_int_list(f"{context}[{row_index}]", row))
    width = len(matrix[0])
    for row_index, row in enumerate(matrix):
        if len(row) != width:
            fail(f"{context}[{row_index}] must have width {width}")
    return matrix


def column_sums(matrix: list[list[int]]) -> list[int]:
    return [sum(row[column] for row in matrix) for column in range(len(matrix[0]))]


def require_success_total(context: str, item: dict[str, Any], prefix: str) -> tuple[int, int]:
    successes = require_nonnegative_int(f"{context}.{prefix}_success", item.get(f"{prefix}_success"))
    total = require_positive_int(f"{context}.{prefix}_total", item.get(f"{prefix}_total"))
    if successes > total:
        fail(f"{context}.{prefix}_success must not exceed {prefix}_total")
    return successes, total


def validate_descriptive_statistics(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    moments = checks["mean-variance-identity"]
    if moments["expected_result"] != "sat":
        fail("mean-variance-identity must expect sat")
    values = single_witness_values(moments, witnesses)
    sample = require_fraction_vector("statistics sample", values.get("sample"))
    mean = require_fraction("statistics mean", values.get("mean"))
    second_moment = require_fraction("statistics second_moment", values.get("second_moment"))
    variance = require_fraction("statistics population_variance", values.get("population_variance"))
    count = Fraction(len(sample))
    computed_mean = sum(sample, Fraction(0)) / count
    computed_second_moment = sum((value * value for value in sample), Fraction(0)) / count
    computed_variance = computed_second_moment - computed_mean * computed_mean
    if computed_mean != mean:
        fail("mean-variance witness mean does not match sample")
    if computed_second_moment != second_moment:
        fail("mean-variance witness second moment does not match sample")
    if computed_variance != variance:
        fail("mean-variance witness variance does not match sample")

    contingency = checks["contingency-table-margins"]
    if contingency["expected_result"] != "sat":
        fail("contingency-table-margins must expect sat")
    values = single_witness_values(contingency, witnesses)
    table = require_count_matrix("contingency table", values.get("table"))
    row_sums = require_nonnegative_int_list("contingency row_sums", values.get("row_sums"))
    expected_column_sums = require_nonnegative_int_list(
        "contingency column_sums",
        values.get("column_sums"),
    )
    total = require_nonnegative_int("contingency total", values.get("total"))
    if [sum(row) for row in table] != row_sums:
        fail("contingency row sums do not match table")
    if column_sums(table) != expected_column_sums:
        fail("contingency column sums do not match table")
    if sum(row_sums) != total:
        fail("contingency total does not match row sums")

    simpson = checks["simpson-paradox-witness"]
    if simpson["expected_result"] != "sat":
        fail("simpson-paradox-witness must expect sat")
    values = single_witness_values(simpson, witnesses)
    if values.get("within_strata_winner") != "A":
        fail("simpson witness within_strata_winner must be A")
    if values.get("aggregate_winner") != "B":
        fail("simpson witness aggregate_winner must be B")
    strata = values.get("strata")
    if not isinstance(strata, list) or len(strata) < 2:
        fail("simpson strata must contain at least two strata")
    a_success_total = 0
    a_total_total = 0
    b_success_total = 0
    b_total_total = 0
    for index, stratum in enumerate(strata):
        if not isinstance(stratum, dict):
            fail(f"simpson strata[{index}] must be an object")
        require_string(f"simpson strata[{index}].id", stratum.get("id"))
        a_success, a_total = require_success_total(f"simpson strata[{index}]", stratum, "a")
        b_success, b_total = require_success_total(f"simpson strata[{index}]", stratum, "b")
        if Fraction(a_success, a_total) <= Fraction(b_success, b_total):
            fail("simpson witness must have A beating B in every stratum")
        a_success_total += a_success
        a_total_total += a_total
        b_success_total += b_success
        b_total_total += b_total
    if Fraction(b_success_total, b_total_total) <= Fraction(a_success_total, a_total_total):
        fail("simpson witness must have B beating A in aggregate")


def require_tail_kind(context: str, value: Any) -> str:
    require_string(context, value)
    if value not in {"equal", "less_equal", "greater_equal"}:
        fail(f"{context} must be one of equal, less_equal, greater_equal")
    return value


def binomial_point_probability(trials: int, successes: int, probability: Fraction) -> Fraction:
    if successes < 0 or successes > trials:
        return Fraction(0)
    return (
        Fraction(combination_count(trials, successes))
        * (probability ** successes)
        * ((1 - probability) ** (trials - successes))
    )


def binomial_tail_probability(
    trials: int,
    successes: int,
    probability: Fraction,
    tail: str,
) -> Fraction:
    if tail == "equal":
        return binomial_point_probability(trials, successes, probability)
    if tail == "less_equal":
        return sum(
            (binomial_point_probability(trials, value, probability) for value in range(successes + 1)),
            Fraction(0),
        )
    return sum(
        (binomial_point_probability(trials, value, probability) for value in range(successes, trials + 1)),
        Fraction(0),
    )


def require_2x2_count_table(context: str, value: Any) -> list[list[int]]:
    table = require_count_matrix(context, value)
    if len(table) != 2 or len(table[0]) != 2:
        fail(f"{context} must be a 2x2 count table")
    return table


def hypergeometric_probability(row1: int, row2: int, col1: int, top_left: int) -> Fraction:
    total = row1 + row2
    if top_left < max(0, col1 - row2) or top_left > min(row1, col1):
        return Fraction(0)
    numerator = combination_count(row1, top_left) * combination_count(row2, col1 - top_left)
    denominator = combination_count(total, col1)
    return Fraction(numerator, denominator)


def fisher_left_tail_probability(row1: int, row2: int, col1: int, observed_top_left: int) -> Fraction:
    lower = max(0, col1 - row2)
    return sum(
        (hypergeometric_probability(row1, row2, col1, value) for value in range(lower, observed_top_left + 1)),
        Fraction(0),
    )


def validate_exact_statistical_tests(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    binomial = checks["binomial-tail-pvalue"]
    if binomial["expected_result"] != "sat":
        fail("binomial-tail-pvalue must expect sat")
    values = single_witness_values(binomial, witnesses)
    trials = require_positive_int("binomial trials", values.get("trials"))
    successes = require_nonnegative_int("binomial observed_successes", values.get("observed_successes"))
    probability = require_probability("binomial null_probability", values.get("null_probability"))
    tail = require_tail_kind("binomial tail", values.get("tail"))
    p_value = require_probability("binomial p_value", values.get("p_value"))
    if successes > trials:
        fail("binomial observed_successes must not exceed trials")
    if binomial_tail_probability(trials, successes, probability, tail) != p_value:
        fail("binomial-tail-pvalue p_value is incorrect")

    point = checks["hypergeometric-point-probability"]
    if point["expected_result"] != "sat":
        fail("hypergeometric-point-probability must expect sat")
    values = single_witness_values(point, witnesses)
    table = require_2x2_count_table("hypergeometric table", values.get("table"))
    observed_top_left = require_nonnegative_int("hypergeometric observed_top_left", values.get("observed_top_left"))
    probability = require_probability("hypergeometric point_probability", values.get("point_probability"))
    row1 = table[0][0] + table[0][1]
    row2 = table[1][0] + table[1][1]
    col1 = table[0][0] + table[1][0]
    if hypergeometric_probability(row1, row2, col1, observed_top_left) != probability:
        fail("hypergeometric-point-probability probability is incorrect")

    fisher = checks["fisher-left-tail-pvalue"]
    if fisher["expected_result"] != "sat":
        fail("fisher-left-tail-pvalue must expect sat")
    values = single_witness_values(fisher, witnesses)
    table = require_2x2_count_table("fisher table", values.get("table"))
    observed_top_left = require_nonnegative_int("fisher observed_top_left", values.get("observed_top_left"))
    p_value = require_probability("fisher left_tail_p_value", values.get("left_tail_p_value"))
    row_sums = require_nonnegative_int_list("fisher row_sums", values.get("row_sums"))
    column_sums_value = require_nonnegative_int_list("fisher column_sums", values.get("column_sums"))
    if row_sums != [sum(row) for row in table]:
        fail("fisher-left-tail-pvalue row_sums do not match table")
    if column_sums_value != column_sums(table):
        fail("fisher-left-tail-pvalue column_sums do not match table")
    row1 = row_sums[0]
    row2 = row_sums[1]
    col1 = column_sums_value[0]
    if fisher_left_tail_probability(row1, row2, col1, observed_top_left) != p_value:
        fail("fisher-left-tail-pvalue p_value is incorrect")

    bad = checks["bad-binomial-pvalue-rejected"]
    if bad["expected_result"] != "unsat":
        fail("bad-binomial-pvalue-rejected must expect unsat")
    data = bad.get("data", {})
    trials = require_positive_int("bad binomial trials", data.get("trials"))
    successes = require_nonnegative_int("bad binomial observed_successes", data.get("observed_successes"))
    probability = require_probability("bad binomial null_probability", data.get("null_probability"))
    tail = require_tail_kind("bad binomial tail", data.get("tail"))
    claimed = require_probability("bad binomial claimed_p_value", data.get("claimed_p_value"))
    actual = require_probability("bad binomial actual_p_value", data.get("actual_p_value"))
    if successes > trials:
        fail("bad binomial observed_successes must not exceed trials")
    if binomial_tail_probability(trials, successes, probability, tail) != actual:
        fail("bad-binomial-pvalue-rejected actual_p_value is incorrect")
    if claimed == actual:
        fail("bad-binomial-pvalue-rejected claimed p-value unexpectedly matches")


def require_recurrence_trace(context: str, values: dict[str, Any]) -> list[Fraction]:
    initial = require_fraction(f"{context}.initial", values.get("initial"))
    delta = require_fraction(f"{context}.delta", values.get("delta"))
    steps = require_nonnegative_int(f"{context}.steps", values.get("steps"))
    trace = require_fraction_vector(f"{context}.trace", values.get("trace"))
    if len(trace) != steps + 1:
        fail(f"{context}.trace must contain steps + 1 states")
    if trace[0] != initial:
        fail(f"{context}.trace must start at the initial state")
    for index in range(steps):
        if trace[index + 1] != trace[index] + delta:
            fail(f"{context}.trace transition {index}->{index + 1} does not match delta")
    return trace


def validate_bounded_dynamics(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    recurrence = checks["linear-recurrence-trace"]
    if recurrence["expected_result"] != "sat":
        fail("linear-recurrence-trace must expect sat")
    values = single_witness_values(recurrence, witnesses)
    require_recurrence_trace("linear recurrence", values)

    invariant = checks["bounded-invariant-witness"]
    if invariant["expected_result"] != "sat":
        fail("bounded-invariant-witness must expect sat")
    values = single_witness_values(invariant, witnesses)
    trace = require_recurrence_trace("bounded invariant", values)
    lower_bound = require_fraction("bounded invariant lower_bound", values.get("lower_bound"))
    upper_bound = require_fraction("bounded invariant upper_bound", values.get("upper_bound"))
    if lower_bound > upper_bound:
        fail("bounded invariant lower_bound must be <= upper_bound")
    for index, state in enumerate(trace):
        if state < lower_bound or state > upper_bound:
            fail(f"bounded invariant trace state {index} is outside the claimed bounds")

    reachable = checks["unsafe-threshold-reachable"]
    if reachable["expected_result"] != "sat":
        fail("unsafe-threshold-reachable must expect sat")
    values = single_witness_values(reachable, witnesses)
    trace = require_recurrence_trace("threshold reachability", values)
    threshold = require_fraction("threshold reachability threshold", values.get("threshold"))
    first_step = require_nonnegative_int(
        "threshold reachability first_reaching_step",
        values.get("first_reaching_step"),
    )
    if first_step >= len(trace):
        fail("threshold reachability first_reaching_step is outside the trace")
    if trace[first_step] < threshold:
        fail("threshold reachability first_reaching_step does not reach the threshold")
    for index, state in enumerate(trace[:first_step]):
        if state >= threshold:
            fail(f"threshold reachability state {index} reaches before first_reaching_step")


def validate_pack_semantics(metadata: dict[str, Any], expected: dict[str, Any]) -> None:
    if metadata["id"] == "bounded-dynamics-v0":
        validate_bounded_dynamics(expected)
    if metadata["id"] == "calculus-algebraic-shadow-v0":
        validate_calculus_algebraic_shadow(expected)
    if metadata["id"] == "complex-algebraic-v0":
        validate_complex_algebraic(expected)
    if metadata["id"] == "counting-v0":
        validate_counting(expected)
    if metadata["id"] == "coordinate-geometry-v0":
        validate_coordinate_geometry(expected)
    if metadata["id"] == "descriptive-statistics-v0":
        validate_descriptive_statistics(expected)
    if metadata["id"] == "exact-statistical-tests-v0":
        validate_exact_statistical_tests(expected)
    if metadata["id"] == "finite-cardinality-v0":
        validate_finite_cardinality(expected)
    if metadata["id"] == "finite-compactness-v0":
        validate_finite_compactness(expected)
    if metadata["id"] == "finite-connectedness-v0":
        validate_finite_connectedness(expected)
    if metadata["id"] == "finite-topology-v0":
        validate_finite_topology(expected)
    if metadata["id"] == "finite-sets-v0":
        validate_finite_sets(expected)
    if metadata["id"] == "finite-fields-v0":
        validate_finite_fields(expected)
    if metadata["id"] == "finite-groups-v0":
        validate_finite_groups(expected)
    if metadata["id"] == "finite-measure-v0":
        validate_finite_measure(expected)
    if metadata["id"] == "metric-continuity-v0":
        validate_metric_continuity(expected)
    if metadata["id"] == "finite-predicate-v0":
        validate_finite_predicate(expected)
    if metadata["id"] == "graph-coloring-v0":
        validate_graph_coloring(expected)
    if metadata["id"] == "graph-cut-v0":
        validate_graph_cut(expected)
    if metadata["id"] == "graph-d-separation-v0":
        validate_graph_d_separation(expected)
    if metadata["id"] == "graph-matching-v0":
        validate_graph_matching(expected)
    if metadata["id"] == "graph-reachability-v0":
        validate_graph_reachability(expected)
    if metadata["id"] == "induction-obligations-v0":
        validate_induction_obligations(expected)
    if metadata["id"] == "integer-lia-v0":
        validate_integer_lia(expected)
    if metadata["id"] == "finite-probability-v0":
        validate_finite_probability(expected)
    if metadata["id"] == "finite-markov-chain-v0":
        validate_finite_markov_chain(expected)
    if metadata["id"] == "finite-operator-v0":
        validate_finite_operator(expected)
    if metadata["id"] == "finite-rings-v0":
        validate_finite_rings(expected)
    if metadata["id"] == "gcd-bezout-v0":
        validate_gcd_bezout(expected)
    if metadata["id"] == "linear-optimization-v0":
        validate_linear_optimization(expected)
    if metadata["id"] == "logic-basics-v0":
        validate_logic_basics(expected)
    if metadata["id"] == "matrix-invariants-v0":
        validate_matrix_invariants(expected)
    if metadata["id"] == "proof-methods-refutation-v0":
        validate_proof_methods_refutation(expected)
    if metadata["id"] == "random-matrix-finite-v0":
        validate_random_matrix_finite(expected)
    if metadata["id"] == "modular-arithmetic-v0":
        validate_modular_arithmetic(expected)
    if metadata["id"] == "natural-arithmetic-v0":
        validate_natural_arithmetic(expected)
    if metadata["id"] == "numerical-linear-algebra-v0":
        validate_numerical_linear_algebra(expected)
    if metadata["id"] == "number-theory-v0":
        validate_number_theory(expected)
    if metadata["id"] == "polynomial-identities-v0":
        validate_polynomial_identities(expected)
    if metadata["id"] == "rationals-lra-v0":
        validate_rationals_lra(expected)
    if metadata["id"] == "reals-rcf-shadow-v0":
        validate_reals_rcf_shadow(expected)
    if metadata["id"] == "relations-functions-v0":
        validate_relations_functions(expected)
    if metadata["id"] == "sequence-limit-shadow-v0":
        validate_sequence_limit_shadow(expected)
    if metadata["id"] == "spectral-linear-algebra-v0":
        validate_spectral_linear_algebra(expected)
    if metadata["id"] == "linear-algebra-rational-v0":
        validate_linear_algebra_rational(expected)


def validate_pack(pack_dir: Path, concept_ids: set[str], field_ids: set[str], curriculum_nodes: set[str]) -> None:
    if not pack_dir.is_dir():
        fail(f"{pack_dir} is not a directory")
    missing = sorted(name for name in REQUIRED_FILES if not (pack_dir / name).exists())
    if missing:
        fail(f"{pack_dir.relative_to(ROOT)} missing files: {', '.join(missing)}")
    load_json(SCHEMA)
    metadata = load_json(pack_dir / "metadata.json")
    expected = load_json(pack_dir / "expected.json")
    expected_ids = validate_metadata(pack_dir, metadata, concept_ids, field_ids, curriculum_nodes)
    validate_expected(metadata, expected, expected_ids)


def pack_dirs_from_args(args: list[str]) -> list[Path]:
    if args:
        return [(ROOT / arg).resolve() if not Path(arg).is_absolute() else Path(arg) for arg in args]
    if not DEFAULT_ROOT.exists():
        fail(f"default pack root is missing: {DEFAULT_ROOT.relative_to(ROOT)}")
    return sorted(path for path in DEFAULT_ROOT.iterdir() if path.is_dir())


def main(argv: list[str]) -> int:
    concept_ids, field_ids, curriculum_nodes = concept_indexes()
    pack_dirs = pack_dirs_from_args(argv)
    if not pack_dirs:
        fail("no example packs found")
    for pack_dir in pack_dirs:
        validate_pack(pack_dir, concept_ids, field_ids, curriculum_nodes)
    print(f"validated {len(pack_dirs)} foundational example pack(s)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ValidationError as error:
        print(f"validate-foundational-example-pack: {error}", file=sys.stderr)
        raise SystemExit(1)
