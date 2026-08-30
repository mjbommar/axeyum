#!/usr/bin/env python3
"""Shared fixture builder for `check-declaration-graph.py`'s eight mutation
classes (L1 phase C1/G1).

Both `test-declaration-graph.py` (in-process assertions) and
`test-declaration-graph-mutations.sh` (the guard-deletion kill table) use
this module to build the SAME nine graph variants -- the untouched good
graph plus one mutation per class -- so the fixtures proving "each mutation
is rejected" and the fixtures proving "deleting guard X flips only mutation
X" are identical.

The good graph is small and SYNTHETIC (not derived from a real lean4export
run): five ordinary declarations (Base -> Leaf -> Root, a Definition and a
Theorem depending on Base/Leaf) plus one genuine 2-node mutual-inductive
cycle (Ty <-> Ty.ctor, mirroring the atomic type<->constructor edge
`scripts/lib/declaration_graph.py` adds for real inductive data) -- small
enough that the mutation harness runs in well under a second, while still
exercising every guard, INCLUDING one that must pass a fixture containing a
real, correctly-classified cycle.

Each mutation is built to be surgical: every OTHER self-referential field
(pack_digest, per-record digests, edges.json, source_population counts) is
kept internally consistent with the mutation, so the ONLY thing left
inconsistent is the one invariant the mutation's target guard checks.
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import declaration_graph as dg  # noqa: E402

LAC = dg.LAC

POPULATION_ID = "g1-mutation-fixture"

MUTATION_NAMES = [
    "missing", "duplicate", "reordered", "truncated", "value_exposed",
    "row_deleted", "edge_deleted", "unexpected_cycle",
]
MUTATION_TO_GUARD = {
    "missing": "MISSING",
    "duplicate": "DUPLICATE",
    "reordered": "REORDERED",
    "truncated": "TRUNCATED",
    "value_exposed": "VALUE_EXPOSED",
    "row_deleted": "ENDPOINT_RESOLUTION",
    "edge_deleted": "EDGES_CONSISTENT",
    "unexpected_cycle": "CYCLE_CLASSIFICATION",
}


def _row(name, kind, universes, type_text, value_text, direct_type_deps, direct_value_deps, mutual_group):
    type_digest = LAC.compute_type_digest({"type": type_text})
    value_digest = LAC.compute_value_digest({"value": value_text})
    row = {
        "name": name,
        "kind": kind,
        "universes": universes,
        "type": type_text,
        "value": value_text,
        "type_digest": type_digest,
        "value_digest": value_digest,
        "direct_type_deps": sorted(direct_type_deps),
        "direct_value_deps": sorted(direct_value_deps),
        "mutual_group": sorted(set(mutual_group) | {name}),
    }
    row["identity_digest"] = LAC.compute_identity_digest(row, type_digest, value_digest)
    return row


def build_good_rows() -> list[dict]:
    rows = [
        _row("Base", "Axiom", [], "Sort 0", None, [], [], ["Base"]),
        _row("Leaf", "Definition", [], "Base", "Base", ["Base"], [], ["Leaf"]),
        _row("Root", "Theorem", [], "Base", "Leaf", ["Base"], ["Leaf"], ["Root"]),
        # A genuine mutual-inductive 2-cycle: Ty's atomic type->own-constructor
        # edge (see declaration_graph.py's resolve_rows) plus the
        # constructor's natural ctor->type edge. Present in the GOOD fixture
        # deliberately, so CYCLE_CLASSIFICATION's positive case proves the
        # guard tolerates an EXPLAINED cycle rather than rejecting all cycles.
        _row("Ty", "Inductive", [], "Sort 0", None, ["Ty.ctor"], [], ["Ty", "Ty.ctor"]),
        _row("Ty.ctor", "Constructor", [], "Ty", None, ["Ty"], [], ["Ty", "Ty.ctor"]),
    ]
    return sorted(rows, key=lambda r: r["name"])


def build_edges(rows: list[dict]) -> list[dict]:
    edges = []
    for row in rows:
        for dep in row["direct_type_deps"]:
            edges.append({"from": row["name"], "to": dep, "kind": "type"})
        for dep in row["direct_value_deps"]:
            edges.append({"from": row["name"], "to": dep, "kind": "value"})
    edges.sort(key=lambda e: (e["from"], e["to"], e["kind"]))
    return edges


def compute_transitive(rows: list[dict]) -> None:
    by_name = {r["name"]: r for r in rows}
    type_edges = {n: d["direct_type_deps"] for n, d in by_name.items()}
    value_edges = {n: list(d["direct_type_deps"]) + list(d["direct_value_deps"]) for n, d in by_name.items()}
    for row in rows:
        row["transitive_type_deps"] = LAC.compute_closure(set(row["direct_type_deps"]), type_edges)
        row["transitive_value_deps"] = LAC.compute_closure(
            set(row["direct_type_deps"]) | set(row["direct_value_deps"]), value_edges
        )


def build_pack(rows: list[dict]) -> dict:
    rows = sorted(rows, key=lambda r: r["name"])
    compute_transitive(rows)
    return {
        "contract_version": "0.1.0",
        "text_provenance": "hand-authored",
        "lean_version": "4.30.0",
        "lean_commit": "d024af09",
        "mathlib_version": "test",
        "mathlib_commit": "test",
        "normalization_version": 1,
        "renderer_version": 1,
        "source_population": {
            "population_id": POPULATION_ID,
            "requested_roots": ["Root"],
            "expected_declaration_count": len(rows),
        },
        "trusted_declaration_identities": sorted(r["name"] for r in rows if r["kind"] in dg.TRUSTED_KINDS),
        "pack_digest": LAC.compute_pack_digest(rows),
        "declarations": rows,
    }


def build_typeproj(pack: dict) -> dict:
    return {
        "population_id": POPULATION_ID,
        "declarations": [LAC.project_type_only(r) for r in pack["declarations"]],
    }


def build_cycles(pack: dict) -> dict:
    return {
        "population_id": POPULATION_ID,
        "type_graph": dg.classify_cycles(pack["declarations"], mode="type"),
        "full_graph": dg.classify_cycles(pack["declarations"], mode="full"),
    }


def load_good():
    rows = build_good_rows()
    pack = build_pack(rows)
    edges = {"population_id": POPULATION_ID, "edges": build_edges(pack["declarations"])}
    typeproj = build_typeproj(pack)
    cycles = build_cycles(pack)
    return pack, typeproj, edges, cycles


def build_missing(pack: dict, edges: dict) -> tuple[dict, dict]:
    """Delete the `Root` declaration -- the only name in the EXTERNAL
    population registry's `expected_roots` -- and tidy every field the pack
    itself controls: drop it from `source_population`, recompute
    `pack_digest`, and remove Root's own edges from edges.json (Root is
    never anyone else's dependency, so this cannot trip ENDPOINT_RESOLUTION;
    only the external registry, untouched, still expects it)."""
    pack = copy.deepcopy(pack)
    edges = copy.deepcopy(edges)
    pack["declarations"] = [d for d in pack["declarations"] if d["name"] != "Root"]
    pack["source_population"]["requested_roots"] = []
    pack["source_population"]["expected_declaration_count"] = len(pack["declarations"])
    pack["pack_digest"] = LAC.compute_pack_digest(pack["declarations"])
    edges["edges"] = [e for e in edges["edges"] if e["from"] != "Root"]
    return pack, edges


def build_duplicate(pack: dict) -> dict:
    """Append an exact duplicate of `Leaf`. Content-identical, so per-record
    digests, edge SETS (deduped), and cycle classification are all
    unaffected -- only name-uniqueness is violated."""
    pack = copy.deepcopy(pack)
    dup = copy.deepcopy(next(d for d in pack["declarations"] if d["name"] == "Leaf"))
    pack["declarations"].append(dup)
    pack["pack_digest"] = LAC.compute_pack_digest(pack["declarations"])
    return pack


def build_reordered(pack: dict) -> dict:
    """Swap two declarations' file order WITHOUT recomputing `pack_digest` --
    per-record content, edges, and cycle classification are all
    order-independent, so only the order-sensitive hash chain disagrees."""
    pack = copy.deepcopy(pack)
    decls = pack["declarations"]
    i, j = 0, 1
    decls[i], decls[j] = decls[j], decls[i]
    return pack  # pack_digest deliberately STALE (computed for the old order)


def build_truncated(pack: dict) -> dict:
    """Corrupt `Leaf`'s `type` text WITHOUT recomputing its digests -- the
    stored `type_digest`/`identity_digest` (and hence `pack_digest`, which
    only ever hashes `identity_digest` values) still match the OLD, correct
    content, so only the direct type/value-digest recomputation disagrees."""
    pack = copy.deepcopy(pack)
    for d in pack["declarations"]:
        if d["name"] == "Leaf":
            d["type"] = "CORRUPTED"
    return pack


def build_value_exposed(typeproj: dict) -> dict:
    """Leak a value-bearing key onto one projection record."""
    typeproj = copy.deepcopy(typeproj)
    typeproj["declarations"][0]["value"] = "LEAKED"
    return typeproj


def build_row_deleted(pack: dict, edges: dict) -> tuple[dict, dict]:
    """Delete `Leaf`'s row while Root's `direct_value_deps` (untouched)
    still names it. `Leaf` has no dependencies beyond `Base` (already in
    Root's own transitive set independently), so Root's recorded
    `transitive_value_deps` does not change and TRUNCATED stays green --
    only ENDPOINT_RESOLUTION can see the dangling reference. `pack_digest`
    is recomputed over the remaining rows so REORDERED stays green, and
    Leaf's OWN outgoing edge (Leaf -> Base) is dropped from edges.json too
    (a row that no longer exists cannot be the SOURCE of a materialized
    edge), so EDGES_CONSISTENT stays green and only ENDPOINT_RESOLUTION
    fires."""
    pack = copy.deepcopy(pack)
    edges = copy.deepcopy(edges)
    pack["declarations"] = [d for d in pack["declarations"] if d["name"] != "Leaf"]
    pack["source_population"]["expected_declaration_count"] = len(pack["declarations"])
    pack["pack_digest"] = LAC.compute_pack_digest(pack["declarations"])
    edges["edges"] = [e for e in edges["edges"] if e["from"] != "Leaf"]
    return pack, edges


def build_edge_deleted(edges: dict) -> dict:
    """Delete the (Root, Leaf, value) edge from edges.json while rows.json
    is untouched -- Root's own `direct_value_deps` still lists `Leaf`, so
    every row-level guard (including ENDPOINT_RESOLUTION) is unaffected;
    only the materialized edge list disagrees with what the rows recompute."""
    edges = copy.deepcopy(edges)
    edges["edges"] = [e for e in edges["edges"] if not (e["from"] == "Root" and e["to"] == "Leaf")]
    return edges


def build_unexpected_cycle(pack: dict, edges: dict) -> tuple[dict, dict]:
    """Add a fresh 2-cycle (X <-> Y, both plain Definitions) whose
    `mutual_group` does NOT cover the pair -- an unexplained cycle a real
    extraction bug could produce. Every other field is kept correct (proper
    digests, `pack_digest` recomputed, edges added) so only cycle
    classification disagrees; the committed `cycles.json` this mutation is
    checked against is deliberately the STALE good-fixture one, which knows
    nothing about X/Y."""
    pack = copy.deepcopy(pack)
    edges = copy.deepcopy(edges)
    x = _row("X", "Definition", [], "Base", "Y", ["Base"], ["Y"], ["X"])
    y = _row("Y", "Definition", [], "Base", "X", ["Base"], ["X"], ["Y"])
    pack["declarations"] = sorted(pack["declarations"] + [x, y], key=lambda r: r["name"])
    compute_transitive(pack["declarations"])
    pack["source_population"]["expected_declaration_count"] = len(pack["declarations"])
    pack["pack_digest"] = LAC.compute_pack_digest(pack["declarations"])
    edges["edges"] = build_edges(pack["declarations"])
    return pack, edges


def write_fixture(target_dir: Path, fixture_name: str, pack: dict, typeproj: dict, edges: dict, cycles: dict) -> None:
    (target_dir / f"{fixture_name}.rows.json").write_text(json.dumps(pack, indent=2) + "\n", encoding="utf-8")
    (target_dir / f"{fixture_name}.typeproj.json").write_text(json.dumps(typeproj, indent=2) + "\n", encoding="utf-8")
    (target_dir / f"{fixture_name}.edges.json").write_text(json.dumps(edges, indent=2) + "\n", encoding="utf-8")
    (target_dir / f"{fixture_name}.cycles.json").write_text(json.dumps(cycles, indent=2) + "\n", encoding="utf-8")


def write_all_fixtures(target_dir: Path) -> None:
    target_dir.mkdir(parents=True, exist_ok=True)
    pop_dir = target_dir / "populations"
    pop_dir.mkdir(parents=True, exist_ok=True)
    (pop_dir / f"{POPULATION_ID}.json").write_text(
        json.dumps({"population_id": POPULATION_ID, "expected_roots": ["Root"]}, indent=2) + "\n",
        encoding="utf-8",
    )

    good_pack, good_typeproj, good_edges, good_cycles = load_good()
    write_fixture(target_dir, "good", good_pack, good_typeproj, good_edges, good_cycles)

    missing_pack, missing_edges = build_missing(good_pack, good_edges)
    write_fixture(target_dir, "missing", missing_pack, good_typeproj, missing_edges, good_cycles)

    dup_pack = build_duplicate(good_pack)
    write_fixture(target_dir, "duplicate", dup_pack, good_typeproj, good_edges, good_cycles)

    reordered_pack = build_reordered(good_pack)
    write_fixture(target_dir, "reordered", reordered_pack, good_typeproj, good_edges, good_cycles)

    truncated_pack = build_truncated(good_pack)
    write_fixture(target_dir, "truncated", truncated_pack, good_typeproj, good_edges, good_cycles)

    value_exposed_typeproj = build_value_exposed(good_typeproj)
    write_fixture(target_dir, "value_exposed", good_pack, value_exposed_typeproj, good_edges, good_cycles)

    row_deleted_pack, row_deleted_edges = build_row_deleted(good_pack, good_edges)
    write_fixture(target_dir, "row_deleted", row_deleted_pack, good_typeproj, row_deleted_edges, good_cycles)

    edge_deleted_edges = build_edge_deleted(good_edges)
    write_fixture(target_dir, "edge_deleted", good_pack, good_typeproj, edge_deleted_edges, good_cycles)

    cyc_pack, cyc_edges = build_unexpected_cycle(good_pack, good_edges)
    write_fixture(target_dir, "unexpected_cycle", cyc_pack, good_typeproj, cyc_edges, good_cycles)


def main(argv: list[str]) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", type=Path, required=True)
    args = parser.parse_args(argv)
    write_all_fixtures(args.write_fixtures)
    print(f"wrote fixtures to {args.write_fixtures}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
