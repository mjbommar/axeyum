#!/usr/bin/env python3
"""Gate: validate `artifacts/declaration-graph/graph/*.rows.json` and its
companion files (L1 phase C1 / G1,
docs/plan/graph-directed-library-roadmap-2026-08-30.md).

This checker needs NO Lean toolchain -- it validates the committed JSON, the
same way `scripts/check-library-artifact-contract.py` (ADR-0800) validates a
committed pack. Regenerating from Mathlib is `scripts/gen-declaration-graph.py`'s
job, run by hand/CI-offline, not by this gate.

Eight guards, each independently mutation-verified to be killed by exactly
one fixture (`scripts/tests/test-declaration-graph-mutations.sh`):

  MISSING              every population's expected_roots present     (reused, ADR-0800)
  DUPLICATE            declaration names pairwise distinct            (reused, ADR-0800)
  REORDERED            pack_digest matches file order                 (reused, ADR-0800)
  TRUNCATED            per-record digests + transitive closures       (reused, ADR-0800)
  VALUE_EXPOSED        typeproj file carries no value-bearing key      (reused, ADR-0800)
  ENDPOINT_RESOLUTION  every direct_type/value_dep resolves to a row   (new -- ROW deletion)
  EDGES_CONSISTENT     edges.json == edges recomputed from rows        (new -- EDGE deletion)
  CYCLE_CLASSIFICATION every multi-node SCC explained by mutual_group  (new)

The first five are the LITERAL functions from `scripts/check-library-
artifact-contract.py` (ADR-0800's reader A), imported via
`scripts/lib/declaration_graph.py`'s `LAC` -- not reimplemented -- because a
declaration-graph row IS shaped as a valid ADR-0800 pack record (with two
extra fields, `mutual_group` and `origin_module`, which those functions
never read).

Usage:
    python3 scripts/check-declaration-graph.py
    python3 scripts/check-declaration-graph.py --graph-dir DIR --population-dir DIR
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import declaration_graph as dg  # noqa: E402

LAC = dg.LAC

DEFAULT_GRAPH_DIR = REPO_ROOT / "artifacts" / "declaration-graph" / "graph"
DEFAULT_POPULATION_DIR = REPO_ROOT / "artifacts" / "declaration-graph" / "populations"


def load_json(path: Path) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def rows_path_for(population_id: str, graph_dir: Path) -> Path:
    return graph_dir / f"{population_id}.rows.json"


def typeproj_path_for(rows_path: Path) -> Path:
    name = rows_path.name
    assert name.endswith(".rows.json"), name
    return rows_path.with_name(name[: -len(".rows.json")] + ".typeproj.json")


def edges_path_for(rows_path: Path) -> Path:
    name = rows_path.name
    return rows_path.with_name(name[: -len(".rows.json")] + ".edges.json")


def cycles_path_for(rows_path: Path) -> Path:
    name = rows_path.name
    return rows_path.with_name(name[: -len(".rows.json")] + ".cycles.json")


# ---------------------------------------------------------------------------
# GUARD:ENDPOINT_RESOLUTION -- new, catches ROW deletion
# ---------------------------------------------------------------------------


# GUARD:ENDPOINT_RESOLUTION begin
def check_endpoint_resolution(pack: dict) -> list[str]:
    """Every name appearing in ANY row's `direct_type_deps`/`direct_value_deps`
    must itself be present as a row's `name` in this same graph. Unlike
    ADR-0800's C0 contract (whose 9-declaration demonstration pack may
    legitimately stop at a Lean-core boundary), a declaration-graph
    population is extracted via `lean4export`, which always emits a
    dependency's FULL transitive closure alongside it -- so a name that
    resolves to nothing is either a bug in extraction or a deleted row, not
    an expected external boundary. This is what actually catches deleting a
    non-root declaration: `check_missing_roots` only watches the
    population's own named roots, and `check_record_digests` (TRUNCATED)
    only re-derives transitive closures from `direct_*_deps` fields that are
    themselves untouched by a row deletion -- neither one is guaranteed to
    fire when a referenced LEAF row disappears."""
    names = {d["name"] for d in pack["declarations"]}
    missing_endpoints: dict[str, list[str]] = {}
    for d in pack["declarations"]:
        for dep in list(d["direct_type_deps"]) + list(d["direct_value_deps"]):
            if dep not in names:
                missing_endpoints.setdefault(dep, []).append(d["name"])
    if missing_endpoints:
        return [
            f"dependency {dep!r} referenced by {sorted(referrers)} has no row in this graph"
            for dep, referrers in sorted(missing_endpoints.items())
        ]
    return []
# GUARD:ENDPOINT_RESOLUTION end


# ---------------------------------------------------------------------------
# GUARD:EDGES_CONSISTENT -- new, catches EDGE deletion
# ---------------------------------------------------------------------------


# GUARD:EDGES_CONSISTENT begin
def check_edges_consistent(pack: dict, edges_path: Path) -> list[str]:
    """`<population>.edges.json` is a MATERIALIZED view of every row's
    `direct_type_deps`/`direct_value_deps`. Recompute the edge set from the
    rows and require an EXACT match (as sets of (from, to, kind) triples)
    against the committed file. This is deliberately a DIFFERENT check from
    ENDPOINT_RESOLUTION: deleting one edge from `edges.json` while leaving
    `rows.json` untouched changes nothing about which names resolve (every
    row's own `direct_*_deps` still lists the dependency; the edge is simply
    missing from the separate materialized file), so ENDPOINT_RESOLUTION
    cannot see it -- only recomputing and diffing the edge LIST does."""
    if not edges_path.exists():
        return [f"no edges file at {edges_path}"]
    edges_doc = load_json(edges_path)
    recorded = {(e["from"], e["to"], e["kind"]) for e in edges_doc.get("edges", [])}
    recomputed: set[tuple[str, str, str]] = set()
    for d in pack["declarations"]:
        for dep in d["direct_type_deps"]:
            recomputed.add((d["name"], dep, "type"))
        for dep in d["direct_value_deps"]:
            recomputed.add((d["name"], dep, "value"))
    missing_from_file = recomputed - recorded
    extra_in_file = recorded - recomputed
    errors = []
    if missing_from_file:
        errors.append(
            f"{edges_path}: {len(missing_from_file)} edge(s) present in rows.json "
            f"but absent from edges.json, e.g. {sorted(missing_from_file)[:5]}"
        )
    if extra_in_file:
        errors.append(
            f"{edges_path}: {len(extra_in_file)} edge(s) present in edges.json "
            f"but absent from rows.json, e.g. {sorted(extra_in_file)[:5]}"
        )
    return errors
# GUARD:EDGES_CONSISTENT end


# ---------------------------------------------------------------------------
# GUARD:CYCLE_CLASSIFICATION -- new
# ---------------------------------------------------------------------------


# GUARD:CYCLE_CLASSIFICATION begin
def check_cycle_classification(pack: dict, cycles_path: Path) -> list[str]:
    """Recompute type-graph and full-graph SCCs from the rows (via
    `declaration_graph.classify_cycles`, the SAME function the generator
    uses) and require: (a) the committed `<population>.cycles.json` agrees
    with a fresh recomputation, and (b) NEITHER graph has an
    UNEXPECTED_CYCLE. `classify_cycles` itself already requires every
    multi-node SCC's node set to be a subset of some member row's
    `mutual_group`, so an unexplained cycle already sorts into
    `unexpected_cycles`; this guard is what makes that finding a GATE
    FAILURE instead of a number sitting unread in a JSON file."""
    if not cycles_path.exists():
        return [f"no cycles file at {cycles_path}"]
    recorded = load_json(cycles_path)
    fresh_type = dg.classify_cycles(pack["declarations"], mode="type")
    fresh_full = dg.classify_cycles(pack["declarations"], mode="full")
    errors = []
    if recorded.get("type_graph") != fresh_type:
        errors.append(f"{cycles_path}: type_graph classification does not match a fresh recomputation")
    if recorded.get("full_graph") != fresh_full:
        errors.append(f"{cycles_path}: full_graph classification does not match a fresh recomputation")
    for label, report in (("type_graph", fresh_type), ("full_graph", fresh_full)):
        if report["unexpected_cycles"]:
            errors.append(
                f"{label}: {len(report['unexpected_cycles'])} UNEXPECTED cycle(s) not explained "
                f"by any row's mutual_group: {report['unexpected_cycles']}"
            )
    return errors
# GUARD:CYCLE_CLASSIFICATION end


def validate_graph(rows_path: Path, population_dir: Path) -> list[str]:
    errors: list[str] = []
    try:
        pack = load_json(rows_path)
    except (json.JSONDecodeError, OSError) as e:
        return [f"{rows_path}: cannot load: {e}"]

    if not isinstance(pack.get("declarations"), list) or not pack["declarations"]:
        return [f"{rows_path}: `declarations` must be a non-empty array"]

    # Reused verbatim from ADR-0800's reader A.
    errors += [f"{rows_path}: {e}" for e in LAC.check_missing_roots(pack, population_dir)]
    errors += [f"{rows_path}: {e}" for e in LAC.check_no_duplicate_names(pack)]
    errors += [f"{rows_path}: {e}" for e in LAC.check_pack_digest(pack)]
    errors += [f"{rows_path}: {e}" for e in LAC.check_record_digests(pack)]

    typeproj_path = typeproj_path_for(rows_path)
    errors += [f"{e}" for e in LAC.check_typeproj_no_value_leak(typeproj_path)]

    # New to G1.
    errors += [f"{rows_path}: {e}" for e in check_endpoint_resolution(pack)]
    errors += [f"{e}" for e in check_edges_consistent(pack, edges_path_for(rows_path))]
    errors += [f"{e}" for e in check_cycle_classification(pack, cycles_path_for(rows_path))]

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rows", type=Path, default=None, help="validate a single *.rows.json file")
    parser.add_argument("--graph-dir", type=Path, default=DEFAULT_GRAPH_DIR)
    parser.add_argument("--population-dir", type=Path, default=DEFAULT_POPULATION_DIR)
    args = parser.parse_args()

    if args.rows is not None:
        rows_paths = [args.rows]
    else:
        rows_paths = sorted(args.graph_dir.glob("*.rows.json"))

    if not rows_paths:
        print("check-declaration-graph: no graphs found -- nothing checked", file=sys.stderr)
        return 1

    all_errors: list[str] = []
    for p in rows_paths:
        errs = validate_graph(p, args.population_dir)
        if errs:
            all_errors.extend(errs)
        else:
            print(f"check-declaration-graph: OK {p}")

    if all_errors:
        print("check-declaration-graph: FAILED", file=sys.stderr)
        for e in all_errors:
            print(f"  {e}", file=sys.stderr)
        return 1

    print(f"check-declaration-graph: {len(rows_paths)} graph(s) valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
