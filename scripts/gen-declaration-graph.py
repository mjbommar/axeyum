#!/usr/bin/env python3
"""Generate the L1 phase C1/G1 declaration-graph artifacts.

Shells out to the pinned lean4export toolchain
(`scripts/provision-lean-import-toolchain.sh`) once per root name in the
named population, parses each export with `scripts/lib/declaration_graph.py`,
merges the results by declaration name (verifying content agreement where
roots' closures overlap -- lean4export's output is deterministic, so a
disagreement here means the toolchain drifted between runs), computes
transitive closures by REUSING `compute_closure` from
`scripts/check-library-artifact-contract.py` (ADR-0800), classifies cycles,
and writes four files under `artifacts/declaration-graph/graph/`:

    <population_id>.rows.json      archival pack (type AND value/proof data)
    <population_id>.typeproj.json  producer-facing type-only projection
    <population_id>.edges.json     materialized edge list
    <population_id>.cycles.json    cycle classification report

Vendors nothing: reads whatever the pinned toolchain checkout has on disk
(default `/data0/axeyum/lean-import-toolchain`) and writes only the four
compact JSON files above -- no raw ndjson, no Mathlib source, is committed.

Usage:
    python3 scripts/gen-declaration-graph.py --population mathlib-group-defs-v1
    python3 scripts/gen-declaration-graph.py --population P --toolchain-root DIR
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lib"))
import declaration_graph as dg  # noqa: E402

DEFAULT_TOOLCHAIN_ROOT = Path("/data0/axeyum/lean-import-toolchain")
DEFAULT_POPULATION_DIR = REPO_ROOT / "artifacts" / "declaration-graph" / "populations"
DEFAULT_GRAPH_DIR = REPO_ROOT / "artifacts" / "declaration-graph" / "graph"
CONTRACT_VERSION = "0.1.0"


def load_json(path: Path) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def export_root(toolchain_root: Path, module: str, root_name: str, timeout: int) -> str:
    """Run lean4export for one root and return the raw ndjson text.
    `module == "Init"` uses lean4export's own checkout (core Lean only, no
    Mathlib environment needed); anything else runs through mathlib4's
    `lake env` so the requested module's compiled environment is on the
    Lean search path."""
    lean_bin_dir = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.30.0" / "bin"
    lean4export_bin = toolchain_root / "lean4export" / ".lake" / "build" / "bin" / "lean4export"
    env = {"PATH": f"{lean_bin_dir}:/usr/bin:/bin"}
    if module == "Init":
        cwd = toolchain_root / "lean4export"
        cmd = [str(lean4export_bin), module, "--", root_name]
    else:
        cwd = toolchain_root / "mathlib4"
        lake_bin = lean_bin_dir / "lake"
        cmd = [str(lake_bin), "env", str(lean4export_bin), module, "--", root_name]
    proc = subprocess.run(
        cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"lean4export failed for {module} -- {root_name}: rc={proc.returncode}\n{proc.stderr[-2000:]}"
        )
    if "PANIC" in proc.stderr or len(proc.stdout.splitlines()) < 2:
        raise RuntimeError(
            f"lean4export produced no declarations for {module} -- {root_name} "
            f"(likely an unknown constant): {proc.stderr[-500:]}"
        )
    return proc.stdout


def merge_rows(all_rows: list[dict]) -> list[dict]:
    by_name: dict[str, dict] = {}
    conflicts = []
    for row in all_rows:
        name = row["name"]
        if name in by_name:
            if by_name[name]["identity_digest"] != row["identity_digest"]:
                conflicts.append(name)
            continue
        by_name[name] = row
    if conflicts:
        raise RuntimeError(
            f"declaration(s) exported with disagreeing content across roots "
            f"(toolchain nondeterminism?): {sorted(conflicts)}"
        )
    return sorted(by_name.values(), key=lambda r: r["name"])


def compute_transitive(rows: list[dict]) -> None:
    """Mutates each row in place, adding `transitive_type_deps` /
    `transitive_value_deps` via ADR-0800's `compute_closure` -- the SAME
    function `scripts/check-library-artifact-contract.py` uses, not a
    reimplementation."""
    by_name = {r["name"]: r for r in rows}
    type_edges = {n: d["direct_type_deps"] for n, d in by_name.items()}
    value_edges = {
        n: list(d["direct_type_deps"]) + list(d["direct_value_deps"])
        for n, d in by_name.items()
    }
    for row in rows:
        row["transitive_type_deps"] = dg.LAC.compute_closure(set(row["direct_type_deps"]), type_edges)
        row["transitive_value_deps"] = dg.LAC.compute_closure(
            set(row["direct_type_deps"]) | set(row["direct_value_deps"]), value_edges
        )


def build_edges(rows: list[dict]) -> list[dict]:
    edges = []
    for row in rows:
        for dep in row["direct_type_deps"]:
            edges.append({"from": row["name"], "to": dep, "kind": "type"})
        for dep in row["direct_value_deps"]:
            edges.append({"from": row["name"], "to": dep, "kind": "value"})
    edges.sort(key=lambda e: (e["from"], e["to"], e["kind"]))
    return edges


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--population", required=True, help="population_id under artifacts/declaration-graph/populations/")
    parser.add_argument("--population-dir", type=Path, default=DEFAULT_POPULATION_DIR)
    parser.add_argument("--graph-dir", type=Path, default=DEFAULT_GRAPH_DIR)
    parser.add_argument("--toolchain-root", type=Path, default=DEFAULT_TOOLCHAIN_ROOT)
    parser.add_argument("--timeout", type=int, default=120, help="per-root lean4export timeout, seconds")
    args = parser.parse_args(argv)

    pop_path = args.population_dir / f"{args.population}.json"
    if not pop_path.exists():
        print(f"gen-declaration-graph: no population file at {pop_path}", file=sys.stderr)
        return 1
    population = load_json(pop_path)

    all_rows: list[dict] = []
    for root in population["requested_roots"]:
        name, module = root["name"], root["module"]
        print(f"gen-declaration-graph: exporting {module} -- {name}", file=sys.stderr)
        ndjson_text = export_root(args.toolchain_root, module, name, args.timeout)
        tmp = args.graph_dir / f".{args.population}.{name.replace('.', '_')}.tmp.ndjson"
        tmp.write_text(ndjson_text, encoding="utf-8")
        try:
            ef = dg.parse_ndjson(tmp)
            rows = dg.resolve_rows(ef, module)
        finally:
            tmp.unlink(missing_ok=True)
        all_rows.extend(rows)
        print(f"  -> {len(rows)} declaration rows in this root's closure", file=sys.stderr)

    rows = merge_rows(all_rows)
    compute_transitive(rows)
    edges = build_edges(rows)
    type_cycles = dg.classify_cycles(rows, mode="type")
    full_cycles = dg.classify_cycles(rows, mode="full")

    for c in type_cycles["unexpected_cycles"] + full_cycles["unexpected_cycles"]:
        print(f"gen-declaration-graph: WARNING unexpected cycle {c}", file=sys.stderr)

    pack = {
        "contract_version": CONTRACT_VERSION,
        "text_provenance": "lean4export",
        "lean_version": population["lean_version"],
        "lean_commit": population["lean_commit"],
        "mathlib_version": population["mathlib_version"],
        "mathlib_commit": population["mathlib_commit"],
        "normalization_version": 1,
        "renderer_version": 1,
        "source_population": {
            "population_id": population["population_id"],
            "requested_roots": [r["name"] for r in population["requested_roots"]],
            "expected_declaration_count": len(rows),
        },
        "trusted_declaration_identities": sorted(
            r["name"] for r in rows if r["kind"] in dg.TRUSTED_KINDS
        ),
        "pack_digest": dg.LAC.compute_pack_digest(rows),
        "declarations": rows,
    }

    typeproj = {
        "population_id": population["population_id"],
        "declarations": [dg.LAC.project_type_only(r) for r in rows],
    }

    cycles_report = {
        "population_id": population["population_id"],
        "type_graph": type_cycles,
        "full_graph": full_cycles,
    }

    args.graph_dir.mkdir(parents=True, exist_ok=True)
    (args.graph_dir / f"{args.population}.rows.json").write_text(
        json.dumps(pack, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    (args.graph_dir / f"{args.population}.typeproj.json").write_text(
        json.dumps(typeproj, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    (args.graph_dir / f"{args.population}.edges.json").write_text(
        json.dumps({"population_id": population["population_id"], "edges": edges}, indent=2) + "\n",
        encoding="utf-8",
    )
    (args.graph_dir / f"{args.population}.cycles.json").write_text(
        json.dumps(cycles_report, indent=2) + "\n", encoding="utf-8"
    )

    print(
        f"gen-declaration-graph: {len(rows)} declarations, {len(edges)} edges, "
        f"{len(type_cycles['expected_cycles'])} type-graph cycles "
        f"({len(type_cycles['unexpected_cycles'])} unexpected), "
        f"{len(full_cycles['expected_cycles'])} full-graph cycles "
        f"({len(full_cycles['unexpected_cycles'])} unexpected)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
