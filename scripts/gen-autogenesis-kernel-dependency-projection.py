#!/usr/bin/env python3
"""Generate the kernel-observed declaration/dependency projection for Autogenesis.

This is a sidecar over the constructed kernel library.  It does not change a
fact's human planning `depends_on`: its edges are direct theorem references read
from accepted kernel declarations.  Non-theorem declaration kinds are retained
as nodes but never receive invented proof-dependency edges.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json"
COMMAND = [
    "cargo", "run", "-q", "-p", "axeyum-lean-kernel", "--example",
    "kernel_declaration_projection",
]


def inventory() -> dict[str, dict[str, object]]:
    proc = subprocess.run(
        COMMAND, cwd=ROOT, check=True, capture_output=True, text=True, timeout=1800
    )
    rows: dict[str, dict[str, object]] = {}
    for line in proc.stdout.splitlines():
        prelude, kind, name, footprint, dependencies, canonical_type = line.split("\t", 5)
        direct = [dependency for dependency in dependencies.split(",") if dependency]
        row = {
            "id": name,
            "declaration_kind": kind,
            "visible_in": [prelude],
            "axiom_footprint_size": int(footprint),
            "direct_theorem_dependencies": direct,
            "canonical_type": canonical_type,
        }
        prior = rows.get(name)
        if prior is None:
            rows[name] = row
            continue
        for field in (
            "declaration_kind",
            "axiom_footprint_size",
            "direct_theorem_dependencies",
            "canonical_type",
        ):
            if prior[field] != row[field]:
                raise ValueError(f"inconsistent {field} for declaration {name}")
        cast = prior["visible_in"]
        assert isinstance(cast, list)
        cast.append(prelude)
    for row in rows.values():
        visible = row["visible_in"]
        assert isinstance(visible, list)
        row["visible_in"] = sorted(visible)
    return dict(sorted(rows.items()))


def projection() -> dict[str, object]:
    declarations = inventory()
    edges = []
    for name, row in declarations.items():
        if row["declaration_kind"] != "theorem":
            continue
        dependencies = row["direct_theorem_dependencies"]
        assert isinstance(dependencies, list)
        for dependency in dependencies:
            target = declarations.get(dependency)
            if target is None:
                raise ValueError(f"theorem {name} depends on absent declaration {dependency}")
            if target["declaration_kind"] != "theorem":
                raise ValueError(f"theorem {name} dependency {dependency} is not a theorem")
            edges.append({"source": name, "target": dependency, "relation": "direct-theorem-depends-on"})
    edges.sort(key=lambda edge: (edge["source"], edge["target"]))
    kinds = Counter(str(row["declaration_kind"]) for row in declarations.values())
    axiom_free = sum(row["axiom_footprint_size"] == 0 for row in declarations.values())
    return {
        "schema_version": 1,
        "kind": "axeyum-kernel-dependency-projection",
        "derivation": {
            "method": "kernel-derived",
            "command": " ".join(COMMAND),
            "scope": "all constructed Axeyum kernel preludes",
            "edge_semantics": "direct theorem references from accepted theorem terms only",
            "non_theorem_policy": "definitions, inductives, constructors, recursors, axioms, opaque constants, and quotient declarations are nodes only; this projection does not invent theorem-dependency edges for them",
        },
        "census": {
            "declarations": len(declarations),
            "theorems": kinds["theorem"],
            "direct_theorem_dependency_edges": len(edges),
            "axiom_free_declarations": axiom_free,
            "declaration_kinds": dict(sorted(kinds.items())),
        },
        "declarations": list(declarations.values()),
        "direct_theorem_dependency_edges": edges,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(projection(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            print("AUTOGENESIS_KERNEL_PROJECTION_ERROR|projection is stale", file=sys.stderr)
            return 1
    else:
        OUTPUT.write_text(rendered)
    data = json.loads(rendered)
    census = data["census"]
    print(
        "AUTOGENESIS_KERNEL_PROJECTION|"
        f"declarations={census['declarations']}|theorems={census['theorems']}|"
        f"edges={census['direct_theorem_dependency_edges']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
