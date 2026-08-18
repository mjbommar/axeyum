#!/usr/bin/env python3
"""Build or verify the proof-derived B -> A candidate catalog."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import pathlib
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
DEPENDENCY_CHECKER = ROOT / "scripts/check-fact-depends-derived.py"


class ChainCatalogError(RuntimeError):
    """A proof-derived chain catalog cannot be constructed exactly."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def dependency_module():
    spec = importlib.util.spec_from_file_location(
        "depends_derived_for_autogenesis_chain_catalog", DEPENDENCY_CHECKER
    )
    if spec is None or spec.loader is None:
        raise ChainCatalogError(f"cannot load {DEPENDENCY_CHECKER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        fact_id = fact.get("id")
        if not isinstance(fact_id, str) or fact_id in facts:
            raise ChainCatalogError(f"malformed or duplicate fact id in {path}")
        facts[fact_id] = fact
    return facts


def theorem_index(
    facts: dict[str, dict[str, Any]], theorem_of
) -> tuple[dict[str, str], list[str]]:
    by_theorem: dict[str, str] = {}
    unnamed: list[str] = []
    for fact_id, fact in sorted(facts.items()):
        if fact.get("proof_route") != "kernel-lean" or fact.get(
            "epistemic_status"
        ) not in {"proved", "computed"}:
            continue
        theorem = theorem_of(fact)
        if theorem is None:
            unnamed.append(fact_id)
            continue
        if theorem in by_theorem:
            raise ChainCatalogError(
                f"kernel theorem {theorem!r} maps to multiple fact rows"
            )
        by_theorem[theorem] = fact_id
    return by_theorem, unnamed


def build_catalog(
    facts: dict[str, dict[str, Any]],
    graph: dict[str, list[str]],
    theorem_of,
) -> dict[str, Any]:
    if len(graph) < 1:
        raise ChainCatalogError("kernel dependency inventory is empty")
    by_theorem, unnamed = theorem_index(facts, theorem_of)
    missing_inventory = sorted(
        by_theorem[theorem] for theorem in by_theorem if theorem not in graph
    )

    edges: list[tuple[str, str, str, str]] = []
    for consequent_theorem, consequent_id in sorted(by_theorem.items()):
        if consequent_theorem not in graph:
            continue
        declared = set(facts[consequent_id].get("depends_on") or [])
        for premise_theorem in sorted(set(graph[consequent_theorem])):
            premise_id = by_theorem.get(premise_theorem)
            if premise_id is None or premise_id == consequent_id:
                continue
            if premise_id not in declared:
                raise ChainCatalogError(
                    f"proof-derived edge {premise_id} -> {consequent_id} is absent from depends_on"
                )
            edges.append(
                (premise_id, consequent_id, premise_theorem, consequent_theorem)
            )
    if not edges:
        raise ChainCatalogError("kernel-lean subgraph has no proof-derived edge")

    parents: dict[str, list[str]] = {}
    for premise_id, consequent_id, _, _ in edges:
        parents.setdefault(consequent_id, []).append(premise_id)
    depth_cache: dict[str, int] = {}

    def depth(fact_id: str, active: tuple[str, ...] = ()) -> int:
        if fact_id in depth_cache:
            return depth_cache[fact_id]
        if fact_id in active:
            raise ChainCatalogError("proof-derived fact graph contains a cycle")
        value = 1 + max(
            (depth(parent, active + (fact_id,)) for parent in parents.get(fact_id, [])),
            default=0,
        )
        depth_cache[fact_id] = value
        return value

    candidates: list[dict[str, Any]] = []
    for premise_id, consequent_id, premise_theorem, consequent_theorem in edges:
        premise = facts[premise_id]
        consequent = facts[consequent_id]
        other_dependencies = sorted(
            dependency
            for dependency in consequent.get("depends_on") or []
            if dependency != premise_id
        )
        axiom_free = (
            premise.get("axiom_footprint") == []
            and consequent.get("axiom_footprint") == []
        )
        other_dependencies_established = all(
            dependency in facts
            and facts[dependency].get("epistemic_status")
            in {"axiom", "proved", "computed", "refuted"}
            for dependency in other_dependencies
        )
        candidate: dict[str, Any] = {
            "premise": {
                "fact_id": premise_id,
                "fact_sha256": digest(premise),
                "theorem": premise_theorem,
            },
            "consequent": {
                "fact_id": consequent_id,
                "fact_sha256": digest(consequent),
                "theorem": consequent_theorem,
                "other_dependencies": other_dependencies,
            },
            "proof_derived_direct_edge": True,
            "axiom_free": axiom_free,
            "counterfactual_last_missing_dependency": other_dependencies_established,
            "rank": {
                "other_dependency_count": len(other_dependencies),
                "consequent_depth": depth(consequent_id),
            },
            "qualification": {
                "state": "unmeasured",
                "requires_same_target_pre_b_no_credit": True,
                "requires_b_production": True,
                "requires_post_b_a_production_with_derived_dependency": True,
                "requires_proof_leakage_audit": True,
            },
        }
        candidate["chain_id"] = digest(
            {
                "premise_fact_id": premise_id,
                "consequent_fact_id": consequent_id,
                "premise_theorem": premise_theorem,
                "consequent_theorem": consequent_theorem,
            }
        )
        candidates.append(candidate)
    candidates.sort(
        key=lambda row: (
            not row["axiom_free"],
            not row["counterfactual_last_missing_dependency"],
            row["rank"]["other_dependency_count"],
            row["rank"]["consequent_depth"],
            row["consequent"]["fact_id"],
            row["premise"]["fact_id"],
        )
    )

    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-proof-derived-chain-catalog",
        "authority": {
            "fact_ledger_sha256": digest(
                [
                    {"fact_id": fact_id, "fact_sha256": digest(facts[fact_id])}
                    for fact_id in sorted(facts)
                ]
            ),
            "theorem_dependency_inventory_sha256": digest(graph),
        },
        "policy": {
            "routes": ["kernel-lean"],
            "edge_requirement": "direct-kernel-theorem-dependency-and-declared-fact-edge",
            "autonomous_selection_requires_qualification": True,
            "ranking": [
                "axiom-free-first",
                "all-other-dependencies-established-first",
                "fewest-other-dependencies",
                "shallowest-consequent",
                "lexicographic-fact-ids",
            ],
        },
        "coverage": {
            "fact_count": len(facts),
            "named_kernel_facts": len(by_theorem),
            "unnamed_kernel_fact_ids": unnamed,
            "missing_inventory_fact_ids": missing_inventory,
            "proof_derived_edges": len(candidates),
            "distinct_consequents": len(
                {row["consequent"]["fact_id"] for row in candidates}
            ),
            "axiom_free_edges": sum(row["axiom_free"] for row in candidates),
            "maximum_depth": max(depth_cache.values()),
        },
        "candidates": candidates,
        "selection": {
            "outcome": "refused-no-qualified-chain",
            "selected_chain_id": None,
            "reason": "structural candidates require operational qualification evidence",
        },
    }
    catalog["catalog_sha256"] = digest(catalog)
    return catalog


def verify_catalog(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    unsigned = dict(actual)
    claimed = unsigned.pop("catalog_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ChainCatalogError("chain catalog digest is missing or invalid")
    if actual != expected:
        raise ChainCatalogError("chain catalog is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true")
    action.add_argument("--json", action="store_true")
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        dependencies = dependency_module()
        graph = dependencies.inventory()
        if len(graph) < 100:
            raise ChainCatalogError(
                f"dependency inventory returned only {len(graph)} theorems"
            )
        catalog = build_catalog(load_facts(), graph, dependencies.theorem_of)
        if args.check:
            print(
                f"AUTOGENESIS_CHAIN_CATALOG_OK|{catalog['catalog_sha256']}|"
                f"edges={catalog['coverage']['proof_derived_edges']}|"
                f"consequents={catalog['coverage']['distinct_consequents']}|"
                f"missing_inventory={len(catalog['coverage']['missing_inventory_fact_ids'])}"
            )
        elif args.verify is not None:
            verify_catalog(json.loads(args.verify.read_text()), catalog)
            print(f"AUTOGENESIS_CHAIN_CATALOG_OK|{catalog['catalog_sha256']}")
        elif args.output is not None:
            output = args.output.resolve()
            if output.exists():
                raise ChainCatalogError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(catalog, indent=2, sort_keys=True) + "\n")
            print(f"AUTOGENESIS_CHAIN_CATALOG|{catalog['catalog_sha256']}|{output}")
        else:
            print(json.dumps(catalog, indent=2, sort_keys=True))
        return 0
    except (
        OSError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ChainCatalogError,
    ) as error:
        print(f"AUTOGENESIS_CHAIN_CATALOG_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
