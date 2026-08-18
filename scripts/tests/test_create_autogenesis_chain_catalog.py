from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "create-autogenesis-chain-catalog.py"
SPEC = importlib.util.spec_from_file_location("autogenesis_chain_catalog", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fact(fact_id: str, theorem: str, dependencies: list[str]) -> dict:
    return {
        "id": fact_id,
        "epistemic_status": "proved",
        "proof_route": "kernel-lean",
        "axiom_footprint": [],
        "depends_on": dependencies,
        "evidence": [{"theorem": theorem}],
    }


def theorem_of(value):
    return value["evidence"][0]["theorem"]


class ChainCatalogTests(unittest.TestCase):
    def inputs(self):
        facts = {
            "F:B": fact("F:B", "Nat.b", []),
            "F:A": fact("F:A", "Nat.a", ["F:B", "F:C"]),
            "F:C": fact("F:C", "Nat.c", []),
            "F:authored-only": fact("F:authored-only", "Nat.authored", ["F:B"]),
        }
        graph = {
            "Nat.b": [],
            "Nat.a": ["Nat.b"],
            "Nat.c": [],
            "Nat.authored": [],
        }
        return facts, graph

    def test_only_direct_kernel_dependency_becomes_a_candidate(self):
        facts, graph = self.inputs()
        catalog = MODULE.build_catalog(facts, graph, theorem_of)
        self.assertEqual(catalog["coverage"]["proof_derived_edges"], 1)
        candidate = catalog["candidates"][0]
        self.assertEqual(candidate["premise"]["fact_id"], "F:B")
        self.assertEqual(candidate["consequent"]["fact_id"], "F:A")
        self.assertEqual(candidate["consequent"]["other_dependencies"], ["F:C"])
        self.assertEqual(catalog["selection"]["selected_chain_id"], None)

    def test_missing_declared_edge_fails_closed(self):
        facts, graph = self.inputs()
        facts["F:A"]["depends_on"] = ["F:C"]
        with self.assertRaisesRegex(MODULE.ChainCatalogError, "absent"):
            MODULE.build_catalog(facts, graph, theorem_of)

    def test_catalog_is_deterministic_and_content_addressed(self):
        facts, graph = self.inputs()
        first = MODULE.build_catalog(facts, graph, theorem_of)
        second = MODULE.build_catalog(copy.deepcopy(facts), copy.deepcopy(graph), theorem_of)
        self.assertEqual(first, second)
        MODULE.verify_catalog(first, second)
        mutated = copy.deepcopy(first)
        mutated["candidates"][0]["axiom_free"] = False
        mutated["catalog_sha256"] = MODULE.digest(
            {key: value for key, value in mutated.items() if key != "catalog_sha256"}
        )
        with self.assertRaisesRegex(MODULE.ChainCatalogError, "stale"):
            MODULE.verify_catalog(mutated, second)

    def test_duplicate_theorem_mapping_is_rejected(self):
        facts, graph = self.inputs()
        facts["F:duplicate"] = fact("F:duplicate", "Nat.b", [])
        with self.assertRaisesRegex(MODULE.ChainCatalogError, "multiple"):
            MODULE.build_catalog(facts, graph, theorem_of)

    def test_named_fact_outside_inventory_is_reported_not_inferred(self):
        facts, graph = self.inputs()
        graph.pop("Nat.authored")
        catalog = MODULE.build_catalog(facts, graph, theorem_of)
        self.assertEqual(
            catalog["coverage"]["missing_inventory_fact_ids"], ["F:authored-only"]
        )
        self.assertNotIn(
            "F:authored-only",
            [row["consequent"]["fact_id"] for row in catalog["candidates"]],
        )


if __name__ == "__main__":
    unittest.main()
