from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import unittest


SCRIPT = Path(__file__).parents[1] / "check-autogenesis-semantic-abstraction-census.py"
SPEC = importlib.util.spec_from_file_location(
    "check_autogenesis_semantic_abstraction_census", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def digest(seed: str) -> str:
    return (seed * 64)[:64]


class SemanticAbstractionCensusTests(unittest.TestCase):
    def test_immutable_census_is_accepted(self):
        manifest = MODULE.validate()
        self.assertEqual(manifest["population"], MODULE.EXPECTED_POPULATION)

    def descriptor(self):
        return {
            "artifacts": ["r001.ndjson"],
            "axiom_footprint": ["propext"],
            "bindings": 1,
            "contract_shape": "pointwise-function-equation",
            "direct_theorem_dependencies": ["Nat.add_comm"],
            "facts": ["F:test"],
            "families": ["control"],
            "first_artifact": "r001.ndjson",
            "instantiated_type_sha256": digest("b"),
            "name": "Control.f",
            "normalization_rewrites": 0,
            "returns_prop": False,
            "source_content_sha256": digest("a"),
            "source_occurrences": 1,
            "trusted_closure": {
                "axiom": ["propext"],
                "theorem": ["Nat.add_comm"],
            },
            "type_pi_binders": 1,
            "universe_sha256": [digest("c")],
            "value_body_kind": "application",
            "value_expression_nodes": 3,
            "value_lambda_binders": 1,
        }

    def assert_rejected(self, mutate, message):
        row = copy.deepcopy(self.descriptor())
        mutate(row)
        with self.assertRaisesRegex(MODULE.SemanticCensusError, message):
            MODULE.validate_definition(row)

    def test_exact_descriptor_is_accepted(self):
        identity, bindings, occurrences, trusted = MODULE.validate_definition(
            self.descriptor()
        )
        self.assertTrue(identity.startswith("Control.f|"))
        self.assertEqual((bindings, occurrences), (1, 1))
        self.assertEqual(trusted, {"axiom": 1, "theorem": 1})

    def test_hash_mutation_is_rejected(self):
        self.assert_rejected(
            lambda row: row.__setitem__("source_content_sha256", "bad"), "digest"
        )

    def test_unsorted_artifacts_are_rejected(self):
        def mutate(row):
            row["artifacts"] = ["r002.ndjson", "r001.ndjson"]
            row["bindings"] = 2
            row["facts"] = ["F:a", "F:b"]

        self.assert_rejected(mutate, "sorted")

    def test_binding_population_mutation_is_rejected(self):
        self.assert_rejected(lambda row: row.__setitem__("bindings", 2), "population")

    def test_contract_shape_is_derived_from_checked_type(self):
        self.assert_rejected(
            lambda row: row.__setitem__("contract_shape", "predicate-equivalence"),
            "contract shape",
        )

    def test_empty_trusted_closure_is_rejected(self):
        self.assert_rejected(lambda row: row.__setitem__("trusted_closure", {}), "absent")

    def test_direct_theorem_must_be_in_closure(self):
        self.assert_rejected(
            lambda row: row.__setitem__(
                "direct_theorem_dependencies", ["Missing.theorem"]
            ),
            "direct theorem",
        )

    def test_expression_node_count_is_positive(self):
        self.assert_rejected(
            lambda row: row.__setitem__("value_expression_nodes", 0), "shape"
        )

    def test_universe_identity_is_checked(self):
        self.assert_rejected(
            lambda row: row.__setitem__("universe_sha256", ["bad"]), "digest"
        )


if __name__ == "__main__":
    unittest.main()
