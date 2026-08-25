from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "create-autogenesis-reflexivity-coverage-input.py"
SPEC = importlib.util.spec_from_file_location(
    "create_autogenesis_reflexivity_coverage_input", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ReflexivityCoverageInputTests(unittest.TestCase):
    MODULES = {"family-a": "Mathlib.A", "family-b": "Mathlib.B"}

    def nursery(self):
        entries = []
        for index in range(138):
            entries.append(
                {
                    "fact_id": f"F:selected-{index:03d}",
                    "family": "family-a" if index % 2 else "family-b",
                    "partition": "train" if index < 78 else "development",
                }
            )
        entries.append(
            {
                "fact_id": "F:sealed",
                "family": "sealed-family",
                "partition": "held-out",
            }
        )
        return {"state": "frozen-evaluation", "entries": entries}

    @staticmethod
    def fact(fact_id):
        return {
            "id": fact_id,
            "formal": {"language": "lean4-surface", "statement": "∀ n : ℕ, n = n"},
        }

    def test_build_opens_only_train_and_development_facts(self):
        opened = []

        def load(fact_id):
            opened.append(fact_id)
            if fact_id == "F:sealed":
                raise AssertionError("held-out fact was opened")
            return self.fact(fact_id)

        # `expected=138` is this fixture's OWN population size (78 train + 60
        # development, built by `nursery()` above), passed explicitly rather
        # than relying on `MODULE.LIVE_POPULATION`. The fixture has no business
        # depending on a constant that tracks the real nursery -- that live
        # count moved 138 -> 157 on 2026-08-22 for a legitimate reason (a
        # held-out family graduating to development) and had nothing to do
        # with this synthetic population.
        source, mapping = MODULE.build(self.nursery(), load, self.MODULES, expected=138)
        self.assertEqual(len(opened), 138)
        self.assertNotIn("F:sealed", opened)
        self.assertEqual(mapping["authority"]["held_out_inspected"], False)
        self.assertEqual(mapping["authority"]["facts_opened"], 138)
        self.assertEqual(source.count("def r"), 138)
        self.assertNotIn("sealed", source)

    def test_output_is_deterministic_under_entry_reordering(self):
        nursery = self.nursery()
        first = MODULE.build(nursery, self.fact, self.MODULES, expected=138)
        changed = copy.deepcopy(nursery)
        changed["entries"].reverse()
        second = MODULE.build(changed, self.fact, self.MODULES, expected=138)
        self.assertEqual(first[0], second[0])
        self.assertEqual(first[1]["rows"], second[1]["rows"])

    def test_wrong_population_size_is_rejected(self):
        nursery = self.nursery()
        nursery["entries"].pop(0)
        with self.assertRaisesRegex(MODULE.CoverageInputError, "expected 138"):
            MODULE.build(nursery, self.fact, self.MODULES, expected=138)

    def test_non_surface_fact_is_rejected(self):
        def load(fact_id):
            fact = self.fact(fact_id)
            fact["formal"]["language"] = "lean-kernel"
            return fact

        with self.assertRaisesRegex(MODULE.CoverageInputError, "unexpected language"):
            MODULE.build(self.nursery(), load, self.MODULES, expected=138)


if __name__ == "__main__":
    unittest.main()
