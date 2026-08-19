from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "create-autogenesis-nursery-dispatch-baseline.py"
SPEC = importlib.util.spec_from_file_location("create_autogenesis_nursery_dispatch_baseline", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DispatchBaselineTests(unittest.TestCase):
    def setUp(self) -> None:
        self.nursery = MODULE.load(MODULE.NURSERY)
        self.registry = MODULE.load(MODULE.OPERATIONS)
        self.facts = MODULE.load_facts()

    def test_repository_baseline_never_inspects_held_out(self) -> None:
        result = MODULE.build(self.nursery, self.registry, self.facts)
        self.assertFalse(result["authority"]["held_out_inspected"])
        self.assertEqual({row["partition"] for row in result["rows"]}, {"train", "development"})
        self.assertEqual(result["coverage"]["candidates"], 138)

    def test_current_population_declines_before_execution_on_surface_language(self) -> None:
        result = MODULE.build(self.nursery, self.registry, self.facts)
        self.assertEqual(result["coverage"]["eligible_for_dispatch"], 0)
        self.assertEqual(
            result["coverage"]["decline_reasons"],
            {"unsupported-formal-language:lean4-surface": 138},
        )
        self.assertEqual(result["budget"]["executor_invocations"], 0)

    def test_matching_authoritative_operation_is_dispatchable(self) -> None:
        fact = {"id": "F:x", "formal": {"language": "lean4-surface", "fragment": "Nat"}}
        operation = {
            "id": "op",
            "applicability": {
                "fact_ids": ["F:x"],
                "formal_languages": ["lean4-surface"],
                "fragments": ["Nat"],
            },
        }
        self.assertEqual(MODULE.classify(fact, [operation]), ("dispatchable", ["op"]))

    def test_population_drift_fails_closed(self) -> None:
        nursery = copy.deepcopy(self.nursery)
        nursery["entries"] = nursery["entries"][:-1]
        with self.assertRaisesRegex(MODULE.BaselineError, "expected 138"):
            MODULE.build(nursery, self.registry, self.facts)


if __name__ == "__main__":
    unittest.main()
