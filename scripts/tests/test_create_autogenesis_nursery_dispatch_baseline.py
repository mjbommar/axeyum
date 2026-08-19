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

    def test_current_population_selects_only_the_registered_checked_candidate(self) -> None:
        result = MODULE.build(self.nursery, self.registry, self.facts)
        self.assertEqual(result["coverage"]["eligible_for_dispatch"], 1)
        self.assertEqual(
            result["coverage"]["decline_reasons"],
            {
                "no-exact-authoritative-operation": 137,
            },
        )
        self.assertEqual(result["coverage"]["already_established"], 0)
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

    def test_adapter_readiness_does_not_claim_dispatch(self) -> None:
        fact = {"id": "F:x", "formal": {"language": "lean4-surface", "fragment": "Nat"}}
        self.assertEqual(
            MODULE.classify(fact, [], {"F:x"}),
            ("statement-adapter-ready:no-authoritative-producer", []),
        )

    def test_checked_candidate_does_not_claim_dispatch_or_admission(self) -> None:
        fact = {"id": "F:x", "formal": {"language": "lean4-surface", "fragment": "Nat"}}
        self.assertEqual(
            MODULE.classify(fact, [], {"F:x"}, {"F:x"}),
            ("reflexivity-candidate-checked:not-registered-or-admitted", []),
        )

    def test_established_row_is_not_redispatched(self) -> None:
        nursery = copy.deepcopy(self.nursery)
        facts = copy.deepcopy(self.facts)
        fact_id = "F:ml430-nat-ascfactorial-zero-fd183202"
        facts[fact_id]["epistemic_status"] = "proved"
        result = MODULE.build(nursery, self.registry, facts)
        row = next(row for row in result["rows"] if row["fact_id"] == fact_id)
        self.assertEqual(row["outcome"], "already-established")
        self.assertIsNone(row["decline_reason"])
        self.assertEqual(result["coverage"]["already_established"], 1)

    def test_population_drift_fails_closed(self) -> None:
        nursery = copy.deepcopy(self.nursery)
        nursery["entries"] = nursery["entries"][:-1]
        with self.assertRaisesRegex(MODULE.BaselineError, "expected 138"):
            MODULE.build(nursery, self.registry, self.facts)


if __name__ == "__main__":
    unittest.main()
