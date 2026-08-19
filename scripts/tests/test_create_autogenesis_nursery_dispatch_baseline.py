from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import unittest
from unittest import mock


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

    def test_fact_loader_does_not_open_held_out_paths(self) -> None:
        nursery = {
            "entries": [
                {"fact_id": "F:open", "partition": "train"},
                {"fact_id": "F:sealed", "partition": "held-out"},
            ]
        }
        opened = []

        def load(path):
            opened.append(path.name)
            return {"id": "F:open"}

        with mock.patch.object(MODULE, "load", side_effect=load):
            facts = MODULE.load_selected_facts(nursery)
        self.assertEqual(facts, {"F:open": {"id": "F:open"}})
        self.assertEqual(opened, ["F-open.json"])

    def test_current_population_separates_admitted_row_from_pre_execution_declines(self) -> None:
        result = MODULE.build(self.nursery, self.registry, self.facts)
        self.assertEqual(result["coverage"]["eligible_for_dispatch"], 1)
        self.assertEqual(
            result["coverage"]["decline_reasons"],
            {
                "no-exact-authoritative-operation": 136,
            },
        )
        self.assertEqual(result["coverage"]["already_established"], 1)
        self.assertEqual(result["budget"]["executor_invocations"], 0)

        fact_id = "F:ml430-nat-descfactorial-zero-966b01df"
        row = next(row for row in result["rows"] if row["fact_id"] == fact_id)
        self.assertEqual(row["outcome"], "eligible-for-dispatch")
        self.assertTrue(row["statement_adapter_ready"])
        self.assertTrue(row["reflexivity_candidate_checked"])

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
