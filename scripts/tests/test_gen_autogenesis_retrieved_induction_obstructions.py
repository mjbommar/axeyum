import copy
import importlib.util
import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-autogenesis-retrieved-induction-obstructions.py"
SPEC = importlib.util.spec_from_file_location("retrieved_obstructions", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RetrievedInductionObstructionProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.census = json.loads(MODULE.CENSUS.read_text())
        cls.ranking = json.loads(MODULE.RANKING.read_text())

    def build(self, census=None, ranking=None):
        return MODULE.build(
            census or self.census,
            ranking or self.ranking,
            census_path=MODULE.CENSUS,
            ranking_path=MODULE.RANKING,
        )

    def test_live_population_is_partitioned_without_control_leakage(self):
        result = self.build()
        self.assertEqual(result["census"]["rows"], 51)
        self.assertEqual(result["census"]["positive_targets"], 45)
        self.assertEqual(result["census"]["must_decline_controls"], 6)
        self.assertEqual(result["census"]["accepted_positive_targets"], 1)
        self.assertEqual(result["census"]["accepted_must_decline_controls"], 0)
        self.assertTrue(
            all(row["eligible_for_strategy_queue"] for row in result["strategy_queue"])
        )
        self.assertTrue(
            all(
                not row["eligible_for_strategy_queue"]
                for row in result["control_observations"]
            )
        )

    def test_positive_demands_match_measured_stage_boundaries(self):
        self.assertEqual(
            self.build()["census"]["positive_demand"],
            {
                "authoritative-operation-integration": 1,
                "binder-or-generalization": 1,
                "missing-rewrite-or-induction-plan": 5,
                "non-equality-terminal-family": 13,
                "type-slice-generalization": 25,
            },
        )

    def test_accepted_control_fails_closed(self):
        census = copy.deepcopy(self.census)
        control = next(
            row
            for row in census["outcomes"]
            if row["evaluation_class"] == "must-decline-control"
        )
        control["result"] = "accepted"
        with self.assertRaisesRegex(ValueError, "must-decline controls were accepted"):
            self.build(census=census)

    def test_unknown_evaluation_class_fails_closed(self):
        census = copy.deepcopy(self.census)
        census["outcomes"][0]["evaluation_class"] = "held-out-target"
        with self.assertRaisesRegex(ValueError, "unknown evaluation class"):
            self.build(census=census)

    def test_missing_ranking_row_fails_closed(self):
        ranking = copy.deepcopy(self.ranking)
        missing = self.census["outcomes"][0]["fact_id"]
        ranking["goals"] = [
            row for row in ranking["goals"] if row["fact_id"] != missing
        ]
        census = copy.deepcopy(self.census)
        census["source"]["candidate_ranking"]["sha256"] = MODULE.digest(MODULE.RANKING)
        with self.assertRaisesRegex(ValueError, "census fact is absent from ranking"):
            self.build(census=census, ranking=ranking)


if __name__ == "__main__":
    unittest.main()
