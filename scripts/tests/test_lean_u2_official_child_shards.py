from __future__ import annotations

import copy
import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_official_child_shards",
    ROOT / "scripts/gen-lean-u2-official-child-shards.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2OfficialChildShardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.expected = GEN.build_authority()

    def authority(self) -> dict:
        return copy.deepcopy(self.expected)

    def assert_rejected(self, authority: dict) -> None:
        resealed = GEN.seal(authority, GEN.SCHEMA)
        self.assertTrue(GEN.validate_authority(resealed))

    def test_committed_authority_is_exact_deterministic_and_non_executed(self) -> None:
        observed = GEN.load_json(GEN.MANIFEST)
        self.assertEqual(observed, self.expected)
        self.assertEqual(GEN.validate_authority(observed), [])
        self.assertEqual(GEN.check_outputs(observed), [])
        self.assertEqual(
            observed["summary"],
            {
                "registration_cases": 3723,
                "selection_sets": 8,
                "official_attempts": 111,
                "distinct_membership_plans": 5,
                "distinct_membership_case_occurrences": 18277,
                "physical_child_shards": 289,
                "selection_expanded_shard_occurrences": 461,
                "attempt_expanded_shard_occurrences": 6451,
                "selected_case_union": 3723,
                "selected_case_union_sha256": (
                    "21e9bc117f0bedb7e80cd2f87ac8cb7d5032af4a946d6666f4298e531b1e5369"
                ),
                "historical_unique_observed_cases": 1,
                "outcomes_observed_by_m1": 0,
            },
        )
        self.assertEqual(observed["credits"], GEN.ZERO_CREDITS)
        self.assertFalse(observed["claims"]["lean_parity_established"])

    def test_membership_partition_closure_order_and_bound_are_exact(self) -> None:
        authority = self.authority()
        profiles = GEN.load_json(GEN.PROFILES_PATH)
        selections = {row["id"]: row for row in profiles["selection_sets"]}
        shards = {row["id"]: row for row in authority["shards"]}
        for membership in authority["membership_plans"]:
            source_ids = selections[membership["selection_set_ids"][0]][
                "selected_case_ids"
            ]
            reconstructed = []
            for ordinal, shard_id in enumerate(membership["shard_ids"]):
                shard = shards[shard_id]
                self.assertEqual(shard["ordinal"], ordinal)
                self.assertEqual(shard["start_offset"], len(reconstructed))
                self.assertGreater(shard["case_count"], 0)
                self.assertLessEqual(shard["case_count"], 64)
                reconstructed.extend(shard["case_ids"])
                self.assertEqual(shard["end_offset"], len(reconstructed))
                self.assertEqual(shard["outcome"], "not-run")
            self.assertEqual(reconstructed, source_ids)
            for selection_id in membership["selection_set_ids"]:
                self.assertEqual(selections[selection_id]["selected_case_ids"], source_ids)

    def test_exact_membership_deduplication_keeps_all_selection_identities(self) -> None:
        authority = self.authority()
        groups = [row["selection_set_ids"] for row in authority["membership_plans"]]
        self.assertIn(
            ["default-all", "default-filtered-aec7358564e4"], groups
        )
        self.assertIn(
            ["full-lake-all", "full-lake-filtered-6325d6cffd5d"], groups
        )
        self.assertIn(
            ["default-filtered-d1bb9722e72c", "full-lake-filtered-d803b176baa6"],
            groups,
        )
        self.assertEqual(
            [row["selection_set_id"] for row in authority["selection_bindings"]],
            sorted(row["selection_set_id"] for row in authority["selection_bindings"]),
        )

    def test_attempt_bindings_are_closed_and_all_not_run(self) -> None:
        authority = self.authority()
        profiles = GEN.load_json(GEN.PROFILES_PATH)
        attempts = {row["id"]: row for row in profiles["attempts"]}
        selections = {
            row["selection_set_id"]: row for row in authority["selection_bindings"]
        }
        self.assertEqual(len(authority["attempt_bindings"]), len(attempts))
        for binding in authority["attempt_bindings"]:
            source = attempts[binding["attempt_id"]]
            selection = selections[binding["selection_set_id"]]
            self.assertEqual(binding["source_attempt_sha256"], source["sha256"])
            self.assertEqual(binding["shard_ids"], selection["shard_ids"])
            self.assertEqual(binding["outcome"], "not-run")

    def test_historical_m0_case_is_annotation_only(self) -> None:
        history = self.authority()["historical_observation"]
        self.assertEqual(history["case_id"], "compile/534.lean")
        self.assertEqual(history["process_attempts"], 4)
        self.assertEqual(history["official_outcomes"], 2)
        self.assertEqual((history["official_passes"], history["official_failures"]), (1, 1))
        self.assertFalse(history["completes_m1_shard"])
        containing = [
            row
            for row in self.authority()["shards"]
            if history["case_id"] in row["case_ids"]
        ]
        self.assertGreater(len(containing), 0)
        self.assertTrue(
            all(row["historical_observation_case_ids"] == [history["case_id"]] for row in containing)
        )
        self.assertTrue(all(row["outcome"] == "not-run" for row in containing))

    def test_input_physical_validator_and_parent_semantic_drift_fail_closed(self) -> None:
        source_hashes = dict(GEN.SOURCE_HASHES)
        source_hashes[next(iter(source_hashes))] = "0" * 64
        with mock.patch.object(GEN, "SOURCE_HASHES", source_hashes):
            with self.assertRaisesRegex(GEN.ShardError, "source authority drift"):
                GEN.build_authority()

        validator_hashes = dict(GEN.VALIDATOR_HASHES)
        validator_hashes[next(iter(validator_hashes))] = "0" * 64
        with mock.patch.object(GEN, "VALIDATOR_HASHES", validator_hashes):
            with self.assertRaisesRegex(GEN.ShardError, "validator source drift"):
                GEN.build_authority()

        original_load = GEN.load_json

        def load_with_bad_schema(path: Path) -> dict:
            value = original_load(path)
            if path == GEN.U2_PATH:
                value["schema"] = "mutated"
            return value

        with mock.patch.object(GEN, "load_json", side_effect=load_with_bad_schema):
            with self.assertRaisesRegex(GEN.ShardError, "invalid frozen parent"):
                GEN.build_authority()

    def test_membership_shard_and_case_closure_mutations_are_rejected(self) -> None:
        mutations = []

        missing_shard = self.authority()
        missing_shard["shards"].pop()
        mutations.append(missing_shard)

        reordered_shards = self.authority()
        reordered_shards["shards"][0], reordered_shards["shards"][1] = (
            reordered_shards["shards"][1],
            reordered_shards["shards"][0],
        )
        mutations.append(reordered_shards)

        bad_bound = self.authority()
        shard = bad_bound["shards"][0]
        shard["case_ids"].append(shard["case_ids"][0])
        shard["case_count"] += 1
        shard["end_offset"] += 1
        bad_bound["shards"][0] = GEN.seal(shard, GEN.SHARD_DOMAIN)
        mutations.append(bad_bound)

        bad_offset = self.authority()
        shard = bad_offset["shards"][0]
        shard["start_offset"] = 1
        bad_offset["shards"][0] = GEN.seal(shard, GEN.SHARD_DOMAIN)
        mutations.append(bad_offset)

        reordered_cases = self.authority()
        shard = reordered_cases["shards"][0]
        shard["case_ids"][0], shard["case_ids"][1] = (
            shard["case_ids"][1],
            shard["case_ids"][0],
        )
        shard["first_case_id"] = shard["case_ids"][0]
        reordered_cases["shards"][0] = GEN.seal(shard, GEN.SHARD_DOMAIN)
        mutations.append(reordered_cases)

        for authority in mutations:
            with self.subTest(kind=len(authority["shards"])):
                self.assert_rejected(authority)

    def test_selection_attempt_outcome_history_claim_and_credit_mutations_are_rejected(self) -> None:
        mutations = []

        selection = self.authority()
        selection["selection_bindings"][0]["membership_plan_id"] = "invented"
        selection["selection_bindings"][0] = GEN.seal(
            selection["selection_bindings"][0], GEN.SELECTION_DOMAIN
        )
        mutations.append(selection)

        attempt = self.authority()
        attempt["attempt_bindings"][0]["outcome"] = "passed"
        attempt["attempt_bindings"][0] = GEN.seal(
            attempt["attempt_bindings"][0], GEN.ATTEMPT_DOMAIN
        )
        mutations.append(attempt)

        history = self.authority()
        history["historical_observation"]["completes_m1_shard"] = True
        history["historical_observation"] = GEN.seal(
            history["historical_observation"], GEN.HISTORY_DOMAIN
        )
        mutations.append(history)

        claim = self.authority()
        claim["claims"]["lean_parity_established"] = True
        mutations.append(claim)

        credit = self.authority()
        credit["credits"]["parity_credit"] = 1
        mutations.append(credit)

        for authority in mutations:
            with self.subTest(authority=authority["record_sha256"]):
                self.assert_rejected(authority)

    def test_direct_check_command_passes_without_execution_surface(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(Path(GEN.__file__).resolve()), "--check"],
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr.decode())
        self.assertIn(b"outcomes=0|pairs=0|parity=0", completed.stdout)
        self.assertNotIn(b"run-m0", completed.stdout)


if __name__ == "__main__":
    unittest.main()
