import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-cnf-construction-profile.py"
SPEC = importlib.util.spec_from_file_location("analyze_cnf_construction_profile", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def profile() -> dict:
    return {
        "profile_complete": True,
        "declared_clause_literals": 5,
        "visited_clause_literals": 5,
        "false_constants_dropped": 0,
        "repeated_literals_dropped": 0,
        "tautologies": {"true_constant": 0, "complementary_literal": 0},
        "canonical_literals": 5,
        "canonical_clause_lengths": {
            "empty": 0,
            "unit": 1,
            "binary": 2,
            "ternary": 0,
            "larger": 0,
        },
        "primary_vacant_probes": 2,
        "primary_occupied_probes": 1,
        "primary_exact_duplicates": 1,
        "collision_bucket_comparisons": 0,
        "collision_exact_duplicates": 0,
        "collision_inserts": 0,
        "duplicate_origins": {
            "profile_complete": True,
            "duplicate_clauses": 1,
            "duplicate_canonical_literals": 1,
            "lengths": {
                "empty": {"clauses": 0, "literals": 0},
                "unit": {"clauses": 1, "literals": 1},
                "binary": {"clauses": 0, "literals": 0},
                "ternary": {"clauses": 0, "literals": 0},
                "larger": {"clauses": 0, "literals": 0},
            },
            "rows": [
                {
                    "first_origin": "root/root/assertion/unit",
                    "duplicate_origin": "root/root/assertion/unit",
                    "owner_relation": "same",
                    "duplicate_clauses": 1,
                    "duplicate_canonical_literals": 1,
                    "lengths": {
                        "empty": {"clauses": 0, "literals": 0},
                        "unit": {"clauses": 1, "literals": 1},
                        "binary": {"clauses": 0, "literals": 0},
                        "ternary": {"clauses": 0, "literals": 0},
                        "larger": {"clauses": 0, "literals": 0},
                    },
                }
            ],
            "invariants": {
                name: True for name in MODULE.ORIGIN_INVARIANTS
            },
        },
        "invariants": {name: True for name in MODULE.INVARIANTS},
    }


def cnf() -> dict:
    return {
        "clause_attempts": 3,
        "tautological_clauses_skipped": 0,
        "duplicate_clauses_skipped": 1,
        "clauses_emitted": 2,
        "detailed_profile": profile(),
    }


def artifact() -> dict:
    instances = []
    for family, outcome in (("arithmetic", "sat"), ("slice-partial", "unsat")):
        instances.append(
            {
                "outcome": outcome,
                "corpus_manifest": {"family": family, "decision_agrees": True},
                "layer_attribution": {"construction": {"cnf": cnf()}},
            }
        )
    aggregate = cnf()
    aggregate["clause_attempts"] *= 2
    aggregate["duplicate_clauses_skipped"] *= 2
    aggregate["clauses_emitted"] *= 2
    aggregate_profile = aggregate["detailed_profile"]
    for path in MODULE.COUNTER_PATHS.values():
        if path[0] != "detailed_profile":
            continue
        current = aggregate
        for key in path[:-1]:
            current = current[key]
        current[path[-1]] *= 2
    aggregate_profile["profiled_instances"] = 2
    aggregate_profile["instances"] = 2
    aggregate_origins = aggregate_profile["duplicate_origins"]
    aggregate_origins["duplicate_clauses"] = 2
    aggregate_origins["duplicate_canonical_literals"] = 2
    aggregate_origins["lengths"]["unit"] = {"clauses": 2, "literals": 2}
    aggregate_origins["rows"][0]["duplicate_clauses"] = 2
    aggregate_origins["rows"][0]["duplicate_canonical_literals"] = 2
    aggregate_origins["rows"][0]["lengths"]["unit"] = {
        "clauses": 2,
        "literals": 2,
    }
    aggregate_origins["profiled_instances"] = 2
    aggregate_origins["instances"] = 2
    return {
        "version": 36,
        "config": {
            "backend_kind": "sat-bv",
            "profile_cnf_construction": True,
            "jobs": 1,
            "corpus_hash": "corpus",
            "config_hash": "config",
            "corpus_manifest": {"content_hash": "sha256:abcd"},
        },
        "summary": {
            "files": 2,
            "sat": 1,
            "unsat": 1,
            "unknown": 0,
            "unsupported": 0,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "manifest": {"compared": 2, "agree": 2, "disagree": 0},
            "oracle": {"compared": 2, "agree": 2, "disagree": 0, "skipped": 0},
            "layer_attribution": {
                "instances": 2,
                "model_replay_instances": 1,
                "construction": {"cnf": aggregate},
            },
        },
        "instances": instances,
    }


class CnfConstructionProfileAnalysisTests(unittest.TestCase):
    def test_accepts_exact_population_and_family_partitions(self) -> None:
        report = MODULE.analyze_artifact(
            artifact(),
            expected_files=2,
            expected_sat=1,
            expected_unsat=1,
            expected_manifest_sha256="abcd",
            expected_families={"arithmetic": 1, "slice-partial": 1},
        )
        self.assertTrue(report["accepted"])
        self.assertEqual(report["aggregate"]["clause_attempts"], 6)
        self.assertEqual(report["families"]["arithmetic"]["sat"], 1)
        self.assertEqual(report["families"]["slice-partial"]["unsat"], 1)
        origins = report["duplicate_origins"]
        self.assertEqual(origins["duplicate_clauses"], 2)
        self.assertEqual(origins["rows"][0]["participating_instances"], 2)
        self.assertEqual(origins["rows"][0]["largest_instance_share"], 0.5)
        self.assertEqual(
            origins["rows"][0]["families"]["arithmetic"]["sat"], 1
        )
        self.assertEqual(
            origins["rows"][0]["families"]["slice-partial"]["unsat"], 1
        )

    def test_rejects_failed_instance_invariant(self) -> None:
        value = artifact()
        value["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["invariants"]["duplicates_partition"] = False
        with self.assertRaisesRegex(RuntimeError, "failed invariant"):
            MODULE.analyze_artifact(value)

    def test_rejects_aggregate_that_does_not_resum_instances(self) -> None:
        value = artifact()
        value["summary"]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["canonical_literals"] += 1
        with self.assertRaisesRegex(RuntimeError, "do not equal per-instance sums"):
            MODULE.analyze_artifact(value)

    def test_rejects_duplicate_origin_owner_and_literal_drift(self) -> None:
        owner_drift = artifact()
        owner_drift["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["rows"][0]["owner_relation"] = "unknown"
        with self.assertRaisesRegex(RuntimeError, "owner relation"):
            MODULE.analyze_artifact(owner_drift)

        literal_drift = artifact()
        literal_drift["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["rows"][0]["duplicate_canonical_literals"] += 1
        with self.assertRaisesRegex(RuntimeError, "duplicate-origin"):
            MODULE.analyze_artifact(literal_drift)

        matrix_drift = artifact()
        summary_origins = matrix_drift["summary"]["layer_attribution"]["construction"][
            "cnf"
        ]["detailed_profile"]["duplicate_origins"]
        summary_origins["rows"][0]["duplicate_clauses"] = 1
        summary_origins["rows"][0]["duplicate_canonical_literals"] = 1
        summary_origins["rows"][0]["lengths"]["unit"] = {
            "clauses": 1,
            "literals": 1,
        }
        cross = dict(summary_origins["rows"][0])
        cross["owner_relation"] = "cross"
        cross["lengths"] = {
            bucket: dict(values)
            for bucket, values in summary_origins["rows"][0]["lengths"].items()
        }
        summary_origins["rows"].append(cross)
        with self.assertRaisesRegex(RuntimeError, "rows do not equal per-instance sums"):
            MODULE.analyze_artifact(matrix_drift)

    def test_rejects_oracle_skip_and_family_drift(self) -> None:
        skipped = artifact()
        skipped["summary"]["oracle"]["skipped"] = 1
        with self.assertRaisesRegex(RuntimeError, "skipped"):
            MODULE.analyze_artifact(skipped)

        with self.assertRaisesRegex(RuntimeError, "family-count gate"):
            MODULE.analyze_artifact(
                artifact(),
                expected_families={"arithmetic": 2},
            )


if __name__ == "__main__":
    unittest.main()
