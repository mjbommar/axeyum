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
            "parity_overlap": {
                "profile_complete": True,
                "duplicate_clauses": 0,
                "duplicate_canonical_literals": 0,
                "lengths": {
                    "empty": {"clauses": 0, "literals": 0},
                    "unit": {"clauses": 0, "literals": 0},
                    "binary": {"clauses": 0, "literals": 0},
                    "ternary": {"clauses": 0, "literals": 0},
                    "larger": {"clauses": 0, "literals": 0},
                },
                "rows": [],
                "invariants": {
                    name: True for name in MODULE.PARITY_INVARIANTS
                },
            },
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
        "storage": {
            "formula_clauses": 2,
            "formula_literals": 4,
            "clause_end_logical_bytes": 8,
            "literal_logical_bytes": 32,
            "arena_logical_bytes": 40,
            "arena_capacity_bytes": 48,
            "legacy_logical_lower_bound_bytes": 80,
            "invariants": {
                name: True for name in MODULE.STORAGE_INVARIANTS
            },
            "invariants_hold": True,
            "logical_ratio_at_most_80_percent": True,
        },
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
    aggregate_storage = aggregate["storage"]
    for name in MODULE.STORAGE_FIELDS:
        aggregate_storage[name] *= 2
    del aggregate_storage["invariants"]
    del aggregate_storage["invariants_hold"]
    del aggregate_storage["logical_ratio_at_most_80_percent"]
    aggregate_storage["invariant_instances"] = 2
    aggregate_storage["logical_ratio_at_most_80_percent_instances"] = 2
    aggregate_storage["all_invariants_hold"] = True
    aggregate_storage["all_logical_ratios_at_most_80_percent"] = True
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
        "version": 38,
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


def legacy_artifact(value: dict | None = None) -> dict:
    value = artifact() if value is None else value
    value["version"] = 36
    profiles = [
        instance["layer_attribution"]["construction"]["cnf"]["detailed_profile"]
        for instance in value["instances"]
    ]
    profiles.append(
        value["summary"]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]
    )
    for current in profiles:
        del current["duplicate_origins"]["parity_overlap"]
    for instance in value["instances"]:
        del instance["layer_attribution"]["construction"]["cnf"]["storage"]
    del value["summary"]["layer_attribution"]["construction"]["cnf"]["storage"]
    return value


def v37_artifact() -> dict:
    value = artifact()
    value["version"] = 37
    for instance in value["instances"]:
        del instance["layer_attribution"]["construction"]["cnf"]["storage"]
    del value["summary"]["layer_attribution"]["construction"]["cnf"]["storage"]
    return value


def parity_artifact() -> dict:
    value = artifact()
    profiles = [
        instance["layer_attribution"]["construction"]["cnf"]["detailed_profile"]
        for instance in value["instances"]
    ]
    profiles.append(
        value["summary"]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]
    )
    for index, current in enumerate(profiles):
        multiplier = 2 if index == 2 else 1
        origin = current["duplicate_origins"]
        origin["rows"][0]["first_origin"] = "root/and_tree/forward/parity"
        origin["rows"][0]["duplicate_origin"] = "root/and_tree/forward/parity"
        origin["duplicate_canonical_literals"] = multiplier * 2
        origin["lengths"]["unit"] = {"clauses": 0, "literals": 0}
        origin["lengths"]["binary"] = {
            "clauses": multiplier,
            "literals": multiplier * 2,
        }
        origin["rows"][0]["duplicate_canonical_literals"] = multiplier * 2
        origin["rows"][0]["lengths"]["unit"] = {
            "clauses": 0,
            "literals": 0,
        }
        origin["rows"][0]["lengths"]["binary"] = {
            "clauses": multiplier,
            "literals": multiplier * 2,
        }
        overlap = origin["parity_overlap"]
        overlap["duplicate_clauses"] = multiplier
        overlap["duplicate_canonical_literals"] = multiplier * 2
        overlap["lengths"]["binary"] = {
            "clauses": multiplier,
            "literals": multiplier * 2,
        }
        overlap["rows"] = [
            {
                "relation": "within_leaf",
                "first_shape": "a2-f0-t0-d1-r1-x0",
                "duplicate_shape": "a2-f0-t0-d1-r1-x0",
                "duplicate_clauses": multiplier,
                "duplicate_canonical_literals": multiplier * 2,
                "lengths": {
                    "empty": {"clauses": 0, "literals": 0},
                    "unit": {"clauses": 0, "literals": 0},
                    "binary": {
                        "clauses": multiplier,
                        "literals": multiplier * 2,
                    },
                    "ternary": {"clauses": 0, "literals": 0},
                    "larger": {"clauses": 0, "literals": 0},
                },
            }
        ]
    return value


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
        self.assertTrue(report["storage"]["available"])
        self.assertEqual(report["storage"]["formula_clauses"], 4)
        self.assertEqual(report["storage"]["formula_literals"], 8)
        self.assertEqual(report["storage"]["logical_ratio"], 0.5)
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

    def test_accepts_legacy_v36_without_parity_overlap(self) -> None:
        report = MODULE.analyze_artifact(legacy_artifact())

        self.assertEqual(report["artifact"]["version"], 36)
        self.assertFalse(report["duplicate_origins"]["parity_overlap"]["available"])
        self.assertFalse(report["storage"]["available"])

    def test_accepts_v37_without_flat_storage(self) -> None:
        report = MODULE.analyze_artifact(v37_artifact())

        self.assertEqual(report["artifact"]["version"], 37)
        self.assertFalse(report["storage"]["available"])

    def test_require_flat_storage_rejects_legacy_artifact(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "version 38"):
            MODULE.analyze_artifact(v37_artifact(), require_flat_storage=True)

    def test_rejects_flat_storage_accounting_ratio_and_invariants(self) -> None:
        accounting = artifact()
        accounting["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "storage"
        ]["formula_clauses"] += 1
        with self.assertRaisesRegex(RuntimeError, "formula-clause count"):
            MODULE.analyze_artifact(accounting)

        ratio = artifact()
        ratio["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "storage"
        ]["logical_ratio_at_most_80_percent"] = False
        with self.assertRaisesRegex(RuntimeError, "80-percent"):
            MODULE.analyze_artifact(ratio)

        invariant = artifact()
        invariant["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "storage"
        ]["invariants"]["clause_ends_monotone"] = False
        with self.assertRaisesRegex(RuntimeError, "failed invariant"):
            MODULE.analyze_artifact(invariant)

        summary = artifact()
        summary["summary"]["layer_attribution"]["construction"]["cnf"]["storage"][
            "invariant_instances"
        ] = 1
        with self.assertRaisesRegex(RuntimeError, "population is incomplete"):
            MODULE.analyze_artifact(summary)

    def test_accepts_exact_legacy_baseline_and_rejects_drift(self) -> None:
        value = parity_artifact()
        baseline = MODULE.analyze_artifact(legacy_artifact(parity_artifact()))
        baseline["schema"] = "axeyum.cnf-construction-profile-analysis.v2"

        report = MODULE.analyze_artifact(
            value,
            expected_same_owner_parity_duplicates=2,
            expected_baseline_analysis=baseline,
        )
        self.assertTrue(report["accepted"])

        baseline["aggregate"]["clause_attempts"] += 1
        with self.assertRaisesRegex(RuntimeError, "construction aggregate drift"):
            MODULE.analyze_artifact(
                parity_artifact(), expected_baseline_analysis=baseline
            )

    def test_rejects_failed_instance_invariant(self) -> None:
        value = artifact()
        value["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["invariants"]["duplicates_partition"] = False
        with self.assertRaisesRegex(RuntimeError, "failed invariant"):
            MODULE.analyze_artifact(value)

    def test_rejects_v37_without_parity_overlap(self) -> None:
        value = v37_artifact()
        del value["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["parity_overlap"]
        with self.assertRaisesRegex(RuntimeError, "parity-overlap"):
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

    def test_accepts_and_decodes_parity_overlap_shapes(self) -> None:
        report = MODULE.analyze_artifact(
            parity_artifact(), expected_same_owner_parity_duplicates=2
        )
        overlap = report["duplicate_origins"]["parity_overlap"]
        self.assertEqual(overlap["duplicate_clauses"], 2)
        self.assertEqual(overlap["rows"][0]["relation"], "within_leaf")
        self.assertEqual(overlap["rows"][0]["first_shape"]["raw_arity"], 2)
        self.assertEqual(
            overlap["rows"][0]["first_shape"]["repeated_literal_pairs"], 1
        )

    def test_rejects_parity_relation_shape_and_summary_drift(self) -> None:
        bad_relation = parity_artifact()
        bad_relation["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["parity_overlap"]["rows"][0]["relation"] = "same"
        with self.assertRaisesRegex(RuntimeError, "relation"):
            MODULE.analyze_artifact(bad_relation)

        bad_shape = parity_artifact()
        bad_shape["instances"][0]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["parity_overlap"]["rows"][0][
            "first_shape"
        ] = "a3-f2-t2-d0-r0-x0"
        with self.assertRaisesRegex(RuntimeError, "constants exceed arity"):
            MODULE.analyze_artifact(bad_shape)

        summary_drift = parity_artifact()
        summary_drift["summary"]["layer_attribution"]["construction"]["cnf"][
            "detailed_profile"
        ]["duplicate_origins"]["parity_overlap"]["rows"][0][
            "duplicate_clauses"
        ] = 1
        with self.assertRaisesRegex(RuntimeError, "parity-overlap"):
            MODULE.analyze_artifact(summary_drift)


if __name__ == "__main__":
    unittest.main()
