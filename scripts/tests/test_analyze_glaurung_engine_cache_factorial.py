#!/usr/bin/env python3

import importlib.util
import pathlib
import unittest


SCRIPT = (
    pathlib.Path(__file__).parents[1]
    / "analyze-glaurung-engine-cache-factorial.py"
)
SPEC = importlib.util.spec_from_file_location("engine_cache_factorial_analyzer", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
ANALYZER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ANALYZER)


def report(mode: str = "warm-exact") -> dict:
    policy = "off" if mode.endswith("off") else mode.split("-", 1)[1]
    warm = "adaptive" if mode.startswith("warm") else "off"
    cache_class = "miss" if policy == "off" else "exact-sat"
    backend_called = cache_class == "miss"
    cache = {
        "policy": policy,
        "lookups": 0 if policy == "off" else 1,
        "exact_sat_hits": 0 if policy == "off" else 1,
        "exact_unsat_hits": 0,
        "sat_superset_hits": 0,
        "unsat_subset_hits": 0,
        "misses": 0 if policy != "off" else 0,
        "sat_replay_attempts": 0 if policy == "off" else 1,
        "sat_replay_successes": 0 if policy == "off" else 1,
        "sat_replay_failures": 0,
        "sat_replay_missing_symbols": 0,
        "insertions": 0,
        "evictions": 0,
        "oversize_bypasses": 0,
        "conflicts": 0,
        "entries": 0,
        "assertion_refs": 0,
        "model_values": 0,
        "peak_entries": 0,
        "peak_assertion_refs": 0,
        "peak_model_values": 0,
        "lookup_nanos": 5 if policy != "off" else 0,
        "model_replay_nanos": 5 if policy != "off" else 0,
        "index_update_nanos": 0,
        "eviction_nanos": 0,
    }
    return {
        "schema": ANALYZER.REPORT_SCHEMA,
        "gate": "pass",
        "trace": {"manifest_sha256": "a" * 64, "check_count": 1},
        "bindings": {
            "finding_sha256": "b" * 64,
            "offline_replay_sha256": "c" * 64,
        },
        "implementation": {
            "replay_executable_sha256": "d" * 64,
            "glaurung_replay_revision": "e" * 40,
            "axeyum_source": {"revision": "f" * 40, "tracked_dirty": False},
        },
        "configuration": {
            "factorial_mode": mode,
            "GLAURUNG_ENGINE_CONSTRAINT_CACHE": policy,
            "GLAURUNG_AXEYUM_WARM_REUSE": warm,
            "engine_cache_limits": {
                "max_entries": 4096,
                "max_assertion_refs": 524288,
                "max_model_values": 262144,
                "max_model_values_per_entry": 256,
            },
        },
        "outcomes": {
            "recorded_sat": 1,
            "recorded_unsat": 0,
            "recorded_unknown": 0,
            "recorded_error": 0,
            "actual_sat": 1,
            "actual_unsat": 0,
            "actual_unknown": 0,
            "recovered_decisions": 0,
            "lost_decisions": 0,
            "opposite_decisions": 0,
        },
        "exact_work": {
            "synchronization_mismatches": 0,
            "resets_after_error": 0,
        },
        "ownership": {
            "live_paths": 0,
            "serial_tracked_owners": 0,
            "serial_references": 0,
        },
        "replay_sat_cache": {"replay_failures": 0},
        "engine_constraint_cache": cache,
        "timing": {"actual_axeyum_nanos": 20, "peak_rss_kib": 1024},
        "checks": [
            {
                "index": 0,
                "query_sha256": "0" * 64,
                "recorded_outcome": "sat",
                "assertion_count": 1,
                "owner_id": 7,
                "cache_class": cache_class,
                "backend_called": backend_called,
                "warm_synchronized": False,
                "lookup_nanos": 5 if policy != "off" else 0,
                "model_replay_nanos": 5 if policy != "off" else 0,
                "index_update_nanos": 0,
                "eviction_nanos": 0,
                "backend_miss_nanos": 10 if policy == "off" else 0,
                "wrapper_nanos": 20,
                "stage_slack_nanos": 10,
            }
        ],
    }


def registration() -> dict:
    return {
        "sources": {
            "glaurung": {"revision": "e" * 40},
            "axeyum": {"revision": "f" * 40},
        },
        "executable": {"sha256": "d" * 64},
        "protocol": {
            "cache_limits": {
                "max_entries": 4096,
                "max_assertion_refs": 524288,
                "max_model_values": 262144,
                "max_model_values_per_entry": 256,
            }
        },
    }


class EngineCacheFactorialAnalyzerTests(unittest.TestCase):
    def test_passing_report_enforces_complete_stage_and_binding_contract(self) -> None:
        validated = ANALYZER.validate_report(
            report(),
            pathlib.Path("fixture-report.json"),
            "warm-exact",
            {
                "manifest_sha256": "a" * 64,
                "finding_sha256": "b" * 64,
                "offline_replay_sha256": "c" * 64,
            },
            registration(),
        )
        self.assertEqual(validated["class_counts"]["exact-sat"], 1)
        self.assertEqual(validated["wrapper_nanos"], [20.0])

    def test_cache_hit_that_calls_backend_is_rejected(self) -> None:
        value = report()
        value["checks"][0]["backend_called"] = True
        with self.assertRaisesRegex(ANALYZER.AnalysisError, "hit called backend"):
            ANALYZER.validate_report(
                value,
                pathlib.Path("fixture-report.json"),
                "warm-exact",
                {
                    "manifest_sha256": "a" * 64,
                    "finding_sha256": "b" * 64,
                    "offline_replay_sha256": "c" * 64,
                },
                registration(),
            )

    def test_unbounded_opportunity_classification_drift_is_rejected(self) -> None:
        loaded = {
            "cache": {"evictions": 0, "oversize_bypasses": 0},
            "class_counts": {
                "exact-sat": 0,
                "exact-unsat": 0,
                "sat-superset": 0,
                "unsat-subset": 0,
                "miss": 1,
            },
        }
        expected = {
            "checks": 1,
            "exact_hits": 1,
            "exact_sat_hits": 1,
            "exact_unsat_hits": 0,
            "sat_superset_hits": 0,
            "unsat_subset_hits": 0,
            "misses": 0,
        }
        with self.assertRaisesRegex(ANALYZER.AnalysisError, "differs without"):
            ANALYZER.expected_classification(loaded, expected, "cold-exact")

    def test_paired_ratio_uses_repetition_geomeans_and_fixed_bootstrap(self) -> None:
        numerator = [
            {"wrapper_nanos": [20.0, 40.0], "process_geomean_nanos": 28.284}
            for _ in range(5)
        ]
        denominator = [
            {"wrapper_nanos": [10.0, 20.0], "process_geomean_nanos": 14.142}
            for _ in range(5)
        ]
        summary = ANALYZER.ratio_summary(numerator, denominator, 10_000, 0)
        self.assertAlmostEqual(summary["geometric_mean"], 2.0)
        self.assertAlmostEqual(summary["bootstrap_95_percent_ci"][0], 2.0)
        self.assertAlmostEqual(summary["bootstrap_95_percent_ci"][1], 2.0)
        self.assertEqual(summary["conclusion"], "denominator-faster")


if __name__ == "__main__":
    unittest.main()
