from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "summarize-glaurung-repetitions.py"
SPEC = importlib.util.spec_from_file_location("summarize_glaurung_repetitions", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def artifact(axeyum_seconds: float, z3_seconds: float) -> dict:
    stages = {
        "word_preprocess_s": axeyum_seconds * 0.1,
        "bit_blast_s": axeyum_seconds * 0.2,
        "cnf_encode_s": axeyum_seconds * 0.2,
        "cnf_inprocess_s": 0.0,
        "solve_s": axeyum_seconds * 0.4,
        "model_lift_s": axeyum_seconds * 0.05,
        "model_replay_s": axeyum_seconds * 0.05,
    }
    return {
        "version": 24,
        "config": {
            "backend": "axeyum-sat-bv rustsat-batsat",
            "compare_backend": "z3 4.13.3.0",
            "compare_z3": True,
            "config_hash": "cfg",
            "corpus_hash": "corpus",
            "corpus_manifest": {
                "content_hash": "sha256:manifest",
                "selected_entries": 2,
            },
            "determinism": {
                "profile": "axeyum-bench-fixed-seeds-v1",
                "corpus_order": "stable manifest order (or deterministic lexical path order without a manifest)",
                "sat_bv": {
                    "adapter": "rustsat-batsat",
                    "option_source": "batsat::SolverOpts::default from the Cargo.lock-pinned dependency",
                    "random_seed": 91_648_253.0,
                    "random_var_freq": 0.0,
                    "random_polarity": False,
                    "random_initial_activity": False,
                },
                "z3": {
                    "random_seed": 0,
                    "parameter": "random_seed",
                    "set_explicitly": True,
                },
            },
            "experiment": {
                "environment_hash": "sha256:environment",
                "source": {"dirty": False, "revision": "revision"},
            },
            "jobs": 1,
            "timeout_ms": 10_000,
            "resource_limit": 2_000_000,
            "node_budget": 300_000,
            "cnf_variable_budget": 3_000_000,
            "cnf_clause_budget": 8_000_000,
            "resources": {
                "profile": "axeyum-qfbv-cold-bounded-v1",
                "required": True,
                "limits": {
                    "search": 2_000_000,
                    "dag_nodes": 300_000,
                    "cnf_variables": 3_000_000,
                    "cnf_clauses": 8_000_000,
                },
                "units": {
                    "primary_search": "rustsat-batsat within_budget progress checks",
                    "z3_oracle_search": "Z3 rlimit units",
                    "dag_nodes": "unique reachable term DAG nodes before lowering",
                    "cnf_variables": "variables in the formula submitted to SAT",
                    "cnf_clauses": "clauses in the formula submitted to SAT",
                },
                "wall_clock_safety_timeout_ms": 10_000,
                "wall_clock_is_deterministic": False,
                "cross_backend_numeric_limits_are_work_equivalent": False,
            },
            "require_in_process_z3": True,
            "require_reproducible_run": True,
            "require_deterministic_resources": True,
        },
        "summary": {
            "files": 2,
            "decided": 2,
            "decided_percent": 100.0,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "manifest": {"expected": 2, "compared": 2, "agree": 2, "disagree": 0},
            "oracle": {
                "enabled": True,
                "compared": 2,
                "agree": 2,
                "disagree": 0,
                "skipped": 0,
            },
            "unsat_proof_replay": {"requested": False, "missing": 0},
            "layer_attribution": {
                "instances": 2,
                "total_pipeline_s": axeyum_seconds,
                **stages,
            },
            "client_comparison": {
                "instances": 2,
                "axeyum_total_s": axeyum_seconds,
                "z3_total_s": z3_seconds,
                "axeyum_over_z3_ratio": axeyum_seconds / z3_seconds,
            },
        },
    }


class RepetitionSummaryTests(unittest.TestCase):
    def write_artifact(self, root: Path, name: str, value: dict) -> Path:
        path = root / name
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def test_reports_whole_corpus_sample_variance(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = [
                self.write_artifact(root, "run-001.json", artifact(1.0, 0.5)),
                self.write_artifact(root, "run-002.json", artifact(1.2, 0.5)),
                self.write_artifact(root, "run-003.json", artifact(0.8, 0.5)),
            ]
            result = MODULE.summarize(paths)
            self.assertEqual(result["repetitions"], 3)
            self.assertEqual(
                [run["artifact"] for run in result["runs"]],
                ["run-001.json", "run-002.json", "run-003.json"],
            )
            self.assertAlmostEqual(result["variance"]["axeyum_total_s"]["mean"], 1.0)
            self.assertAlmostEqual(
                result["variance"]["axeyum_total_s"]["sample_standard_deviation"], 0.2
            )
            self.assertEqual(result["variance"]["axeyum_total_s"]["p50"], 1.0)
            self.assertEqual(result["variance"]["axeyum_over_z3_ratio"]["p95"], 2.4)

    def test_rejects_acceptance_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            good = self.write_artifact(root, "run-001.json", artifact(1.0, 0.5))
            bad_value = artifact(1.0, 0.5)
            bad_value["summary"]["oracle"]["disagree"] = 1
            bad = self.write_artifact(root, "run-002.json", bad_value)
            with self.assertRaisesRegex(
                MODULE.SummaryError, "oracle.disagree must be zero"
            ):
                MODULE.summarize([good, bad])

    def test_rejects_identity_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = self.write_artifact(root, "run-001.json", artifact(1.0, 0.5))
            changed = artifact(1.0, 0.5)
            changed["config"]["experiment"]["environment_hash"] = "sha256:other"
            second = self.write_artifact(root, "run-002.json", changed)
            with self.assertRaisesRegex(MODULE.SummaryError, "config differs"):
                MODULE.summarize([first, second])

    def test_rejects_decorative_or_drifting_solver_seed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            changed = artifact(1.0, 0.5)
            changed["config"]["determinism"]["sat_bv"]["random_seed"] = 1.0
            first = self.write_artifact(root, "run-001.json", changed)
            second = self.write_artifact(root, "run-002.json", changed)
            with self.assertRaisesRegex(
                MODULE.SummaryError, "sat_bv.random_seed must be 91648253"
            ):
                MODULE.summarize([first, second])

    def test_rejects_missing_or_decorative_resource_profile(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            changed = artifact(1.0, 0.5)
            changed["config"]["resources"]["limits"]["search"] = 1
            first = self.write_artifact(root, "run-001.json", changed)
            second = self.write_artifact(root, "run-002.json", changed)
            with self.assertRaisesRegex(
                MODULE.SummaryError,
                "limits.search must match config.resource_limit",
            ):
                MODULE.summarize([first, second])

    def test_requires_multiple_unique_trials(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = self.write_artifact(Path(directory), "run.json", artifact(1.0, 0.5))
            with self.assertRaisesRegex(MODULE.SummaryError, "at least two"):
                MODULE.summarize([path])
            with self.assertRaisesRegex(MODULE.SummaryError, "paths must be unique"):
                MODULE.summarize([path, path])

    def test_output_must_share_the_source_artifact_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            inputs = [root / "runs" / "run-001.json", root / "runs" / "run-002.json"]
            with self.assertRaisesRegex(MODULE.SummaryError, "common source-artifact"):
                MODULE.validate_output_location(
                    root / "elsewhere" / "summary.json", inputs
                )
            MODULE.validate_output_location(root / "runs" / "summary.json", inputs)


if __name__ == "__main__":
    unittest.main()
