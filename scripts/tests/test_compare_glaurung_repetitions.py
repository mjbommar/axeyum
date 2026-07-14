from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "compare-glaurung-repetitions.py"
SPEC = importlib.util.spec_from_file_location("compare_glaurung_repetitions", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

BASELINE_REVISION = "1" * 40
CANDIDATE_REVISION = "2" * 40
ENVIRONMENT_HASH = "sha256:" + "3" * 64
MANIFEST_HASH = "sha256:" + "4" * 64


def source_artifact(
    revision: str,
    axeyum_seconds: float,
    z3_seconds: float,
    *,
    environment_hash: str = ENVIRONMENT_HASH,
) -> dict:
    stages = {
        "word_preprocess_s": axeyum_seconds * 0.1,
        "bit_blast_s": axeyum_seconds * 0.2,
        "cnf_encode_s": axeyum_seconds * 0.2,
        "cnf_inprocess_s": 0.0,
        "solve_s": axeyum_seconds * 0.4,
        "model_lift_s": axeyum_seconds * 0.05,
        "model_replay_s": axeyum_seconds * 0.05,
    }
    config = {
        "backend": "axeyum-sat-bv rustsat-batsat",
        "backend_kind": "sat-bv",
        "compare_backend": "z3 4.13.3.0",
        "compare_z3": True,
        "config_hash": "config-hash",
        "corpus_hash": "corpus-hash",
        "corpus_manifest": {
            "content_hash": MANIFEST_HASH,
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
            "environment_hash": environment_hash,
            "source": {"dirty": False, "revision": revision},
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
        "logic": "QF_BV",
        "min_decided_percent": 100.0,
        "preprocess": True,
        "prove_unsat": False,
        "require_in_process_z3": True,
        "require_reproducible_run": True,
        "require_deterministic_resources": True,
    }
    return {
        "version": 22,
        "config": config,
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


def write_repetition_summary(
    root: Path,
    name: str,
    revision: str,
    axeyum_values: list[float],
    z3_values: list[float],
    *,
    environment_hash: str = ENVIRONMENT_HASH,
) -> Path:
    directory = root / name
    directory.mkdir()
    artifacts = []
    for index, (axeyum, z3) in enumerate(
        zip(axeyum_values, z3_values, strict=True), start=1
    ):
        path = directory / f"run-{index:03}.json"
        path.write_text(
            json.dumps(
                source_artifact(
                    revision,
                    axeyum,
                    z3,
                    environment_hash=environment_hash,
                )
            ),
            encoding="utf-8",
        )
        artifacts.append(path)
    summary = MODULE.SUMMARIZER.summarize(artifacts)
    summary_path = directory / "summary.json"
    summary_path.write_text(json.dumps(summary), encoding="utf-8")
    return summary_path


class RepetitionComparisonTests(unittest.TestCase):
    def comparable_pair(self, root: Path) -> tuple[Path, Path]:
        baseline = write_repetition_summary(
            root,
            "baseline",
            BASELINE_REVISION,
            [1.0, 1.2, 0.8],
            [0.5, 0.6, 0.4],
        )
        candidate = write_repetition_summary(
            root,
            "candidate",
            CANDIDATE_REVISION,
            [0.9, 1.08, 0.72],
            [0.5, 0.6, 0.4],
        )
        return baseline, candidate

    def test_compares_distinct_commits_and_reports_raw_controls(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            baseline, candidate = self.comparable_pair(Path(directory))
            result = MODULE.compare(baseline, candidate)
            self.assertEqual(result["baseline"]["source_revision"], BASELINE_REVISION)
            self.assertEqual(result["candidate"]["source_revision"], CANDIDATE_REVISION)
            self.assertAlmostEqual(
                result["metrics"]["axeyum_total_s"]["candidate_minus_baseline_percent"],
                -10.0,
            )
            self.assertAlmostEqual(
                result["metrics"]["z3_total_s"]["candidate_minus_baseline_percent"],
                0.0,
            )
            self.assertAlmostEqual(
                result["metrics"]["axeyum_over_z3_ratio"][
                    "candidate_minus_baseline_percent"
                ],
                -10.0,
            )
            self.assertTrue(result["gate"]["passed"])
            self.assertFalse(result["gate"]["configured"])

    def test_rejects_same_revision_and_environment_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = write_repetition_summary(
                root, "baseline", BASELINE_REVISION, [1.0, 1.2], [0.5, 0.6]
            )
            same_revision = write_repetition_summary(
                root, "same", BASELINE_REVISION, [0.9, 1.08], [0.5, 0.6]
            )
            with self.assertRaisesRegex(
                MODULE.ComparisonError, "different clean source"
            ):
                MODULE.compare(baseline, same_revision)

            drifted = write_repetition_summary(
                root,
                "drifted",
                CANDIDATE_REVISION,
                [0.9, 1.08],
                [0.5, 0.6],
                environment_hash="sha256:" + "5" * 64,
            )
            with self.assertRaisesRegex(MODULE.ComparisonError, "differ beyond"):
                MODULE.compare(baseline, drifted)

    def test_rejects_tampered_summary_or_missing_source_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline, candidate = self.comparable_pair(root)
            value = json.loads(candidate.read_text(encoding="utf-8"))
            value["variance"]["axeyum_total_s"]["mean"] = 999.0
            candidate.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                MODULE.ComparisonError, "does not match its source"
            ):
                MODULE.compare(baseline, candidate)

            candidate = write_repetition_summary(
                root,
                "missing",
                CANDIDATE_REVISION,
                [0.9, 1.08],
                [0.5, 0.6],
            )
            (candidate.parent / "run-001.json").unlink()
            with self.assertRaisesRegex(
                MODULE.ComparisonError, "source artifact validation"
            ):
                MODULE.compare(baseline, candidate)

    def test_explicit_ratio_gate_fails_regression(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = write_repetition_summary(
                root, "baseline", BASELINE_REVISION, [1.0, 1.1], [0.5, 0.55]
            )
            candidate = write_repetition_summary(
                root, "candidate", CANDIDATE_REVISION, [1.2, 1.32], [0.5, 0.55]
            )
            result = MODULE.compare(
                baseline, candidate, max_ratio_regression_percent=5.0
            )
            self.assertTrue(result["gate"]["configured"])
            self.assertFalse(result["gate"]["passed"])
            self.assertAlmostEqual(
                result["gate"]["checks"][0]["observed_percent"], 20.0
            )


if __name__ == "__main__":
    unittest.main()
