from __future__ import annotations

import copy
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).parents[1]


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


COMPARATOR = load(
    "compare_glaurung_shard_repetitions",
    "compare-glaurung-shard-repetitions.py",
)
SUMMARIZER = load(
    "summarize_glaurung_shard_repetitions_test",
    "summarize-glaurung-shard-repetitions.py",
)


def composite(revision: str, axeyum: float, z3: float, rss: int) -> dict:
    stages = {
        "word_preprocess_s": axeyum * 0.1,
        "bit_blast_s": axeyum * 0.2,
        "cnf_encode_s": axeyum * 0.2,
        "cnf_inprocess_s": 0.0,
        "solve_s": axeyum * 0.3,
        "model_lift_s": axeyum * 0.1,
        "model_replay_s": axeyum * 0.1,
    }
    rewrite = {
        "applications": 3,
        "changed_instances": 2,
        "decision_changes": 0,
        "decision_matches": 2,
        "sat_unsat_conflicts": 0,
    }
    construction = {
        "aig_nodes_created": 11,
        "cnf_clauses_emitted": 13,
        "cnf_variables": 7,
    }
    config = {
        "jobs": 1,
        "experiment": {
            "environment_hash": "environment",
            "source": {"dirty": False, "revision": revision},
        },
    }
    return {
        "schema": "axeyum-glaurung-qfbv-sharded-summary-v1",
        "source_artifact_version": 32,
        "policy": "canonical",
        "contract": {"coverage": "exact"},
        "capture": {"files": 2, "path_set_sha256": "paths", "shards": 1},
        "identity": {
            "source_revision": revision,
            "dirty": "false",
            "reproducible": "true",
            "normalized_config_sha256": f"config-{revision}",
            "environment_hash": "environment",
        },
        "normalized_config": config,
        "shards": [
            {
                "index": 0,
                "tier": "full-shard-00-of-01",
                "files": 2,
                "manifest_sha256": "manifest",
                "capture_index_sha256": "capture",
                "sat": 1,
                "unsat": 1,
                "rewrite": rewrite,
                "construction": construction,
                "exit_status": 0,
            }
        ],
        "aggregate": {
            "publication_ready": True,
            "files": 2,
            "sat": 1,
            "unsat": 1,
            "axeyum_total_s": axeyum,
            "z3_total_s": z3,
            "axeyum_over_z3_ratio": axeyum / z3,
            "maximum_resident_set_kib": rss,
            "stages": stages,
            "rewrite": rewrite,
            "construction": construction,
        },
    }


class ShardComparisonTests(unittest.TestCase):
    def write_composite(self, path: Path, value: dict) -> Path:
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def make_repetitions(
        self, root: Path, name: str, revision: str, axeyum: float, z3: float, rss: int
    ) -> Path:
        directory = root / name
        directory.mkdir()
        paths = [
            self.write_composite(
                directory / f"composite-{index}.json",
                composite(revision, axeyum + offset, z3, rss),
            )
            for index, offset in enumerate((-0.01, 0.01), start=1)
        ]
        summary = SUMMARIZER.summarize(paths)
        path = directory / "repetitions.json"
        path.write_text(json.dumps(summary), encoding="utf-8")
        return path

    def test_compares_clean_revisions_and_applies_gates(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = self.make_repetitions(root, "base", "a" * 40, 1.0, 2.0, 1000)
            candidate = self.make_repetitions(root, "candidate", "b" * 40, 0.9, 2.0, 900)
            result = COMPARATOR.compare(
                baseline,
                candidate,
                max_ratio_regression_percent=3,
                max_axeyum_regression_percent=3,
                max_rss_regression_percent=5,
                max_z3_drift_percent=2,
            )
            self.assertTrue(result["gate"]["passed"])
            self.assertEqual(result["metrics"]["axeyum_total_s"]["direction"], "improvement")

    def test_rejects_capture_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = self.make_repetitions(root, "base", "a" * 40, 1.0, 2.0, 1000)
            candidate = self.make_repetitions(root, "candidate", "b" * 40, 1.0, 2.0, 1000)
            value = json.loads(candidate.read_text())
            source_path = Path(value["runs"][0]["summary"])
            source = json.loads(source_path.read_text())
            source["capture"]["path_set_sha256"] = "different"
            source_path.write_text(json.dumps(source), encoding="utf-8")
            # Rebuild a valid candidate repetition summary with internally
            # consistent but baseline-incompatible capture identity.
            sources = [Path(run["summary"]) for run in value["runs"]]
            other = json.loads(sources[1].read_text())
            other["capture"]["path_set_sha256"] = "different"
            sources[1].write_text(json.dumps(other), encoding="utf-8")
            candidate.write_text(json.dumps(SUMMARIZER.summarize(sources)), encoding="utf-8")
            with self.assertRaisesRegex(COMPARATOR.ComparisonError, "corpus, environment"):
                COMPARATOR.compare(baseline, candidate)

    def test_reports_threshold_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            baseline = self.make_repetitions(root, "base", "a" * 40, 1.0, 2.0, 1000)
            candidate = self.make_repetitions(root, "candidate", "b" * 40, 1.1, 2.0, 1100)
            result = COMPARATOR.compare(
                baseline,
                candidate,
                max_ratio_regression_percent=3,
                max_axeyum_regression_percent=3,
                max_rss_regression_percent=5,
                max_z3_drift_percent=2,
            )
            self.assertFalse(result["gate"]["passed"])


if __name__ == "__main__":
    unittest.main()
