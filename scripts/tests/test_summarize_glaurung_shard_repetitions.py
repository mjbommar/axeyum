from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "summarize-glaurung-shard-repetitions.py"
SPEC = importlib.util.spec_from_file_location(
    "summarize_glaurung_shard_repetitions", SCRIPT
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def summary(axeyum: float, z3: float, rss: int) -> dict:
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
    shard = {
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
        "axeyum_total_s": axeyum,
        "z3_total_s": z3,
        "maximum_resident_set_kib": rss,
    }
    return {
        "schema": "axeyum-glaurung-qfbv-sharded-summary-v1",
        "source_artifact_version": 33,
        "policy": "canonical",
        "contract": {"coverage": "exact"},
        "capture": {"files": 2, "path_set_sha256": "paths", "shards": 1},
        "identity": {"source_revision": "revision", "dirty": "false"},
        "normalized_config": {"jobs": 1},
        "shards": [shard],
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


class ShardRepetitionTests(unittest.TestCase):
    def write(self, root: Path, name: str, value: dict) -> Path:
        path = root / name
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def test_reports_complete_composite_variance(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = [
                self.write(root, "run-1.json", summary(1.0, 2.0, 1000)),
                self.write(root, "run-2.json", summary(1.2, 2.0, 1200)),
            ]
            result = MODULE.summarize(paths)
            self.assertEqual(result["repetitions"], 2)
            self.assertAlmostEqual(result["variance"]["axeyum_total_s"]["mean"], 1.1)
            self.assertAlmostEqual(
                result["variance"]["axeyum_total_s"]["sample_standard_deviation"],
                2**0.5 / 10,
            )
            self.assertEqual(result["variance"]["maximum_resident_set_kib"]["p95"], 1200)

    def test_rejects_deterministic_work_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = self.write(root, "run-1.json", summary(1.0, 2.0, 1000))
            changed = summary(1.0, 2.0, 1000)
            changed["aggregate"]["construction"]["cnf_clauses_emitted"] += 1
            second = self.write(root, "run-2.json", changed)
            with self.assertRaisesRegex(MODULE.SummaryError, "deterministic work"):
                MODULE.summarize([first, second])

    def test_rejects_non_publishable_or_single_summary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            value = summary(1.0, 2.0, 1000)
            value["aggregate"]["publication_ready"] = False
            path = self.write(root, "run.json", value)
            with self.assertRaisesRegex(MODULE.SummaryError, "at least two"):
                MODULE.summarize([path])
            second = self.write(root, "run-2.json", value)
            with self.assertRaisesRegex(MODULE.SummaryError, "publication_ready"):
                MODULE.summarize([path, second])


if __name__ == "__main__":
    unittest.main()
