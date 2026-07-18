import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-qfbv-faithfulness.py"
SPEC = importlib.util.spec_from_file_location("analyze_qfbv_faithfulness", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def row(path: str, outcome: str, family: str) -> dict:
    unsat = outcome == "unsat"
    return {
        "file": f"/capture/{path}",
        "outcome": outcome,
        "corpus_manifest": {
            "path": path,
            "content_hash": f"sha256:{path[:1] * 64}",
            "expected": outcome,
            "family": family,
            "decision_compared": True,
            "decision_agrees": True,
        },
        "oracle": {
            "outcome": outcome,
            "decision_compared": True,
            "decision_agrees": True,
        },
        "unsat_proof_replay": "checked" if unsat else "not-applicable",
        "end_to_end_unsat": {
            "status": "certified" if unsat else "not-applicable",
        },
    }


def artifact() -> dict:
    return {
        "version": 33,
        "config": {
            "backend_kind": "sat-bv",
            "logic": "QF_BV",
            "jobs": 1,
            "manifest_validation_jobs": 1,
            "prove_unsat": True,
            "certify_end_to_end_unsat": True,
            "end_to_end_deadline_ms": 1000,
            "compare_z3": True,
            "require_in_process_z3": True,
            "require_reproducible_run": True,
            "require_deterministic_resources": True,
            "preprocess": False,
            "demand_bit_slicing": False,
            "range_demand_slicing": False,
            "cnf_inprocessing": False,
            "cnf_vivify": False,
            "native_cdcl": False,
            "rewrite": {"mode": "off"},
            "query_plan": {"mode": "full"},
            "config_hash": "cfg",
            "experiment": {
                "environment_hash": "sha256:environment",
                "source": {"dirty": False, "revision": "revision"},
            },
            "corpus_manifest": {
                "content_hash": "sha256:manifest",
                "name": "manifest-v1",
                "selected_entries": 2,
                "selected_tier": "representative",
            },
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
            "manifest": {"expected": 2, "compared": 2, "agree": 2, "disagree": 0},
            "oracle": {"compared": 2, "agree": 2, "disagree": 0, "skipped": 0},
            "unsat_proof_replay": {"requested": True, "checked": 1, "missing": 0},
            "end_to_end_unsat": {
                "requested": True,
                "deadline_ms": 1000,
                "attempted": 1,
                "certified": 1,
                "not_certified": 0,
                "satisfiable_contradictions": 0,
                "recheck_failures": 0,
                "errors": 0,
                "attempted_partitioned": True,
                "elapsed": {
                    "min_ms": 1.0,
                    "p50_ms": 1.0,
                    "mean_ms": 1.0,
                    "p95_ms": 1.0,
                    "max_ms": 1.0,
                },
            },
        },
        "instances": [
            row("queries/a.smt2", "unsat", "arithmetic"),
            row("queries/b.smt2", "sat", "comparison"),
        ],
    }


class FaithfulnessAnalysisTests(unittest.TestCase):
    def write(self, root: Path, name: str, value: dict) -> Path:
        path = root / name
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def test_accepts_two_identity_matched_complete_runs(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = [
                self.write(root, "run-1.json", artifact()),
                self.write(root, "run-2.json", artifact()),
            ]
            result = MODULE.analyze(paths)
            self.assertEqual(result["coverage"]["certified_per_run"], [1, 1])
            self.assertEqual(result["coverage"]["coverage_percent"], 100.0)
            self.assertEqual(result["population"]["unsat_family_counts"], {"arithmetic": 1})

    def test_rejects_missing_cnf_proof(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bad = artifact()
            bad["summary"]["unsat_proof_replay"]["checked"] = 0
            paths = [
                self.write(root, "run-1.json", artifact()),
                self.write(root, "run-2.json", bad),
            ]
            with self.assertRaisesRegex(MODULE.AnalysisError, "checked CNF DRAT"):
                MODULE.analyze(paths)

    def test_rejects_per_query_certification_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            drift = artifact()
            drift["summary"]["end_to_end_unsat"]["certified"] = 0
            drift["summary"]["end_to_end_unsat"]["not_certified"] = 1
            drift["instances"][0]["end_to_end_unsat"]["status"] = "not-certified"
            paths = [
                self.write(root, "run-1.json", artifact()),
                self.write(root, "run-2.json", drift),
            ]
            with self.assertRaisesRegex(MODULE.AnalysisError, "certification drift"):
                MODULE.analyze(paths)

    def test_rejects_empty_unsat_denominator(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            empty = artifact()
            empty["summary"]["sat"] = 2
            empty["summary"]["unsat"] = 0
            empty["summary"]["unsat_proof_replay"]["checked"] = 0
            empty["summary"]["end_to_end_unsat"]["attempted"] = 0
            empty["summary"]["end_to_end_unsat"]["certified"] = 0
            empty["instances"] = [
                row("queries/a.smt2", "sat", "arithmetic"),
                row("queries/b.smt2", "sat", "comparison"),
            ]
            paths = [
                self.write(root, "run-1.json", empty),
                self.write(root, "run-2.json", empty),
            ]
            with self.assertRaisesRegex(MODULE.AnalysisError, "must be nonempty"):
                MODULE.analyze(paths)

    def test_rejects_unordered_elapsed_distribution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bad = artifact()
            bad["summary"]["end_to_end_unsat"]["elapsed"]["p95_ms"] = 0.5
            paths = [
                self.write(root, "run-1.json", artifact()),
                self.write(root, "run-2.json", bad),
            ]
            with self.assertRaisesRegex(MODULE.AnalysisError, "not ordered"):
                MODULE.analyze(paths)


if __name__ == "__main__":
    unittest.main()
