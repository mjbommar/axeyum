from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-qfbv-timeout-sweep.py"
SPEC = importlib.util.spec_from_file_location("analyze_qfbv_timeout_sweep", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


FILES = (("a.smt2", "sat"), ("b.smt2", "unsat"))
TIMEOUTS = (50, 100, 250, 1_000)


def artifact(timeout: int) -> dict:
    instances = []
    for name, expected in FILES:
        oracle = "unknown" if timeout == 50 and name == "b.smt2" else expected
        primary = "unknown" if timeout <= 100 and name == "b.smt2" else expected
        population = MODULE.population(primary, oracle)
        instances.append(
            {
                "file": f"/corpus/{name}",
                "outcome": primary,
                "cold_total_ms": float(timeout) / 10,
                "corpus_manifest": {
                    "path": name,
                    "content_hash": f"sha256:{name[0] * 64}",
                    "expected": expected,
                },
                "oracle": {
                    "backend_kind": "z3",
                    "outcome": oracle,
                    "decision_population": population,
                    "cold_total_ms": float(timeout) / 5,
                },
            }
        )
    populations = {name: 0 for name in MODULE.POPULATIONS}
    for row in instances:
        populations[row["oracle"]["decision_population"]] += 1
    return {
        "version": 32,
        "config": {
            "backend_kind": "sat-bv",
            "logic": "QF_BV",
            "jobs": 1,
            "manifest_validation_jobs": 1,
            "compare_z3": True,
            "require_in_process_z3": True,
            "require_reproducible_run": True,
            "rewrite": {"mode": "off"},
            "timeout_ms": timeout,
            "config_hash": f"cfg-{timeout}",
            "resources": {"wall_clock_safety_timeout_ms": timeout},
            "corpus_manifest": {
                "content_hash": "sha256:manifest",
                "selected_entries": 2,
            },
            "experiment": {
                "environment_hash": "sha256:env",
                "source": {"dirty": False, "revision": "revision"},
            },
        },
        "summary": {
            "files": 2,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "manifest": {"disagree": 0},
            "oracle": {
                "disagree": 0,
                "decision_population": {
                    "both_decided": populations["both-decided"],
                    "axeyum_only_decided": populations["axeyum-only-decided"],
                    "z3_only_decided": populations["z3-only-decided"],
                    "neither_decided": populations["neither-decided"],
                    "accounted": 2,
                },
            },
        },
        "instances": instances,
    }


def cvc5_report() -> dict:
    rows = []
    for repetition in range(5):
        for timeout in TIMEOUTS:
            for name, expected in FILES:
                rows.append(
                    {
                        "timeout_ms": timeout,
                        "repetition": repetition,
                        "path": name,
                        "content_hash": f"sha256:{name[0] * 64}",
                        "expected": expected,
                        "outcome": expected,
                        "elapsed_nanos": 1_000_000,
                    }
                )
    return {
        "schema": MODULE.CVC5_SCHEMA,
        "measured_repetitions": 5,
        "timeouts_ms": list(TIMEOUTS),
        "manifest": {"content_hash": "sha256:manifest", "files": 2},
        "cvc5": {"version": "cvc5 1.3.4"},
        "rows": rows,
    }


class TimeoutSweepTests(unittest.TestCase):
    def write(self, root: Path, name: str, value: dict) -> Path:
        path = root / name
        path.write_text(json.dumps(value), encoding="utf-8")
        return path

    def inputs(self, root: Path) -> tuple[list[Path], Path]:
        artifacts = []
        for timeout in TIMEOUTS:
            for repetition in range(5):
                artifacts.append(
                    self.write(
                        root,
                        f"axeyum-{timeout}-{repetition}.json",
                        artifact(timeout),
                    )
                )
        neutral = self.write(root, "cvc5.json", cvc5_report())
        return artifacts, neutral

    def test_accepts_complete_fixed_work_sweep(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            artifacts, neutral = self.inputs(Path(directory))
            result = MODULE.analyze(artifacts, neutral)
            self.assertEqual(result["cross_solver_sat_unsat_contradictions"], 0)
            self.assertEqual(result["contract"]["repetitions"], 5)
            self.assertEqual(
                result["timeouts"]["250"]["axeyum_z3"]["fixed_both_decided"][
                    "queries"
                ],
                2,
            )
            self.assertEqual(
                result["timeouts"]["50"]["axeyum_z3"]["fixed_both_decided"][
                    "queries"
                ],
                1,
            )

    def test_accepts_current_artifact_v34(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            artifacts, neutral = self.inputs(Path(directory))
            for path in artifacts:
                value = json.loads(path.read_text(encoding="utf-8"))
                value["version"] = 34
                path.write_text(json.dumps(value), encoding="utf-8")
            result = MODULE.analyze(artifacts, neutral)
            self.assertEqual(result["source_artifact_version"], 34)
            self.assertEqual(result["source_artifact_versions"], [34])

    def test_rejects_cross_solver_contradiction(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            artifacts, neutral = self.inputs(Path(directory))
            value = json.loads(neutral.read_text(encoding="utf-8"))
            value["rows"][0]["outcome"] = "unsat"
            neutral.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(MODULE.AnalysisError, "cvc5 disagrees"):
                MODULE.analyze(artifacts, neutral)

    def test_rejects_missing_repetition(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            artifacts, neutral = self.inputs(Path(directory))
            artifacts.pop()
            with self.assertRaisesRegex(MODULE.AnalysisError, "same N>=5"):
                MODULE.analyze(artifacts, neutral)


if __name__ == "__main__":
    unittest.main()
