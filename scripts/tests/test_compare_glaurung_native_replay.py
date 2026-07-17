from __future__ import annotations

import argparse
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "compare-glaurung-native-replay.py"
SPEC = importlib.util.spec_from_file_location("compare_glaurung_native_replay", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def report(candidate: bool, nanos: int = 100_000_000) -> dict:
    continuation = {
        "continuations": 2 if candidate else 0,
        "recoveries": 1 if candidate else 0,
        "unknowns": 1 if candidate else 0,
        "errors": 0,
        "cold_retries": 0,
    }
    return {
        "schema": MODULE.REPORT_SCHEMA,
        "gate": "pass",
        "trace": {"events_sha256": "a" * 64, "check_count": 10},
        "bindings": {"finding_sha256": "b" * 64, "offline_replay_sha256": "c" * 64},
        "implementation": {
            "replay_executable_sha256": "d" * 64,
            "glaurung_replay_revision": "1" * 40,
            "axeyum_source": {"revision": "2" * 40, "tracked_dirty": False},
        },
        "configuration": {"GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE": "1" if candidate else "0"},
        "outcomes": {
            "recorded_sat": 5,
            "recorded_unsat": 4,
            "recorded_unknown": 1,
            "recorded_error": 0,
            "opposite_decisions": 0,
        },
        "exact_work": {
            "synchronization_mismatches": 0,
            "resets_after_error": 0,
            "warm_checks": 10,
        },
        "ownership": {
            "live_paths": 0,
            "serial_tracked_owners": 0,
            "serial_references": 0,
        },
        "replay_sat_cache": {"replay_failures": 0},
        "timeout_continuation": continuation,
        "timing": {"actual_axeyum_nanos": nanos},
    }


class NativeReplayComparisonTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def write_run(self, name: str, value: dict, rss: int = 1000) -> tuple[Path, Path]:
        report_path = self.root / f"{name}.json"
        time_path = self.root / f"{name}.time"
        report_path.write_text(json.dumps(value) + "\n")
        time_path.write_text(
            "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.00\n"
            f"Maximum resident set size (kbytes): {rss}\n"
            "Exit status: 0\n"
        )
        return report_path, time_path

    def arguments(self, controls, candidates) -> argparse.Namespace:
        return argparse.Namespace(
            control_report=[item[0] for item in controls],
            control_time=[item[1] for item in controls],
            candidate_report=[item[0] for item in candidates],
            candidate_time=[item[1] for item in candidates],
            min_repetitions=3,
            max_time_regression_percent=3.0,
            max_rss_regression_percent=5.0,
            max_cv_percent=3.0,
        )

    def test_accepts_repeated_exact_identity_with_bounded_cost(self) -> None:
        controls = [self.write_run(f"control-{i}", report(False)) for i in range(3)]
        candidates = [
            self.write_run(f"candidate-{i}", report(True, 102_000_000), 1040)
            for i in range(3)
        ]
        summary = MODULE.compare(self.arguments(controls, candidates))
        self.assertEqual(summary["gate"], "pass")
        self.assertAlmostEqual(summary["changes_percent"]["axeyum_p50"], 2.0)
        self.assertAlmostEqual(summary["changes_percent"]["maximum_rss_p50"], 4.0)

    def test_rejects_exact_work_drift(self) -> None:
        controls = [self.write_run(f"control-{i}", report(False)) for i in range(3)]
        candidates = [self.write_run(f"candidate-{i}", report(True)) for i in range(3)]
        changed = json.loads(candidates[-1][0].read_text())
        changed["exact_work"]["warm_checks"] = 11
        candidates[-1][0].write_text(json.dumps(changed))
        with self.assertRaisesRegex(MODULE.GateError, "exact trace/work identity drift"):
            MODULE.compare(self.arguments(controls, candidates))

    def test_rejects_no_recovery_and_resource_alarm(self) -> None:
        controls = [self.write_run(f"control-{i}", report(False)) for i in range(3)]
        no_recovery = report(True)
        no_recovery["timeout_continuation"].update(
            {"continuations": 1, "recoveries": 0, "unknowns": 1}
        )
        candidates = [
            self.write_run(f"candidate-{i}", no_recovery, 1100) for i in range(3)
        ]
        with self.assertRaisesRegex(MODULE.GateError, "recover a decision"):
            MODULE.compare(self.arguments(controls, candidates))


if __name__ == "__main__":
    unittest.main()
