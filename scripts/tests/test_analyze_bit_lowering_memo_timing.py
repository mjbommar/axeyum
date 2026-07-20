import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-bit-lowering-memo-timing.py"
SPEC = importlib.util.spec_from_file_location("analyze_bit_lowering_memo_timing", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

RUNNER_SCRIPT = Path(__file__).parents[1] / "run-bit-lowering-memo-timing.py"
RUNNER_SPEC = importlib.util.spec_from_file_location(
    "run_bit_lowering_memo_timing", RUNNER_SCRIPT
)
assert RUNNER_SPEC and RUNNER_SPEC.loader
RUNNER = importlib.util.module_from_spec(RUNNER_SPEC)
RUNNER_SPEC.loader.exec_module(RUNNER)


def runs(
    bit_ratio: float = 0.95,
    cold_ratio: float = 0.99,
    rss_ratio: float = 1.04,
    family_ratio: float = 0.95,
) -> list[dict]:
    result = []
    for cell in MODULE.SCHEDULE:
        candidate = cell == "C"
        result.append(
            {
                "cell": cell,
                "bit_blast_ms": 100.0 * (bit_ratio if candidate else 1.0),
                "cold_total_ms": 120.0 * (cold_ratio if candidate else 1.0),
                "family_bit_blast_ms": {
                    family: 10.0 * (family_ratio if candidate else 1.0)
                    for family in MODULE.FAMILIES
                },
                "max_rss_kib": int(100_000 * (rss_ratio if candidate else 1.0)),
                "elapsed_seconds": 1.0,
            }
        )
    return result


class BitLoweringMemoTimingTests(unittest.TestCase):
    def test_fixed_schedule_is_order_balanced(self) -> None:
        pairs = [MODULE.SCHEDULE[index : index + 2] for index in range(0, 12, 2)]
        self.assertEqual(pairs.count(("B", "C")), 3)
        self.assertEqual(pairs.count(("C", "B")), 3)

    def test_runner_pins_same_schedule_and_disables_profiling(self) -> None:
        self.assertEqual(RUNNER.SCHEDULE, MODULE.SCHEDULE)
        arguments = RUNNER.benchmark_args(Path("artifact.json"))
        self.assertNotIn("--profile-bit-demand", arguments)
        self.assertEqual(arguments[arguments.index("--rewrite") + 1], "off")
        self.assertEqual(arguments[arguments.index("--jobs") + 1], "1")

    def test_registered_green_metrics_are_accepted(self) -> None:
        report = MODULE.evaluate_metrics(runs())
        self.assertTrue(report["accepted"])
        self.assertTrue(all(report["gates"].values()))
        self.assertEqual(report["gated_families"], list(MODULE.FAMILIES))

    def test_bit_blast_and_rss_gates_fail_closed(self) -> None:
        self.assertFalse(MODULE.evaluate_metrics(runs(bit_ratio=0.99))["accepted"])
        self.assertFalse(MODULE.evaluate_metrics(runs(rss_ratio=1.06))["accepted"])

    def test_family_gate_is_not_rescued_by_aggregate_gain(self) -> None:
        values = runs(bit_ratio=0.90)
        for run in values:
            if run["cell"] == "C":
                run["family_bit_blast_ms"]["arithmetic"] = 10.3
        report = MODULE.evaluate_metrics(values)
        self.assertFalse(report["gates"]["gated_family_geomeans_at_most_1_02"])
        self.assertFalse(report["accepted"])


if __name__ == "__main__":
    unittest.main()
