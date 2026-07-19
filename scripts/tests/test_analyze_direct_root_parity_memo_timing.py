import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-direct-root-parity-memo-timing.py"
SPEC = importlib.util.spec_from_file_location(
    "analyze_direct_root_parity_memo_timing", SCRIPT
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DirectRootParityMemoTimingTests(unittest.TestCase):
    def test_fixed_schedule_forms_six_order_balanced_pairs(self) -> None:
        self.assertEqual(len(MODULE.SCHEDULE), 12)
        pairs = [MODULE.SCHEDULE[index : index + 2] for index in range(0, 12, 2)]
        self.assertEqual(pairs.count(("B", "C")), 3)
        self.assertEqual(pairs.count(("C", "B")), 3)

    def test_exhaustive_bootstrap_is_deterministic(self) -> None:
        values = [0.90, 0.91, 0.92, 0.93, 0.94, 0.95]
        first = MODULE.exhaustive_bootstrap_upper(values)
        second = MODULE.exhaustive_bootstrap_upper(values)
        self.assertEqual(first, second)
        self.assertGreaterEqual(first, MODULE.geometric_mean(values))
        self.assertLess(first, 1.0)

    def test_coefficient_of_variation_uses_sample_standard_deviation(self) -> None:
        values = [100.0, 100.0, 100.0, 100.0, 100.0, 100.0]
        self.assertEqual(MODULE.coefficient_of_variation(values), 0.0)


if __name__ == "__main__":
    unittest.main()
