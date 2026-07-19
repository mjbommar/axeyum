import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "analyze-direct-root-parity-memo.py"
SPEC = importlib.util.spec_from_file_location("analyze_direct_root_parity_memo", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class DirectRootParityMemoAnalysisTests(unittest.TestCase):
    def test_accepts_only_exact_registered_counter_deltas(self) -> None:
        baseline = {key: 1_000_000 for key in MODULE.CNF_ANALYSIS.COUNTER_PATHS}
        candidate = {
            key: value + MODULE.COUNTER_DELTAS.get(key, 0)
            for key, value in baseline.items()
        }
        self.assertEqual(
            MODULE.counter_deltas(baseline, candidate)["clause_attempts"],
            -107_000,
        )

        candidate["clauses_emitted"] -= 1
        with self.assertRaisesRegex(RuntimeError, "delta mismatch"):
            MODULE.counter_deltas(baseline, candidate)

    def test_family_partition_uses_only_registered_and_slice_partial(self) -> None:
        baseline = {}
        candidate = {}
        for family in MODULE.FAMILIES:
            baseline[family] = {
                "instances": MODULE.FAMILIES[family],
                "sat": 0,
                "unsat": MODULE.FAMILIES[family],
                "counters": {
                    key: 1_000_000 for key in MODULE.CNF_ANALYSIS.COUNTER_PATHS
                },
            }
            removed = MODULE.FAMILY_REMOVED_DUPLICATES.get(family, 0)
            candidate[family] = {
                "instances": MODULE.FAMILIES[family],
                "sat": 0,
                "unsat": MODULE.FAMILIES[family],
                "counters": {
                    key: value
                    + MODULE.COUNTER_DELTAS.get(key, 0) * removed // 107_000
                    for key, value in baseline[family]["counters"].items()
                },
            }

        deltas = MODULE.family_counter_deltas(baseline, candidate)
        self.assertEqual(deltas["arithmetic"]["clause_attempts"], 0)
        self.assertEqual(deltas["register-slice"]["clause_attempts"], -23_828)
        self.assertEqual(deltas["slice-partial"]["clause_attempts"], -83_172)

    def test_selected_origin_is_exact_same_owner_parity_cell(self) -> None:
        row = {
            "first_origin": "root/and_tree/forward/parity",
            "duplicate_origin": "root/and_tree/forward/parity",
            "owner_relation": "same",
        }
        self.assertTrue(MODULE.selected_origin(row))
        row["owner_relation"] = "cross"
        self.assertFalse(MODULE.selected_origin(row))


if __name__ == "__main__":
    unittest.main()
