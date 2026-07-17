#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import pathlib
import sys
import unittest


SCRIPT = pathlib.Path(__file__).parents[1] / "analyze-glaurung-regime-features.py"
SPEC = importlib.util.spec_from_file_location("regime_features", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
features = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = features
SPEC.loader.exec_module(features)


class RegimeFeatureAnalysisTests(unittest.TestCase):
    def test_extracts_bounded_lexical_query_features(self) -> None:
        query = b"""; ignored comment
(set-logic QF_BV)
(declare-const |x;not-a-comment| (_ BitVec 64))
(assert (= ((_ extract 7 0) (bvadd |x;not-a-comment| (_ bv1 64))) (_ bv2 8)))
(check-sat)
"""
        result = features.query_features(query)
        self.assertEqual(result["declaration_count"], 1)
        self.assertEqual(result["assertion_count"], 1)
        self.assertEqual(result["bv_arithmetic_count"], 1)
        self.assertEqual(result["bv_slice_extend_count"], 1)
        self.assertEqual(result["max_bv_width"], 64)
        self.assertGreater(result["max_sexpr_depth"], 3)

    def test_average_ranks_handle_ties(self) -> None:
        self.assertEqual(features.average_ranks([3.0, 1.0, 1.0]), [3.0, 1.5, 1.5])
        self.assertAlmostEqual(features.spearman([1, 2, 3], [3, 2, 1]), -1.0)

    def test_quartiles_preserve_every_row(self) -> None:
        rows = [
            {
                "driver": "a" if index % 2 == 0 else "b",
                "index": index,
                "query_bytes": index,
                "warm_z3_over_axeyum": 1.0 + index / 10,
                "cold_z3_over_axeyum": 1.0 + index / 20,
            }
            for index in range(9)
        ]
        bins = features.quartile_summaries(rows, "query_bytes")
        self.assertEqual(sum(group["occurrences"] for group in bins), len(rows))
        self.assertEqual([group["quantile_bin"] for group in bins], [1, 2, 3, 4])

    def test_quantile_bins_do_not_split_ties(self) -> None:
        rows = [
            {
                "driver": "a",
                "index": index,
                "query_bytes": 1 if index < 8 else 2,
                "warm_z3_over_axeyum": 1.0,
                "cold_z3_over_axeyum": 1.0,
            }
            for index in range(10)
        ]
        bins = features.quartile_summaries(rows, "query_bytes")
        self.assertEqual(len(bins), 2)
        self.assertEqual(sorted(group["occurrences"] for group in bins), [2, 8])


if __name__ == "__main__":
    unittest.main()
