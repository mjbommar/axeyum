import importlib.util
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "select-nontrivial-external-drat.py"
SPEC = importlib.util.spec_from_file_location("select_nontrivial_external_drat", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def row(index: int, expected: str = "unsat") -> dict:
    digest = f"{index:064x}"
    return {
        "path": f"queries/{digest}.smt2",
        "content_hash": f"sha256:{digest}",
        "expected": expected,
        "family": "fixture",
        "tiers": ["proof-holdout-v1"],
    }


class NontrivialExternalDratSelectionTests(unittest.TestCase):
    def test_candidate_order_excludes_observed_and_sat(self) -> None:
        observed = row(8)
        observed["content_hash"] = f"sha256:{MODULE.OBSERVED_HASH}"
        observed["path"] = f"queries/{MODULE.OBSERVED_HASH}.smt2"
        rows = [row(4), row(2), observed, row(1, "sat"), row(3)]
        rows.extend(row(index) for index in range(10, 10 + MODULE.MAX_ATTEMPTS))
        selected = MODULE.candidate_rows(
            {"version": 1, "logic": "QF_BV", "files": rows}
        )
        self.assertEqual(len(selected), MODULE.MAX_ATTEMPTS)
        self.assertEqual(
            [item["content_hash"] for item in selected[:3]],
            [row(index)["content_hash"] for index in (2, 3, 4)],
        )
        self.assertNotIn(
            f"sha256:{MODULE.OBSERVED_HASH}",
            [item["content_hash"] for item in selected],
        )

    def test_rejects_duplicate_or_short_candidate_population(self) -> None:
        duplicate = row(1)
        with self.assertRaisesRegex(ValueError, "repeats content hash"):
            MODULE.candidate_rows(
                {"version": 1, "logic": "QF_BV", "files": [duplicate, duplicate]}
            )
        with self.assertRaisesRegex(ValueError, "fewer candidates"):
            MODULE.candidate_rows(
                {"version": 1, "logic": "QF_BV", "files": [row(1)]}
            )

    def test_verified_requires_exit_zero_and_marker(self) -> None:
        base = {
            "timed_out": False,
            "exit_code": 0,
            "stdout": {"text": "s VERIFIED\n"},
        }
        self.assertTrue(MODULE.verified(base))
        self.assertFalse(MODULE.verified({**base, "exit_code": 1}))
        self.assertFalse(
            MODULE.verified({**base, "stdout": {"text": "s NOT VERIFIED\n"}})
        )
        self.assertFalse(MODULE.verified({**base, "timed_out": True}))


if __name__ == "__main__":
    unittest.main()
