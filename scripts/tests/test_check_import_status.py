"""Controls for `check-import-status.py`.

The checker passes on the committed tree, so on its own that proves nothing.
Each failure mode is driven here: a number that drifts, and a claim that stops
being present at all. The second is the one that matters — a doc edit that
rewords the block would otherwise turn this gate into a no-op that still
exits 0.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_import_status", ROOT / "scripts" / "check-import-status.py"
)
assert SPEC and SPEC.loader
CIS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CIS)

BLOCK = """
axeyum-lean-import      11 test suites, 5 examples, fail-closed reader
artifacts/lean-imports  6 pinned streams, 6,057 records
artifacts/facts         5 facts on proof_route `imported-kernel-lean`
"""

TRUTH = {
    "test suites": 11,
    "examples": 5,
    "pinned streams": 6,
    "records": 6057,
    "facts": 5,
}


def run(readme_text: str, values: dict[str, int]) -> tuple[int, list[str]]:
    failures = CIS.evaluate(readme_text, values)
    return (1 if failures else 0), failures


class TheCheckerCanFail(unittest.TestCase):
    def test_the_committed_block_passes(self) -> None:
        code, _ = run(BLOCK, TRUTH)
        self.assertEqual(code, 0)

    def test_a_drifted_number_fails(self) -> None:
        """The case that actually happened: the tree grew a test suite and the
        README kept saying 10."""
        code, out = run(BLOCK, {**TRUTH, "test suites": 12})
        self.assertEqual(code, 1)
        self.assertTrue(any("README claims 11, tree has 12" in line for line in out), out)

    def test_thousands_separators_are_not_a_drift(self) -> None:
        code, _ = run(BLOCK.replace("6,057 records", "6057 records"), TRUTH)
        self.assertEqual(code, 0)

    def test_a_claim_that_disappears_fails(self) -> None:
        """A reworded doc must not silently disarm the gate."""
        code, out = run(BLOCK.replace("11 test suites", "several test files"), TRUTH)
        self.assertEqual(code, 1)
        self.assertTrue(any("stopped matching" in line for line in out), out)

    def test_every_claim_is_exercised_by_the_real_readme(self) -> None:
        """A pattern matching nothing in the committed README gates nothing."""
        text = CIS.README.read_text(encoding="utf-8")
        for label, pattern, _ in CIS.CLAIMS:
            self.assertIsNotNone(pattern.search(text), f"dead pattern: {label}")

    def test_the_real_tree_agrees_with_the_real_readme(self) -> None:
        self.assertEqual(CIS.main(), 0)


if __name__ == "__main__":
    unittest.main()
