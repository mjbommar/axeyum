#!/usr/bin/env python3
"""Controls for `scripts/check-proof-plan.py`'s three guards.

Each test feeds `check_unit_tests`/`check_digest_probe`/
`check_footprint_unchanged` a fabricated `subprocess.run` result (never a
real cargo invocation -- this file must run in well under a second) and
asserts the guard returns False for exactly the malformation it names. A
positive control (the guard accepts well-formed input) sits beside each
negative, per the standing "negative controls fail two ways" rule -- a
guard that rejects everything, including good input, is as broken as one
that rejects nothing.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from dataclasses import dataclass
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


check_proof_plan = _load(
    "check_proof_plan", REPO_ROOT / "scripts" / "check-proof-plan.py"
)


@dataclass
class FakeProc:
    returncode: int
    stdout: str
    stderr: str = ""


GOOD_TEST_OUTPUT = (
    "running 11 tests\n"
    "test proof_plan::tests::a ... ok\n"
    "\n"
    "test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 1165 filtered out\n"
)

GOOD_DIGEST_ROWS = "\n".join(
    f"{name}\t0\t{'a' * 64}" for name in check_proof_plan.EXPECTED_SUBJECTS
)


class UnitTestsGuard(unittest.TestCase):
    def test_positive_control_accepts_nonzero_pass(self):
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(0, GOOD_TEST_OUTPUT)
        ):
            self.assertTrue(check_proof_plan.check_unit_tests())

    def test_zero_tests_rejected(self):
        zero = GOOD_TEST_OUTPUT.replace(
            "test result: ok. 11 passed; 0 failed",
            "test result: ok. 0 passed; 0 failed",
        )
        with mock.patch.object(check_proof_plan, "run", return_value=FakeProc(0, zero)):
            self.assertFalse(check_proof_plan.check_unit_tests())

    def test_nonzero_exit_rejected(self):
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(101, GOOD_TEST_OUTPUT)
        ):
            self.assertFalse(check_proof_plan.check_unit_tests())

    def test_a_failure_is_rejected_even_with_a_nonzero_pass_count(self):
        failed = GOOD_TEST_OUTPUT.replace(
            "test result: ok. 11 passed; 0 failed",
            "test result: FAILED. 10 passed; 1 failed",
        )
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(101, failed)
        ):
            self.assertFalse(check_proof_plan.check_unit_tests())


class DigestProbeGuard(unittest.TestCase):
    def test_positive_control_accepts_six_rows(self):
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(0, GOOD_DIGEST_ROWS)
        ):
            ok, rows = check_proof_plan.check_digest_probe()
        self.assertTrue(ok)
        self.assertEqual(len(rows), 6)

    def test_nonzero_exit_rejected(self):
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(1, GOOD_DIGEST_ROWS)
        ):
            ok, rows = check_proof_plan.check_digest_probe()
        self.assertFalse(ok)

    def test_missing_row_rejected(self):
        truncated = "\n".join(GOOD_DIGEST_ROWS.splitlines()[:-1])
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(0, truncated)
        ):
            ok, rows = check_proof_plan.check_digest_probe()
        self.assertFalse(ok)

    def test_wrong_subject_name_rejected(self):
        swapped = GOOD_DIGEST_ROWS.replace(
            check_proof_plan.EXPECTED_SUBJECTS[0], "not_a_real_subject"
        )
        with mock.patch.object(
            check_proof_plan, "run", return_value=FakeProc(0, swapped)
        ):
            ok, rows = check_proof_plan.check_digest_probe()
        self.assertFalse(ok)


class FootprintGuard(unittest.TestCase):
    def test_positive_control_accepts_all_zero(self):
        rows = [(name, 0, "x") for name in check_proof_plan.EXPECTED_SUBJECTS]
        self.assertTrue(check_proof_plan.check_footprint_unchanged(rows))

    def test_one_nonzero_footprint_rejected(self):
        rows = [(name, 0, "x") for name in check_proof_plan.EXPECTED_SUBJECTS]
        rows[2] = (rows[2][0], 1, "x")
        self.assertFalse(check_proof_plan.check_footprint_unchanged(rows))


if __name__ == "__main__":
    unittest.main()
