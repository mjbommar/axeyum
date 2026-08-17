"""Controls for `check-capability-assurance.py`.

It passes on the committed table, which proves nothing by itself. Each guard is
driven to fail here, and the classifier's own distinctions are pinned — in
particular that agreement with an oracle is NOT an external artifact check,
which is the conflation this whole measurement exists to prevent.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_capability_assurance", ROOT / "scripts" / "check-capability-assurance.py"
)
assert SPEC and SPEC.loader
CA = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CA)


class TheClassifierDrawsTheDistinctionThatMatters(unittest.TestCase):
    def test_an_external_checker_reading_our_artifact_is_the_third_tier(self) -> None:
        for ev in ("accepted by the external Rust Carcara checker",
                   "reconstructs to a kernel-checked Lean proof",
                   "DRAT replayed by drat-trim"):
            self.assertEqual(CA.tier({"evidence": ev}), "external-artifact-checker", ev)

    def test_agreeing_with_an_oracle_is_NOT_an_external_check(self) -> None:
        """A differential oracle checks the VERDICT, not our artifact. Counting
        it as external checking is the overstatement the strand exists to
        remove, so it gets its own tier."""
        self.assertEqual(
            CA.tier({"evidence": "differential vs Z3 with zero disagreements"}),
            "differential-only",
        )

    def test_our_own_re_derivation_is_its_own_tier(self) -> None:
        self.assertEqual(
            CA.tier({"evidence": "DRAT proof checked by check_drat (RUP+RAT)"}),
            "self-checker",
        )

    def test_prose_naming_nothing_is_unclassified_not_assumed(self) -> None:
        self.assertEqual(CA.tier({"evidence": "sound by construction"}), "unclassified")


class EachGuardCanFail(unittest.TestCase):
    def test_a_parser_that_stops_matching_fails_rather_than_reporting_zero(self) -> None:
        original = CA.TABLE
        try:
            CA.TABLE = ROOT / "scripts" / "check-capability-assurance.py"  # no entries
            self.assertEqual(CA.main(["--quiet"]), 1)
        finally:
            CA.TABLE = original

    def test_the_committed_table_passes(self) -> None:
        self.assertEqual(CA.main(["--quiet"]), 0)


class TheTableItselfIsParsed(unittest.TestCase):
    def test_entry_and_area_counts_are_what_was_measured(self) -> None:
        recs = CA.entries(CA.TABLE.read_text(encoding="utf-8"))
        self.assertEqual(len(recs), 101)
        self.assertGreaterEqual(len({r["area"] for r in recs}), 23)
        ext = {r["area"] for r in recs if CA.tier(r) == "external-artifact-checker"}
        self.assertGreaterEqual(len(ext), 11)


class CompoundAreaNamesCountAsTheLogicsTheyName(unittest.TestCase):
    """The `area` field is prose and some entries span two logics. Counting raw
    strings understates coverage; rewriting them to one name would delete the
    fact that the capability spans both. So the string stays and the COUNT is
    normalised."""

    def test_a_compound_names_both_logics(self) -> None:
        self.assertEqual(CA.logics("QF_ABV / QF_AUFBV"), {"QF_ABV", "QF_AUFBV"})

    def test_an_abbreviated_second_element_inherits_the_prefix(self) -> None:
        """`QF_UFLIA/UFLRA` means QF_UFLIA and QF_UFLRA. Splitting naively
        invents a logic called `UFLRA` and inflates the denominator — measured
        as 24 logics with a phantom alongside the real `QF_UFLRA`."""
        self.assertEqual(CA.logics("QF_UFLIA/UFLRA"), {"QF_UFLIA", "QF_UFLRA"})
        self.assertNotIn("UFLRA", CA.logics("QF_UFLIA/UFLRA"))

    def test_a_parenthetical_gloss_is_dropped(self) -> None:
        self.assertEqual(CA.logics("QF_S (strings)"), {"QF_S"})
        self.assertEqual(CA.logics("SAT (propositional)"), {"SAT"})

    def test_a_plain_prose_area_is_left_alone(self) -> None:
        """Prefix inheritance must not fire on non-logic areas."""
        self.assertEqual(CA.logics("symbolic execution"), {"symbolic execution"})
        self.assertEqual(CA.logics("datatypes"), {"datatypes"})


if __name__ == "__main__":
    unittest.main()
