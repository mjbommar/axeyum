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
        self.assertEqual(len(recs), 103)
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


class LogicCoverageIsTheNumberTheStrandQuotes(unittest.TestCase):
    """The strand states its metric as "N of 23 logics", but only the ENTRY
    count was ever emitted, so the quoted figure came from ad-hoc snippets that
    each recomputed it — which is how it drifted before. It is derived and
    printed now."""

    def test_covered_logics_and_the_gap_partition_the_whole_set(self) -> None:
        recs = CA.entries(CA.TABLE.read_text(encoding="utf-8"))
        allg = {lg for r in recs for lg in CA.logics(r["area"])}
        covered = {
            lg
            for r in recs
            if CA.tier(r) == "external-artifact-checker"
            for lg in CA.logics(r["area"])
        }
        self.assertEqual(covered | set(CA.rank(recs)), allg)
        self.assertEqual(covered & set(CA.rank(recs)), set())

    def test_a_compound_row_covers_every_logic_it_names(self) -> None:
        """Entry count and logic count differ precisely here, which is why one
        cannot stand in for the other."""
        recs = [
            {"area": "QF_ABV / QF_AUFBV", "evidence": "checked by Lean", "feature": "f"}
        ]
        self.assertEqual(CA.rank(recs), {})


class TheGapIsRankedByDistanceToAnExternalChecker(unittest.TestCase):
    """Strand item B. The ranking is derived because a written one rots: item B
    itself names `QF_UF` and `datatypes` as candidates, and both have since
    become externally checked."""

    @staticmethod
    def _recs(rows: list[tuple[str, str]]) -> list[dict[str, str]]:
        return [{"area": a, "evidence": e, "feature": "f"} for a, e in rows]

    def test_an_existing_refutation_artifact_is_band_one(self) -> None:
        """A DRAT proof that is built and discarded is plumbing, not research."""
        recs = self._recs([
            ("QF_LRA", "checked by Lean"),
            ("SAT", "the DRAT certificate is checked by check_drat"),
        ])
        self.assertEqual(CA.rank(recs)["SAT"][0], 1)

    def test_a_model_replay_without_a_refutation_artifact_is_band_two(self) -> None:
        recs = self._recs([
            ("QF_LRA", "checked by Lean"),
            ("QF_S", "every sat model is replayed through the ground evaluator"),
        ])
        self.assertEqual(CA.rank(recs)["QF_S"][0], 2)

    def test_no_named_artifact_at_all_is_band_three(self) -> None:
        recs = self._recs([
            ("QF_LRA", "checked by Lean"),
            ("synthesis", "the enumerator terminates"),
        ])
        self.assertEqual(CA.rank(recs)["synthesis"][0], 3)

    def test_an_externally_checked_logic_is_not_in_the_gap_at_all(self) -> None:
        """The control: ranking must not offer work on a solved logic."""
        recs = self._recs([("QF_LRA", "reconstructed and checked by Lean")])
        self.assertNotIn("QF_LRA", CA.rank(recs))


class ASharedRowCannotStateTwoDifferentAssurances(unittest.TestCase):
    """`tier` is per ROW, so `QF_IDL / QF_RDL` asserts one tier for both. Measured
    2026-08-17 that is wrong for exactly that row: QF_RDL renders a Lean theory
    reconstruction (official Lean 4.30.0 accepts it; two mutations rejected) and
    QF_IDL renders only a structural attestation. The number cannot express that,
    so it must at least disclose it."""

    @staticmethod
    def _recs(rows: list[str]) -> list[dict[str, str]]:
        return [{"area": a, "evidence": "e", "feature": "f"} for a in rows]

    def test_a_logic_seen_only_in_a_compound_row_is_disclosed(self) -> None:
        recs = self._recs(["QF_IDL / QF_RDL", "QF_LRA"])
        self.assertEqual(CA.compound_only(recs), {"QF_IDL", "QF_RDL"})

    def test_a_logic_with_its_own_row_is_not_disclosed(self) -> None:
        """The control: having a row of its own is what makes the tier that
        logic's own claim, even when it also appears in a compound row."""
        recs = self._recs(["QF_IDL / QF_RDL", "QF_RDL"])
        self.assertEqual(CA.compound_only(recs), {"QF_IDL"})

    def test_the_committed_table_still_discloses_the_logic_that_is_shared(self) -> None:
        """QF_IDL's assurance is still stated only through `QF_IDL / QF_RDL`."""
        recs = CA.entries(CA.TABLE.read_text(encoding="utf-8"))
        self.assertIn("QF_IDL", CA.compound_only(recs))

    def test_qf_rdl_got_its_own_row_once_it_was_gated_separately(self) -> None:
        """The resolution of the case this class was written for. QF_RDL is now
        handed to official Lean by `lean_crosscheck` while QF_IDL still routes
        through ArithDpll and renders only an attestation, so the two no longer
        share a single claim — QF_RDL states its own."""
        recs = CA.entries(CA.TABLE.read_text(encoding="utf-8"))
        self.assertNotIn("QF_RDL", CA.compound_only(recs))
        solo = [r for r in recs if CA.logics(r["area"]) == {"QF_RDL"}]
        self.assertTrue(solo, "QF_RDL lost its own row")
        self.assertEqual(CA.tier(solo[0]), "external-artifact-checker")


if __name__ == "__main__":
    unittest.main()
