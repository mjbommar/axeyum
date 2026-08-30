#!/usr/bin/env python3
"""Controls for the held-out contamination detector.

The property that matters is not "the script runs and exits 0" -- see
`docs/autogenesis/263-holdout-contamination-by-ordinary-development.md`, whose
whole subject is a gate (`check-autogenesis-holdout-isolation.py`) that ran,
exited 0, and reported nothing because it never looked at the right signal.
So every test here proves the detector's verdict actually depends on what a
fake kernel build returns, not just on whether the subprocess call succeeded:
`test_a_matching_kernel_line_is_reported_contaminated` and
`test_a_non_matching_kernel_line_is_not_reported_contaminated` run the SAME
fixture through the SAME code path and differ only in the fake `run`
function's return value, and the two verdicts differ. A detector never shown
to produce two different outcomes is not evidence, by this repository's own
recurring lesson (40 of 162 checker runs once exited 0 on completion alone).
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-holdout-contamination.py"
SPEC = importlib.util.spec_from_file_location("holdout_contamination", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
detector = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(detector)

# The first row of the real reviewed table -- used as-is so the fixture line
# is exactly what a real `nat_theorem_inventory` run must print, not an
# invented approximation of it.
KNOWN_ROW = detector.KNOWN_CONTAMINATION[0]
OTHER_HELD_OUT = "F:ml430-other-example-0000beef"


def fake_process(stdout: str) -> "subprocess.CompletedProcess[str]":
    return subprocess.CompletedProcess(args=[], returncode=0, stdout=stdout, stderr="")


OTHER_KNOWN_IDS = {row["fact_id"] for row in detector.KNOWN_CONTAMINATION} - {
    KNOWN_ROW["fact_id"]
}


class CheckKnownTests(unittest.TestCase):
    def test_a_matching_kernel_line_is_reported_contaminated(self) -> None:
        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            self.assertEqual(prelude, KNOWN_ROW["prelude"])
            self.assertEqual(name_filter, KNOWN_ROW["kernel_name"])
            return fake_process(KNOWN_ROW["expected_line"] + "\n")

        contaminated, skipped = detector.check_known({KNOWN_ROW["fact_id"]}, run=run)
        self.assertEqual([row["fact_id"] for row in contaminated], [KNOWN_ROW["fact_id"]])
        # The other reviewed rows are not in this fixture's held-out set, so
        # they are SKIPPED rather than checked -- the kernel is never asked
        # about a fact this population does not call held-out.
        self.assertEqual(set(skipped), OTHER_KNOWN_IDS)

    def test_a_non_matching_kernel_line_is_not_reported_contaminated(self) -> None:
        """Same fixture, only the fake kernel output differs -- and the
        verdict differs with it. This is the discriminating pair."""
        mutated = KNOWN_ROW["expected_line"].replace("AxNat.zero)", "AxNat.zero))")

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            return fake_process(mutated + "\n")

        contaminated, skipped = detector.check_known({KNOWN_ROW["fact_id"]}, run=run)
        self.assertEqual(contaminated, [])
        self.assertEqual(set(skipped), OTHER_KNOWN_IDS)

    def test_an_empty_kernel_result_is_not_contaminated(self) -> None:
        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            return fake_process("")

        contaminated, _ = detector.check_known({KNOWN_ROW["fact_id"]}, run=run)
        self.assertEqual(contaminated, [])

    def test_a_reviewed_fact_no_longer_held_out_is_skipped_not_checked(self) -> None:
        calls = []

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            calls.append((prelude, name_filter))
            return fake_process(KNOWN_ROW["expected_line"] + "\n")

        contaminated, skipped = detector.check_known({OTHER_HELD_OUT}, run=run)
        self.assertEqual(contaminated, [])
        self.assertEqual(skipped, [row["fact_id"] for row in detector.KNOWN_CONTAMINATION])
        # Every reviewed row is out of the held-out population in this
        # fixture, so the kernel should never even be asked about them.
        self.assertEqual(calls, [])


class CandidateSweepTests(unittest.TestCase):
    def test_a_word_reordered_name_is_surfaced_as_a_candidate(self) -> None:
        """The real miss doc-263 records: `choose-zero-succ` in the ledger is
        `zero_choose_succ` in the kernel. An exact-substring scan finds only
        3 of the 4 real matches for exactly this reason; a word-SET compare
        catches the reordering."""
        held = [{"fact_id": "F:ml430-nat-foo-bar-deadbeef00"}]

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            if prelude == "nat":
                return fake_process("Nat.bar_foo\t1\t(irrelevant type)\n")
            return fake_process("")

        candidates = detector.candidate_sweep(held, reviewed_ids=set(), run=run)
        self.assertEqual(candidates, [("F:ml430-nat-foo-bar-deadbeef00", "nat:Nat.bar_foo")])

    def test_a_non_matching_name_is_not_surfaced(self) -> None:
        held = [{"fact_id": "F:ml430-nat-foo-bar-deadbeef00"}]

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            if prelude == "nat":
                return fake_process("Nat.completely_unrelated\t1\t(irrelevant)\n")
            return fake_process("")

        candidates = detector.candidate_sweep(held, reviewed_ids=set(), run=run)
        self.assertEqual(candidates, [])

    def test_an_already_reviewed_fact_is_not_swept_again(self) -> None:
        fact_id = "F:ml430-nat-foo-bar-deadbeef00"
        held = [{"fact_id": fact_id}]

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            return fake_process("Nat.bar_foo\t1\t(irrelevant)\n" if prelude == "nat" else "")

        candidates = detector.candidate_sweep(held, reviewed_ids={fact_id}, run=run)
        self.assertEqual(candidates, [])


class WidenedSweepTests(unittest.TestCase):
    """The two 2026-08-30 changes, each with the case that kills its mutation.

    Both exist because `natural-parity` was contaminated five hours before it
    was preregistered and this detector reported nothing: the rule could not see
    a longer kernel name, and the detector was not reading the manifest the
    family lives in.
    """

    def test_a_longer_kernel_name_containing_the_slug_is_surfaced(self) -> None:
        """The real miss: `F:ml430-nat-even-iff-…` against the admitted
        `Nat.even_iff_mod_two_eq_zero`. Equality does not reach it; subset
        does. Kills a revert of `<=` to `==`."""
        held = [{"fact_id": "F:ml430-nat-even-iff-024826e9"}]

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            if prelude == "nat":
                return fake_process("Nat.even_iff_mod_two_eq_zero\t1\t(irrelevant)\n")
            return fake_process("")

        candidates = detector.candidate_sweep(held, reviewed_ids=set(), run=run)
        self.assertEqual(
            candidates,
            [("F:ml430-nat-even-iff-024826e9", "nat:Nat.even_iff_mod_two_eq_zero")],
        )

    def test_the_reverse_containment_is_not_surfaced(self) -> None:
        """A kernel name whose words are a subset of the SLUG's is noise with
        no mechanism behind it. Kills a mutation flipping the direction."""
        held = [{"fact_id": "F:ml430-nat-even-add-one-deadbeef00"}]

        def run(prelude: str, name_filter: str) -> "subprocess.CompletedProcess[str]":
            return fake_process("Nat.even\t1\t(irrelevant)\n" if prelude == "nat" else "")

        self.assertEqual(detector.candidate_sweep(held, reviewed_ids=set(), run=run), [])

    def test_both_manifests_are_read(self) -> None:
        """120 of the 136 pre-amendment held-out rows lived in the extension.
        Kills a revert to reading `NURSERY` alone."""
        with tempfile.TemporaryDirectory() as tmp:
            v1 = pathlib.Path(tmp) / "v1.json"
            v2 = pathlib.Path(tmp) / "v2.json"
            v1.write_text(json.dumps({"entries": [
                {"fact_id": "F:only-in-v1", "partition": "held-out"}]}))
            v2.write_text(json.dumps({"entries": [
                {"fact_id": "F:only-in-v2", "partition": "held-out"}]}))
            saved = (detector.NURSERY, detector.EXTENSION)
            try:
                detector.NURSERY, detector.EXTENSION = v1, v2
                ids = {e["fact_id"] for e in detector.held_out_everywhere()}
            finally:
                detector.NURSERY, detector.EXTENSION = saved
        self.assertEqual(ids, {"F:only-in-v1", "F:only-in-v2"})

    def test_an_extension_with_no_held_out_rows_is_an_error(self) -> None:
        """Each manifest must CONTRIBUTE, or half the population goes unwatched
        while the gate still prints a count."""
        with tempfile.TemporaryDirectory() as tmp:
            v1 = pathlib.Path(tmp) / "v1.json"
            v2 = pathlib.Path(tmp) / "v2.json"
            v1.write_text(json.dumps({"entries": [
                {"fact_id": "F:only-in-v1", "partition": "held-out"}]}))
            v2.write_text(json.dumps({"entries": [
                {"fact_id": "F:trainish", "partition": "train"}]}))
            saved = (detector.NURSERY, detector.EXTENSION)
            try:
                detector.NURSERY, detector.EXTENSION = v1, v2
                with self.assertRaises(detector.ContaminationDetectorError):
                    detector.held_out_everywhere()
            finally:
                detector.NURSERY, detector.EXTENSION = saved


class InfrastructureFailureTests(unittest.TestCase):
    def test_a_missing_manifest_is_an_error(self) -> None:
        with self.assertRaises(detector.ContaminationDetectorError):
            detector.load_nursery(pathlib.Path("/nonexistent/nursery.json"))

    def test_an_empty_held_out_population_is_an_error(self) -> None:
        with self.assertRaises(detector.ContaminationDetectorError):
            detector.held_out_entries({"entries": [{"fact_id": "F:x", "partition": "train"}]})

    def test_entries_missing_entirely_is_an_error(self) -> None:
        with self.assertRaises(detector.ContaminationDetectorError):
            detector.held_out_entries({})


class MainEndToEndTests(unittest.TestCase):
    """Drives `main()` itself against a temporary nursery and a fake `run`,
    which is the pair the task brief asks to be shown side by side: one
    fixture where a held-out proposition IS matched, one where it is not."""

    def setUp(self) -> None:
        self._saved_nursery = detector.NURSERY
        self._saved_run = detector.run_inventory
        self._tmp = tempfile.TemporaryDirectory()
        self.nursery_path = pathlib.Path(self._tmp.name) / "nursery-v1.json"
        self.nursery_path.write_text(
            json.dumps(
                {
                    "entries": [
                        {"fact_id": KNOWN_ROW["fact_id"], "partition": "held-out"},
                        {"fact_id": OTHER_HELD_OUT, "partition": "held-out"},
                        {"fact_id": "F:train-example", "partition": "train"},
                    ]
                }
            )
        )
        detector.NURSERY = self.nursery_path

    def tearDown(self) -> None:
        detector.NURSERY = self._saved_nursery
        detector.run_inventory = self._saved_run
        self._tmp.cleanup()

    def run_main(self) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = detector.main(["--no-candidates"])
        return code, out.getvalue(), err.getvalue()

    def test_matched_case_reports_contaminated(self) -> None:
        detector.run_inventory = lambda prelude, name_filter: fake_process(
            KNOWN_ROW["expected_line"] + "\n"
        )
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("verdict=CONTAMINATED", out)
        self.assertIn("contaminated=1", out)
        self.assertIn(f"contaminated|{KNOWN_ROW['fact_id']}", out)

    def test_unmatched_case_reports_clean(self) -> None:
        detector.run_inventory = lambda prelude, name_filter: fake_process("")
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("verdict=CLEAN", out)
        self.assertIn("contaminated=0", out)
        self.assertNotIn("contaminated|F:", out)

    def test_missing_nursery_exits_nonzero(self) -> None:
        detector.NURSERY = pathlib.Path(self._tmp.name) / "does-not-exist.json"
        detector.run_inventory = lambda prelude, name_filter: fake_process("")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("AUTOGENESIS_HOLDOUT_CONTAMINATION_ERROR", err)


if __name__ == "__main__":
    unittest.main()
