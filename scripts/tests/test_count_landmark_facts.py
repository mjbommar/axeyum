"""Controls for `count-landmark-facts.py` (W1-4, roadmap C6/12.3).

Every guard below is driven to failure, per this repository's rule: deleting
any single guard from the checker must kill exactly one test here. The
checker's own job is to make a landmark COUNT depend on a stated, checkable
rule (`epistemic_status == "proved"` and a curated, non-`[generated]` title)
rather than on the raw ledger total, and to refuse to report a count at all
when the ledger it read is malformed rather than merely small.

Nine guards, each isolated to one assertion so a single deleted line kills
exactly one test:

  A. `is_generated` reads the `[generated]` prefix, not any other marker.
  B. `is_landmark` requires BOTH `proved` and curated -- neither alone.
  C. `count` reduces a fact list to the four counters correctly.
  D. `load_facts` raises on invalid JSON, naming the offending file.
  E. `load_facts` raises when `epistemic_status` is missing.
  F. `load_facts` raises when `title` is missing.
  G. `load_facts` raises on an empty facts directory (no ledger silently
     reads as zero landmarks).
  H. `run_check` returns 0 when measured counts equal the baseline.
  I. `run_check` returns nonzero and reports the mismatched field(s) when
     they differ.

Two are driven against the checker's OWN behaviour rather than a hand-built
object (D and G): a scanner that only fails for a fabricated report proves
the `if` statement works, not that the checker actually reads a directory of
real files and can tell a broken one from a healthy one.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "count_landmark_facts", ROOT / "scripts" / "count-landmark-facts.py"
)
assert SPEC and SPEC.loader
CLF = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CLF)


def write_fact(directory: pathlib.Path, name: str, **fields) -> pathlib.Path:
    path = directory / f"{name}.json"
    path.write_text(json.dumps(fields), encoding="utf-8")
    return path


class IsGeneratedTests(unittest.TestCase):
    """Guard A: the `[generated]` prefix, and only that prefix, is read."""

    def test_generated_prefix_is_detected(self) -> None:
        fact = {"title": "[generated] kernel theorem Rat.abs_nonneg (rat prelude)"}
        self.assertTrue(CLF.is_generated(fact))

    def test_curated_title_is_not_generated(self) -> None:
        fact = {"title": "Quadratic reciprocity"}
        self.assertFalse(CLF.is_generated(fact))

    def test_the_marker_must_be_a_prefix_not_a_substring(self) -> None:
        # A title merely MENTIONING the marker mid-string is not the same
        # thing the production pass writes at position 0.
        fact = {"title": "not [generated]: a curated title that discusses generation"}
        self.assertFalse(CLF.is_generated(fact))


class IsLandmarkTests(unittest.TestCase):
    """Guard B: landmark requires proved AND curated -- neither alone."""

    def test_proved_and_curated_is_a_landmark(self) -> None:
        fact = {"epistemic_status": "proved", "title": "Quadratic reciprocity"}
        self.assertTrue(CLF.is_landmark(fact))

    def test_proved_and_generated_is_not_a_landmark(self) -> None:
        fact = {"epistemic_status": "proved", "title": "[generated] kernel theorem X"}
        self.assertFalse(CLF.is_landmark(fact))

    def test_curated_but_not_proved_is_not_a_landmark(self) -> None:
        for status in ("open", "computed", "conjectured", "refuted"):
            with self.subTest(status=status):
                fact = {"epistemic_status": status, "title": "Quadratic reciprocity"}
                self.assertFalse(CLF.is_landmark(fact))


class CountTests(unittest.TestCase):
    """Guard C: the five counters are reduced correctly over a fixed list."""

    def test_counts_over_a_known_fixture_set(self) -> None:
        facts = [
            {"epistemic_status": "proved", "title": "Quadratic reciprocity"},
            {"epistemic_status": "proved", "title": "[generated] kernel theorem X"},
            {"epistemic_status": "proved", "title": "[generated] kernel theorem Y"},
            {"epistemic_status": "open", "title": "An open conjecture"},
            {"epistemic_status": "computed", "title": "[generated] a computed value"},
        ]
        counts = CLF.count(facts)
        self.assertEqual(
            counts,
            {"total": 5, "proved": 3, "generated": 3, "imported": 0, "landmark": 1},
        )


class ImportDependentRouteTests(unittest.TestCase):
    """Guard C2 (ADR-1664 rule 5): a proof term this project did not author, or
    did not author alone, is not a landmark.

    Measured 2026-09-05, before this clause existed: all seven
    `imported-kernel-lean` facts were counted as landmarks, Mathlib's
    Intermediate Value Theorem and Extreme Value Theorem among them. A landmark
    count that includes a theorem Mathlib proved is not measuring what the
    script's own docstring says it measures.
    """

    def fact(self, route: str | None) -> dict:
        f = {"epistemic_status": "proved", "title": "A curated title"}
        if route is not None:
            f["proof_route"] = route
        return f

    def test_an_originated_proved_fact_is_a_landmark(self) -> None:
        # The acceptance half. A clause broad enough to exclude the ordinary
        # case would zero the counter and no exclusion test would notice.
        self.assertTrue(CLF.is_landmark(self.fact("kernel-lean")))

    def test_a_fact_with_no_route_at_all_is_still_a_landmark(self) -> None:
        # `proof_route` is read with `.get` and is deliberately NOT a required
        # field: making the script fail-closed on its absence would reject a
        # well-formed ledger, and treating absence as "imported" would silently
        # drop facts.
        self.assertTrue(CLF.is_landmark(self.fact(None)))

    def test_an_imported_fact_is_not_a_landmark(self) -> None:
        # Deliberately ONE assertion: the mutation harness counts each subTest
        # failure as a separate death, and the contract is that deleting the
        # clause kills exactly one test.
        self.assertFalse(CLF.is_landmark(self.fact("imported-kernel-lean")))

    def test_every_import_dependent_route_is_excluded(self) -> None:
        # Derived from the script's own set rather than from a second copy of
        # the literals: a test that spells the route names twice measures the
        # author's memory. Exercises `rests_on_an_import` directly, so it is
        # unaffected by a mutation at the `is_landmark` call site.
        for route in CLF.IMPORT_DEPENDENT_ROUTES:
            with self.subTest(route=route):
                self.assertTrue(CLF.rests_on_an_import(self.fact(route)))
        for route in ("kernel-lean", "smt-term-level", "cas-certificate", "none"):
            with self.subTest(route=route):
                self.assertFalse(CLF.rests_on_an_import(self.fact(route)))

    def test_the_imported_counter_counts_them_regardless_of_status(self) -> None:
        # `imported` is reported beside `landmark` so the exclusion is visible
        # rather than merely subtracted, and it counts open imports too -- the
        # number a reader wants is "how much of this ledger is scaffolding".
        #
        # Asserts only `imported`, deliberately: the landmark consequence is
        # asserted by `test_an_imported_fact_is_not_a_landmark`, and this suite's
        # contract is that deleting the exclusion clause kills exactly that one
        # test. A `landmark` assertion here would die with it.
        facts = [
            self.fact("imported-kernel-lean"),
            self.fact("kernel-lean-over-import"),
            {"epistemic_status": "open", "title": "t",
             "proof_route": "imported-kernel-lean"},
            self.fact("kernel-lean"),
        ]
        self.assertEqual(CLF.count(facts)["imported"], 3)


class LoadFactsTests(unittest.TestCase):
    """Guards D, E, F, G: the ledger reader fails closed on a broken ledger."""

    def test_invalid_json_is_rejected_by_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            write_fact(directory, "good", epistemic_status="proved", title="Fine")
            bad_path = directory / "bad.json"
            bad_path.write_text("{not valid json", encoding="utf-8")
            with self.assertRaises(CLF.MalformedLedgerError) as ctx:
                CLF.load_facts(directory)
            self.assertEqual(ctx.exception.path, bad_path)

    def test_missing_epistemic_status_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            path = write_fact(directory, "no-status", title="Missing its status")
            with self.assertRaises(CLF.MalformedLedgerError) as ctx:
                CLF.load_facts(directory)
            self.assertEqual(ctx.exception.path, path)
            self.assertIn("epistemic_status", ctx.exception.reason)

    def test_missing_title_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            path = write_fact(directory, "no-title", epistemic_status="proved")
            with self.assertRaises(CLF.MalformedLedgerError) as ctx:
                CLF.load_facts(directory)
            self.assertEqual(ctx.exception.path, path)
            self.assertIn("title", ctx.exception.reason)

    def test_empty_directory_is_rejected_not_silently_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            with self.assertRaises(CLF.MalformedLedgerError):
                CLF.load_facts(directory)

    def test_a_healthy_directory_loads_every_fact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            write_fact(directory, "a", epistemic_status="proved", title="A")
            write_fact(directory, "b", epistemic_status="open", title="B")
            facts = CLF.load_facts(directory)
            self.assertEqual(len(facts), 2)


class RunCheckTests(unittest.TestCase):
    """Guards H, I: --check agrees with a matching baseline and names drift."""

    def test_matching_baseline_returns_zero(self) -> None:
        counts = {"total": 10, "proved": 8, "generated": 3, "landmark": 5}
        with tempfile.TemporaryDirectory() as tmp:
            baseline_path = pathlib.Path(tmp) / "baseline.json"
            baseline_path.write_text(json.dumps(counts), encoding="utf-8")
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                status = CLF.run_check(counts, baseline_path)
            self.assertEqual(status, 0)

    def test_drift_is_reported_and_nonzero(self) -> None:
        baseline = {"total": 10, "proved": 8, "generated": 3, "landmark": 5}
        measured = {"total": 10, "proved": 8, "generated": 3, "landmark": 6}
        with tempfile.TemporaryDirectory() as tmp:
            baseline_path = pathlib.Path(tmp) / "baseline.json"
            baseline_path.write_text(json.dumps(baseline), encoding="utf-8")
            buf = io.StringIO()
            with contextlib.redirect_stderr(buf):
                status = CLF.run_check(measured, baseline_path)
            self.assertNotEqual(status, 0)
            self.assertIn("landmark", buf.getvalue())

    def test_missing_baseline_file_is_reported_and_nonzero(self) -> None:
        counts = {"total": 1, "proved": 1, "generated": 0, "landmark": 1}
        with tempfile.TemporaryDirectory() as tmp:
            missing_path = pathlib.Path(tmp) / "does-not-exist.json"
            buf = io.StringIO()
            with contextlib.redirect_stderr(buf):
                status = CLF.run_check(counts, missing_path)
            self.assertNotEqual(status, 0)
            self.assertIn("BASELINE_MISSING", buf.getvalue())


class MainExitStatusTests(unittest.TestCase):
    """The whole CLI: exit status depends on the finding, not on completion."""

    def test_malformed_ledger_exits_two(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            write_fact(directory, "bad", epistemic_status="proved")  # no title
            buf = io.StringIO()
            with contextlib.redirect_stderr(buf):
                status = CLF.main(["--facts-dir", str(directory)])
            self.assertEqual(status, 2)
            self.assertIn("MALFORMED_LEDGER", buf.getvalue())

    def test_healthy_ledger_with_no_check_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            directory = pathlib.Path(tmp)
            write_fact(directory, "a", epistemic_status="proved", title="A")
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                status = CLF.main(["--facts-dir", str(directory)])
            self.assertEqual(status, 0)
            self.assertIn("LANDMARK_FACTS", buf.getvalue())


if __name__ == "__main__":
    unittest.main()
