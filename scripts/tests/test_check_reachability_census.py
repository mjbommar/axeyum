"""Controls for `check-reachability-census.py`.

The committed census passes every guard, which is exactly the situation in
which a gate is indistinguishable from a no-op — and this repository has
shipped that gate more than once. So every guard is driven to FAIL here on
synthetic input, through its own rejection path.

Verified by mutation on 2026-08-17: deleting any one guard from the checker
kills exactly one test in this file. The guards do not share a validity check,
which is the shape that once made six of seven guards in another suite
removable with everything still green.
"""

from __future__ import annotations

import contextlib
import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_reachability_census", ROOT / "scripts" / "check-reachability-census.py"
)
assert SPEC and SPEC.loader
RC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RC)

NO_CORPUS = pathlib.Path("/nonexistent/reference-corpus/graph")


@contextlib.contextmanager
def stand_in_corpus(rows):
    """A hermetic corpus holding exactly the slugs `rows` censuses.

    ADR-0553 removed the default path to the reference corpus, so it is absent
    unless an operator exports `AXEYUM_MATH_EDUCATION_GRAPH`. The two coverage
    controls used to `skipTest` in that case -- which is every run -- so both
    guards were reported as covered while never executing. That is the same
    trap `test_validate_tactic_catalog.py` documents: a live-sibling test SKIPs
    under the mutation harness and its guard reads as a survivor.
    """
    with tempfile.TemporaryDirectory() as scratch:
        root = pathlib.Path(scratch) / "graph"
        for corpus, directory in RC.CORPUS_DIR.items():
            path = root / directory
            path.mkdir(parents=True)
            for entry in rows:
                if entry["corpus"] == corpus:
                    (path / f"{entry['slug']}.md").write_text("")
        original = RC.CORPUS_ROOT
        RC.CORPUS_ROOT = root
        try:
            yield root
        finally:
            RC.CORPUS_ROOT = original


def row(corpus: str, slug: str, cls: str, fragment: str = "") -> dict[str, str]:
    return {
        "corpus": corpus,
        "slug": slug,
        "class": cls,
        "fragment": fragment,
        "note": "synthetic",
    }


def padded(extra: list[dict[str, str]] | None = None) -> list[dict[str, str]]:
    """A census over the floor, with two B rows so the ranking is non-empty."""
    rows = [
        row("misconception", "b-limits", "B", "limits-and-convergence"),
        row("technique", "b-induction", "B", "induction-over-nat"),
    ]
    rows += [row("misconception", f"a-{i}", "A") for i in range(RC.MIN_ROWS)]
    return rows + (extra or [])


def doc_for(rows: list[dict[str, str]]) -> str:
    """The document a correct generator would have written for `rows`."""
    totals = RC.totals(rows)
    lines = ["<!-- R3-TOTALS:BEGIN -->", "", "| corpus | rows | A | B | C |", "|---|---:|---:|---:|---:|"]
    for corpus in RC.CORPORA:
        counts = totals[corpus]
        lines.append(
            f"| {corpus} | {sum(counts.values())} | {counts['A']} | "
            f"{counts['B']} | {counts['C']} |"
        )
    lines += ["", "<!-- R3-TOTALS:END -->", "", "<!-- R3-RANKING:BEGIN -->", ""]
    lines += ["| fragment | rows | misconceptions | techniques |", "|---|---:|---:|---:|"]
    for name, count, misc, tech in RC.ranking(rows):
        lines.append(f"| {name} | {count} | {misc} | {tech} |")
    lines += ["", "<!-- R3-RANKING:END -->", ""]
    return "\n".join(lines)


class SyntheticCase(unittest.TestCase):
    """Synthetic slugs are not in the real corpus, so coverage is switched off
    here on purpose; `CorpusCoverage` below drives that guard separately."""

    def setUp(self) -> None:
        self._corpus = RC.CORPUS_ROOT
        RC.CORPUS_ROOT = NO_CORPUS

    def tearDown(self) -> None:
        RC.CORPUS_ROOT = self._corpus

    def check(self, rows: list[dict[str, str]], doc: str | None = None) -> list[str]:
        return RC.evaluate(rows, doc if doc is not None else doc_for(rows))[0]


class TheFixtureItselfPasses(SyntheticCase):
    def test_a_well_formed_census_and_its_generated_doc_pass(self) -> None:
        """Without this, every failure below could be the fixture's fault."""
        self.assertEqual(self.check(padded()), [])


class EachGuardCanFail(SyntheticCase):
    def test_an_unknown_class_is_rejected(self) -> None:
        failures = self.check(padded([row("misconception", "mystery", "A2")]))
        self.assertTrue(any("which is not one of" in f for f in failures), failures)

    def test_an_unknown_corpus_is_rejected(self) -> None:
        failures = self.check(padded([row("people", "euler", "A")]))
        self.assertTrue(any("names corpus" in f for f in failures), failures)

    def test_an_out_of_fragment_row_naming_no_fragment_is_rejected(self) -> None:
        """A decline with no feature request in it is the whole R3 finding lost."""
        failures = self.check(padded([row("misconception", "silent-b", "B")]))
        self.assertTrue(any("names no fragment" in f for f in failures), failures)

    def test_a_reachable_row_naming_a_fragment_is_rejected(self) -> None:
        """Otherwise an A row could pad the ranking it is not part of."""
        failures = self.check(
            padded([row("misconception", "reachable", "A", "cardinality")])
        )
        self.assertTrue(any("only B rows contribute" in f for f in failures), failures)

    def test_a_duplicated_slug_is_rejected(self) -> None:
        failures = self.check(padded([row("misconception", "a-0", "C")]))
        self.assertTrue(any("is censused 2 times" in f for f in failures), failures)

    def test_a_census_below_the_floor_is_rejected(self) -> None:
        """A parser that stops matching reports a green zero without this."""
        rows = [row("misconception", "only", "B", "cardinality")]
        failures = self.check(rows)
        self.assertTrue(any("floor" in f for f in failures), failures)

    def test_a_totals_table_that_disagrees_with_the_census_is_rejected(self) -> None:
        rows = padded()
        failures = self.check(rows, doc_for(rows).replace("| 1 |", "| 9 |", 1))
        self.assertTrue(any("R3-TOTALS" in f for f in failures), failures)

    def test_a_ranking_in_the_wrong_ORDER_is_rejected(self) -> None:
        """The counts can all be right and the ranking still be wrong — R3's
        output is an ordered feature request, so order is content."""
        rows = padded()
        doc = doc_for(rows)
        good = "| induction-over-nat | 1 | 0 | 1 |\n| limits-and-convergence | 1 | 1 | 0 |"
        self.assertIn(good, doc)
        swapped = "| limits-and-convergence | 1 | 1 | 0 |\n| induction-over-nat | 1 | 0 | 1 |"
        failures = self.check(rows, doc.replace(good, swapped))
        self.assertTrue(any("R3-RANKING" in f for f in failures), failures)

    def test_a_census_that_ranks_nothing_is_rejected(self) -> None:
        """All-A is a green run asserting that nothing is out of reach."""
        rows = [row("misconception", f"a-{i}", "A") for i in range(RC.MIN_ROWS)]
        failures = self.check(rows)
        self.assertTrue(any("ranks nothing" in f for f in failures), failures)

    def test_a_missing_totals_anchor_is_not_the_same_as_an_empty_table(self) -> None:
        rows = padded()
        doc = doc_for(rows).replace("<!-- R3-TOTALS:BEGIN -->", "")
        self.assertTrue(
            any("no `R3-TOTALS` anchored table" in f for f in self.check(rows, doc))
        )

    def test_a_missing_ranking_anchor_is_reported(self) -> None:
        rows = padded()
        doc = doc_for(rows).replace("<!-- R3-RANKING:END -->", "")
        self.assertTrue(
            any("no `R3-RANKING` anchored table" in f for f in self.check(rows, doc))
        )


class CorpusCoverage(unittest.TestCase):
    """The guard that keeps the denominator honest.

    `17` reached two strand documents partly because a census can be short a
    row and look complete. Both directions are checked, and an absent corpus
    is reported as SKIPPED rather than passing — an empty result from a tool
    never pointed at the subject is not a negative result.
    """

    def setUp(self) -> None:
        self._corpus = RC.CORPUS_ROOT

    def tearDown(self) -> None:
        RC.CORPUS_ROOT = self._corpus

    def test_an_absent_corpus_is_skipped_not_silently_passed(self) -> None:
        RC.CORPUS_ROOT = NO_CORPUS
        failures, checked = RC.corpus_coverage(padded())
        self.assertEqual(failures, [])
        self.assertFalse(checked)

    def test_a_corpus_row_the_census_never_classified_is_rejected(self) -> None:
        census = RC.read_census()
        with stand_in_corpus(census):
            short = [r for r in census if r["slug"] != "pigeonhole"]
            failures, checked = RC.corpus_coverage(short)
        self.assertTrue(checked)
        self.assertTrue(any("is not censused" in f for f in failures), failures)

    def test_a_censused_row_that_left_the_corpus_is_rejected(self) -> None:
        census = RC.read_census()
        with stand_in_corpus(census):
            failures, checked = RC.corpus_coverage(
                census + [row("technique", "telepathy", "A")]
            )
        self.assertTrue(checked)
        self.assertTrue(any("no longer exists" in f for f in failures), failures)

    def test_a_matching_corpus_produces_no_failures(self) -> None:
        """The positive half: without it, a guard that always fails would pass
        both controls above."""
        census = RC.read_census()
        with stand_in_corpus(census):
            failures, checked = RC.corpus_coverage(census)
        self.assertTrue(checked)
        self.assertEqual(failures, [])

    def test_no_default_path_to_the_reference_corpus_is_stored(self) -> None:
        """ADR-0553. The path is the operator's to supply, never the tree's."""
        source = (ROOT / "scripts" / "check-reachability-census.py").read_text()
        # Below the module docstring only -- the docstring NAMES the removed
        # default on purpose, so a reader knows what used to be here.
        code = source.split('"""', 2)[2]
        self.assertNotIn("expanduser", code)
        self.assertNotIn("projects/personal", code)
        self.assertIsNone(RC.CORPUS_ROOT, "no corpus path without the env var")


class TheCommittedCensusIsMeasuredNotAsserted(unittest.TestCase):
    def test_the_committed_census_and_document_agree(self) -> None:
        rows = RC.read_census()
        failures, report = RC.evaluate(rows)
        self.assertEqual(failures, [])
        self.assertEqual(report["rows"], 190)
        # The finding, pinned: induction is what the adversarial corpus wants.
        self.assertEqual(report["ranking"][0][0], "induction-over-nat")
        self.assertEqual(report["ranking"][0][1], 16)
        # And the number this whole exercise re-derived.
        self.assertEqual(report["totals"]["misconception"]["B"], 16)


if __name__ == "__main__":
    unittest.main()
