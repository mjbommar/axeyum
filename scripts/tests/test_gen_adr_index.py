"""Focused tests for the generated ADR index.

Every test here is a control for exactly one guard in
``scripts/gen-adr-index.py``: each guard was deleted in turn and the deletion
had to make exactly one of these fail.  Two guards survived their first
deletion (the front-matter blank-line stop and the filename sort tiebreak) and
the tests for them were written from that failure, not before it.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-adr-index.py"
SPEC = importlib.util.spec_from_file_location("gen_adr_index", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def write(directory: Path, name: str, text: str) -> Path:
    path = directory / name
    path.write_text(text, encoding="utf-8")
    return path


class ParseTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def test_malformed_heading_is_rejected(self) -> None:
        path = write(self.dir, "adr-0001-x.md", "# Not an ADR heading\n\nStatus: accepted\n")
        with self.assertRaises(MODULE.AdrError) as caught:
            MODULE.parse_adr(path)
        self.assertIn("first line", str(caught.exception))

    def test_missing_status_is_rejected(self) -> None:
        path = write(self.dir, "adr-0001-x.md", "# ADR-0001: Title\n\nDate: 2026-01-01\n\nbody\n")
        with self.assertRaises(MODULE.AdrError) as caught:
            MODULE.parse_adr(path)
        self.assertIn("Status", str(caught.exception))

    def test_prose_after_the_front_matter_is_not_front_matter(self) -> None:
        # The blank line ends the front matter.  Without that stop, a line
        # anywhere in the body that happens to read "Key: value" -- ADRs quote
        # the template, and several discuss `Index-summary` -- would be read as
        # metadata and silently rewrite the row.
        path = write(
            self.dir,
            "adr-0001-x.md",
            "# ADR-0001: Heading title\n\nStatus: accepted\n\n## Context\n\nIndex-summary: hijacked\n",
        )
        self.assertEqual(MODULE.parse_adr(path)["title"], "Heading title")

    def test_index_summary_overrides_the_heading(self) -> None:
        path = write(
            self.dir,
            "adr-0001-x.md",
            "# ADR-0001: Terse Heading\n\nStatus: accepted\nIndex-summary: The curated summary\n",
        )
        self.assertEqual(MODULE.parse_adr(path)["title"], "The curated summary")

    def test_index_status_overrides_the_status_line(self) -> None:
        path = write(
            self.dir,
            "adr-0001-x.md",
            "# ADR-0001: Title\n\nStatus: accepted (first slice only)\nIndex-status: accepted\n",
        )
        self.assertEqual(MODULE.parse_adr(path)["status"], "accepted")

    def test_bullet_and_bold_front_matter_styles_parse(self) -> None:
        # Nine committed ADRs use these two shapes; a '^Status:' scan misses
        # every one of them.
        bullet = write(self.dir, "adr-0002-b.md", "# ADR-0002: T\n\n- Status: proposed\n")
        bold = write(self.dir, "adr-0003-c.md", "# ADR-0003: T\n\n- **Status:** accepted\n")
        self.assertEqual(MODULE.parse_adr(bullet)["status"], "proposed")
        self.assertEqual(MODULE.parse_adr(bold)["status"], "accepted")

    def test_pipe_in_a_cell_is_rejected(self) -> None:
        path = write(
            self.dir,
            "adr-0001-x.md",
            "# ADR-0001: T\n\nStatus: accepted\nIndex-summary: a | b\n",
        )
        with self.assertRaises(MODULE.AdrError) as caught:
            MODULE.parse_adr(path)
        self.assertIn("break the table row", str(caught.exception))


class OrderingTests(unittest.TestCase):
    def test_duplicate_numbers_are_ordered_by_filename(self) -> None:
        # Sorting on the number alone is stable, so it would preserve whatever
        # order the filesystem produced for the two 0167s.
        rows = [
            {"number": "0167", "path": "adr-0167-prover-track-entry.md"},
            {"number": "0167", "path": "adr-0167-opt-in-ordered.md"},
        ]
        self.assertEqual(
            [row["path"] for row in sorted(rows, key=MODULE.row_sort_key)],
            ["adr-0167-opt-in-ordered.md", "adr-0167-prover-track-entry.md"],
        )


class RenderTests(unittest.TestCase):
    ROWS = [{"number": "0001", "path": "adr-0001-x.md", "title": "T", "status": "accepted"}]

    def test_preamble_with_its_own_index_heading_is_rejected(self) -> None:
        with self.assertRaises(MODULE.AdrError) as caught:
            MODULE.render("# Decision Records\n\n## Index\n\nhand-written rows\n", self.ROWS)
        self.assertIn("own '## Index'", str(caught.exception))

    def test_preamble_must_start_with_a_level_one_heading(self) -> None:
        with self.assertRaises(MODULE.AdrError) as caught:
            MODULE.render("Some prose with no heading\n", self.ROWS)
        self.assertIn("level-1 heading", str(caught.exception))

    def test_banner_is_emitted_under_the_title(self) -> None:
        rendered = MODULE.render("# Decision Records\n\nprose\n", self.ROWS)
        lines = rendered.splitlines()
        self.assertEqual(lines[0], "# Decision Records")
        self.assertIn("Generated; do not edit by hand", lines[2])


class CollectTests(unittest.TestCase):
    def test_an_empty_decisions_directory_is_rejected(self) -> None:
        with TemporaryDirectory() as tmp:
            original = MODULE.DECISIONS
            MODULE.DECISIONS = Path(tmp)
            try:
                with self.assertRaises(MODULE.AdrError) as caught:
                    MODULE.collect()
            finally:
                MODULE.DECISIONS = original
        self.assertIn("no adr-*.md", str(caught.exception))


class CheckModeTests(unittest.TestCase):
    """`--check` is the gate; it has to notice a hand edit."""

    def _run_check(self, contents: str) -> int:
        with TemporaryDirectory() as tmp:
            output = Path(tmp) / "README.md"
            output.write_text(contents, encoding="utf-8")
            original_output, original_argv = MODULE.OUTPUT, sys.argv
            MODULE.OUTPUT = output
            sys.argv = ["gen-adr-index.py", "--check"]
            try:
                return MODULE.main()
            finally:
                MODULE.OUTPUT, sys.argv = original_output, original_argv

    def test_check_rejects_a_hand_edited_index(self) -> None:
        good = MODULE.render(MODULE.PREAMBLE.read_text(encoding="utf-8"), MODULE.collect())
        self.assertEqual(self._run_check(good), 0)
        self.assertEqual(self._run_check(good.replace("| accepted |", "| rejected |", 1)), 1)


class CommittedIndexTests(unittest.TestCase):
    def test_committed_index_is_exactly_what_the_generator_produces(self) -> None:
        rendered = MODULE.render(
            MODULE.PREAMBLE.read_text(encoding="utf-8"), MODULE.collect()
        )
        self.assertEqual(MODULE.OUTPUT.read_text(encoding="utf-8"), rendered)

    def test_every_adr_file_has_exactly_one_row(self) -> None:
        rows = MODULE.collect()
        files = sorted(path.name for path in MODULE.DECISIONS.glob("adr-*.md"))
        self.assertEqual(sorted(row["path"] for row in rows), files)
        self.assertGreater(len(rows), 400)


if __name__ == "__main__":
    unittest.main()
