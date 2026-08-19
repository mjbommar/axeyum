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


class RemoteCollisionTests(unittest.TestCase):
    """`find_remote_collisions` / `next_free_number`: the cross-checkout guard.

    `--check` (above) only ever reads this working tree, so it cannot see
    `origin/main` minting the same ADR number for a different decision -- the
    live defect this repository shipped twice (0471-0474, then 0468-0470,
    both measured 2026-08-18). These are the pure comparison the network-
    touching `check_remote` wraps.
    """

    def test_same_number_different_content_is_a_collision(self) -> None:
        # A number no real ADR uses. The fixture originally used 0468, a LIVE
        # number, and a repository-wide renumber (`ADR-0468` -> `ADR-0483`,
        # itself a collision fix) rewrote the two filenames here and left the
        # bare `"0468"` assertion behind, because the sed patterns were
        # `ADR-0468` and `adr-0468-` and a bare number matches neither. The
        # suite then failed `'0483' != '0468'`. A fixture that names real ADRs
        # is a fixture the next renumber breaks, so this one names none.
        collisions = MODULE.find_remote_collisions(
            ["adr-0999-local-side.md"],
            ["adr-0999-remote-side.md"],
        )
        self.assertEqual(len(collisions), 1)
        number, local_only, remote_only = collisions[0]
        self.assertEqual(number, "0999")
        self.assertEqual(local_only, ["adr-0999-local-side.md"])
        self.assertEqual(remote_only, ["adr-0999-remote-side.md"])

    def test_identical_filename_on_both_sides_is_not_a_collision(self) -> None:
        # Shared history: the same lane's ADR, already present on both trees.
        self.assertEqual(
            MODULE.find_remote_collisions(["adr-0001-x.md"], ["adr-0001-x.md"]), []
        )

    def test_number_only_on_one_side_is_not_a_collision(self) -> None:
        self.assertEqual(
            MODULE.find_remote_collisions(["adr-0500-x.md"], ["adr-0100-y.md"]), []
        )

    def test_non_numbered_filenames_are_ignored_not_crashed(self) -> None:
        # Numbers deliberately disjoint from the "both sides differ" fixture
        # above, so this exercises only the non-numbered-name skip and not
        # the both-sides-must-differ guard as well.
        self.assertEqual(
            MODULE.find_remote_collisions(
                ["adr-changelog.md", "adr-0001-x.md"], ["adr-0900-y.md"]
            ),
            [],
        )

    def test_next_free_number_is_one_past_the_higher_side(self) -> None:
        self.assertEqual(
            MODULE.next_free_number(
                ["adr-0480-x.md"], ["adr-0479-y.md", "adr-0477-z.md"]
            ),
            "0481",
        )


class CheckRemoteModeTests(unittest.TestCase):
    """`check_remote`: exit status, SKIP-vs-fail, and the staleness trade."""

    def setUp(self) -> None:
        self._saved = {
            name: getattr(MODULE, name)
            for name in (
                "remote_ref_commit",
                "remote_adr_filenames",
                "fetch_head_age_seconds",
                "DECISIONS",
            )
        }
        self.addCleanup(lambda: [setattr(MODULE, k, v) for k, v in self._saved.items()])

    def _use_local(self, tmp: Path, filenames: list[str]) -> None:
        for name in filenames:
            (tmp / name).write_text("", encoding="utf-8")
        MODULE.DECISIONS = tmp

    def test_unresolvable_remote_ref_is_skipped_not_failed(self) -> None:
        MODULE.remote_ref_commit = lambda ref: None

        def _must_not_run(ref: str) -> list[str]:
            raise AssertionError("remote_adr_filenames must not run when the ref is unresolved")

        MODULE.remote_adr_filenames = _must_not_run
        with TemporaryDirectory() as tmp:
            self._use_local(Path(tmp), ["adr-0001-x.md"])
            self.assertEqual(MODULE.check_remote("origin/main", 24.0, False), 0)

    def test_real_collision_fails_regardless_of_freshness(self) -> None:
        # One method, not two: both scenarios below depend on the SAME guard
        # (`if collisions:` firing before the staleness branch is even
        # reached), so a deletion of that guard must kill exactly one test,
        # not two that happen to probe it from different angles.
        MODULE.remote_ref_commit = lambda ref: "deadbeef" * 5
        MODULE.remote_adr_filenames = lambda ref: ["adr-0002-other.md"]
        with TemporaryDirectory() as tmp:
            self._use_local(Path(tmp), ["adr-0002-mine.md"])
            MODULE.fetch_head_age_seconds = lambda: 0.0
            self.assertEqual(
                MODULE.check_remote("origin/main", 24.0, False), 1, "fresh + collision"
            )
            MODULE.fetch_head_age_seconds = lambda: 999_999.0
            self.assertEqual(
                MODULE.check_remote("origin/main", 24.0, False), 1, "stale + collision"
            )

    def test_fresh_clean_passes(self) -> None:
        # Numbers deliberately disjoint from any "both sides claim it"
        # fixture, so this depends only on the overall clean/exit-0 path and
        # not on the both-sides-must-differ guard tested above.
        MODULE.remote_ref_commit = lambda ref: "deadbeef" * 5
        MODULE.remote_adr_filenames = lambda ref: ["adr-0900-y.md"]
        MODULE.fetch_head_age_seconds = lambda: 0.0
        with TemporaryDirectory() as tmp:
            self._use_local(Path(tmp), ["adr-0001-x.md"])
            self.assertEqual(MODULE.check_remote("origin/main", 24.0, False), 0)

    def test_stale_clean_is_advisory_not_a_failure_by_default(self) -> None:
        MODULE.remote_ref_commit = lambda ref: "deadbeef" * 5
        MODULE.remote_adr_filenames = lambda ref: ["adr-0900-y.md"]
        MODULE.fetch_head_age_seconds = lambda: 999_999.0
        with TemporaryDirectory() as tmp:
            self._use_local(Path(tmp), ["adr-0001-x.md"])
            self.assertEqual(MODULE.check_remote("origin/main", 24.0, False), 0)

    def test_stale_clean_fails_with_require_fresh(self) -> None:
        MODULE.remote_ref_commit = lambda ref: "deadbeef" * 5
        MODULE.remote_adr_filenames = lambda ref: ["adr-0900-y.md"]
        MODULE.fetch_head_age_seconds = lambda: 999_999.0
        with TemporaryDirectory() as tmp:
            self._use_local(Path(tmp), ["adr-0001-x.md"])
            self.assertEqual(MODULE.check_remote("origin/main", 24.0, True), 1)


class CheckRemoteCLITests(unittest.TestCase):
    """`--check-remote` CLI wiring, through `main()`."""

    def test_flags_are_parsed_and_routed_to_check_remote(self) -> None:
        calls: list[tuple[str, float, bool]] = []

        def _fake_check_remote(remote_ref: str, max_staleness_hours: float, require_fresh: bool) -> int:
            calls.append((remote_ref, max_staleness_hours, require_fresh))
            return 0

        original_check_remote, original_argv = MODULE.check_remote, sys.argv
        MODULE.check_remote = _fake_check_remote
        sys.argv = [
            "gen-adr-index.py",
            "--check-remote",
            "--remote-ref",
            "upstream/main",
            "--max-staleness-hours",
            "6",
            "--require-fresh",
        ]
        try:
            self.assertEqual(MODULE.main(), 0)
        finally:
            MODULE.check_remote, sys.argv = original_check_remote, original_argv
        self.assertEqual(calls, [("upstream/main", 6.0, True)])

    # A real-git end-to-end run of the SKIP path (no mocking at all) was
    # exercised manually against this checkout's actual `origin/main` while
    # building this gate, rather than kept as a permanent unit test here: it
    # would exercise the exact same `remote_ref_commit is None` guard as
    # `CheckRemoteModeTests.test_unresolvable_remote_ref_is_skipped_not_failed`,
    # and a second test dying from the same guard's deletion would violate
    # this suite's one-guard-one-test discipline for no added coverage.


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
