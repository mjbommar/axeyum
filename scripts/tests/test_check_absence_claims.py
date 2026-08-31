#!/usr/bin/env python3
"""Controls for `scripts/check-absence-claims.py`.

Every test drives the REAL module -- loaded from its real path, not restated
here. A recent lane in this area wrote two suites that each defined their own
copy of the subject and asserted against that, importing nothing; deleting a
namespace from the real validator left them exiting 0 having reported "15/15
guards verified" of their own inline literals. A test that restates its
subject is testing the restatement.

Each test names the ONE guard it drives, so
`scripts/tests/mutation_controls.py absence-claims` can report which deletion
kills which test.
"""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts" / "check-absence-claims.py"

_spec = importlib.util.spec_from_file_location("check_absence_claims", SUBJECT)
assert _spec is not None and _spec.loader is not None
cac = importlib.util.module_from_spec(_spec)
sys.modules["check_absence_claims"] = cac
_spec.loader.exec_module(cac)


# A synthetic authority. Deliberately contains the two-spelling case
# (`congrOfUniformlyContinuous`) and the `Nat`/`AxNat` substring case.
AUTHORITY_NAMES = [
    "CReal.weierstrassMTest",
    "CReal.congrOfUniformlyContinuous",
    "CReal.integral",
    "Rat.sumRange_diagonal",
    "Nat.add",
    "AxReal.add",
]


def projection(names: list[str] = AUTHORITY_NAMES, pad_to: int = 0) -> str:
    """`kernel_declaration_projection` (unfiltered) stdout, as TSV rows."""
    rows = [f"creal\ttheorem\t{n}\t0\t\t\t\t(a type)" for n in names]
    rows += [f"pad\ttheorem\tPad.p{i}\t0\t\t\t\t(a type)" for i in range(pad_to)]
    return "\n".join(rows) + "\n"


class Harness(unittest.TestCase):
    """Build a scratch prose tree and run the real `main` over it."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def census(self, **overrides: object) -> Path:
        data: dict = {
            "authority_declaration_floor": 1,
            "bare_named_claim_budget": 9999,
            "excluded_paths": [],
        }
        data.update(overrides)
        path = self.root / "census.json"
        path.write_text(json.dumps(data))
        return path

    def run_gate(
        self,
        census_path: Path | None = None,
        projection_text: str | None = None,
        extra: list[str] | None = None,
    ) -> tuple[int, str]:
        import contextlib
        import io

        census_path = census_path or self.census()
        proj = self.root / "projection.tsv"
        proj.write_text(projection() if projection_text is None else projection_text)
        argv = [
            "--root",
            str(self.root),
            "--census",
            str(census_path),
            "--projection-file",
            str(proj),
        ] + (extra or [])
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = cac.main(argv)
        return status, out.getvalue() + err.getvalue()

    @staticmethod
    def quoted(text: str) -> str:
        """Indent captured output before putting it in an assertion message.

        The subject prints lines beginning `FAIL: `, and
        `scripts/tests/mutation_controls.py` counts test deaths with
        `^(?:FAIL|ERROR): (\\S+)` over the whole unittest output. A failing
        assertion whose message quotes the subject verbatim therefore invents
        extra "deaths" and the harness reports INCONSISTENT -- measured here,
        one real failure reading as two, and one mutation's seven as fourteen.
        Not a result, per that harness's own contract. Indenting keeps the
        diagnostic and stops it impersonating a test name.
        """
        return "\n" + "".join(f"    | {line}\n" for line in text.splitlines())

    def seed_baseline_claim(self) -> None:
        """One bare absence claim, so the detector-vacuity guard is satisfied."""
        self.write("docs/baseline.md", "A helper for this does not exist yet.\n")

    def seed_marker(self) -> None:
        """One SATISFIED marker, so the zero-marker vacuity guard is satisfied.

        Its own claim names the declaration the marker names, so it is an
        annotated site and contributes nothing to the bare-claim budget --
        which lets a test set that budget to 0 and read the result as being
        about its own fixture.
        """
        self.write(
            "docs/seed-marker.md",
            "`CReal.weierstrassMTest` does not exist.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n",
        )


class ExpiryGuards(Harness):
    def test_G1_absent_marker_on_a_present_declaration_fails(self) -> None:
        """G1: an `absent:` claim whose declaration EXISTS has expired."""
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "The M-test does not exist here.\n"
            "<!-- absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("EXPIRED", out)
        self.assertIn("CReal.weierstrassMTest", out)

    def test_G1_control_absent_marker_on_a_missing_declaration_passes(self) -> None:
        """G1 control: the same marker naming something genuinely absent is green."""
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "The reverse bridge does not exist here.\n"
            "<!-- absent: CReal.within_of_close_within -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))

    def test_G2_spelling_normalized_hit_still_fails(self) -> None:
        """G2: the snake_case spelling of a camelCase kernel name is the same claim."""
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "A congruence lemma for uniformly continuous functions does not exist.\n"
            "<!-- absent: CReal.congr_of_uniformly_continuous -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("EXPIRED", out)
        # The kernel spelling must be reported, or the reader cannot find it.
        self.assertIn("CReal.congrOfUniformlyContinuous", out)

    def test_G3_was_absent_marker_on_a_missing_declaration_fails(self) -> None:
        """G3: a resolution record pointing at nothing (rename or removal)."""
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "This obstacle does not exist any more.\n"
            "<!-- was-absent: CReal.renamedAway -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("DANGLING", out)
        self.assertIn("CReal.renamedAway", out)

    def test_G3_control_was_absent_on_a_present_declaration_passes(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "This obstacle does not exist any more.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))

    def test_G4_marker_kind_is_anchored_not_substring_matched(self) -> None:
        """`was-absent` contains `absent`; reading it as `absent` inverts the check.

        Without the anchor this file's four seeded `was-absent:` records would
        be read as live claims and the gate would red on a clean tree.
        """
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "This obstacle does not exist any more.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))
        self.assertNotIn("EXPIRED", out)


class AnswerabilityGuards(Harness):
    def test_G5_unknown_root_is_unanswerable_not_absent(self) -> None:
        """G5: a name in a root the authority does not carry cannot be 'absent'."""
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "It does not exist.\n<!-- absent: Zorglub.frobnicate -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("UNANSWERABLE", out)

    def test_G6_short_projection_is_a_stale_index_not_a_clean_tree(self) -> None:
        """G6: the committed snapshot held 1,644 against a live 1,861.

        A short index reports a newly-landed declaration as still absent --
        the exact failure this gate exists to catch, arriving through the
        gate's own authority.
        """
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_gate(census_path=self.census(authority_declaration_floor=500))
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("STALE", out)

    def test_G6_control_a_projection_at_the_floor_is_accepted(self) -> None:
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_gate(
            census_path=self.census(authority_declaration_floor=500),
            projection_text=projection(pad_to=600),
        )
        self.assertEqual(status, 0, self.quoted(out))

    def test_G7_malformed_projection_row_is_a_broken_gate(self) -> None:
        """G7: a projection this parser cannot read must not read as 'all absent'."""
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_gate(projection_text="not\ttsv\n")
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("malformed projection row", out)


class MarkerGrammarGuards(Harness):
    def test_G8_marker_naming_nothing_is_rejected(self) -> None:
        """G8: a marker that names nothing cannot expire."""
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent:  -->\n")
        status, out = self.run_gate()
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("names no declaration", out)

    def test_G9_marker_naming_a_non_declaration_is_rejected(self) -> None:
        """G9: `absent: the sqrt lemma` is prose, not a checkable name."""
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: the sqrt lemma -->\n")
        status, out = self.run_gate()
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("not a kernel declaration name", out)

    def test_marker_note_after_a_double_dash_is_not_read_as_a_name(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "It does not exist.\n"
            "<!-- absent: CReal.nope -- needed for chapter 12, see the diary -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))


class QuotedMarkerGuards(Harness):
    """Documentation ABOUT the grammar must not be read as claims.

    Found by running the gate for real: the ADR that DEFINES this marker
    quoted `<!-- was-absent: ... -->` as an example, and the generated ADR
    index copied it, so the gate failed on two markers naming a declaration
    called `...`. The document defining the mechanism failed the mechanism.
    """

    def test_G19_a_marker_in_a_code_span_is_documentation_not_a_claim(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "docs/adr.md",
            "Write `<!-- absent: Root.name -->` beside the claim.\n"
            "It does not exist.\n<!-- absent: CReal.nope -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))

    def test_G20_a_marker_in_a_code_fence_is_documentation_not_a_claim(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "docs/adr.md",
            "It does not exist.\n<!-- absent: CReal.nope -->\n"
            "\n```text\n<!-- absent: CReal.weierstrassMTest -->\n```\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))

    def test_quoted_markers_are_counted_never_silently_dropped(self) -> None:
        """A swallowed marker is a false green, the one outcome to avoid."""
        self.seed_baseline_claim()
        self.write(
            "docs/adr.md",
            "Write `<!-- absent: Root.name -->` beside the claim.\n"
            "It does not exist.\n<!-- absent: CReal.nope -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))
        self.assertIn("1 more QUOTED", out)

    def test_an_unquoted_marker_on_the_same_line_still_counts(self) -> None:
        """Stripping code spans must not swallow a real marker beside one."""
        self.seed_baseline_claim()
        self.write(
            "docs/adr.md",
            "As in `<!-- absent: Root.name -->`. It does not exist. "
            "<!-- absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.weierstrassMTest", out)


class VacuityGuards(Harness):
    def test_G10_scanning_zero_files_cannot_be_a_pass(self) -> None:
        """G10: the failure mode this gate is FOR -- exiting 0 on completion alone."""
        status, out = self.run_gate()
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("scanned 0 files", out)

    def test_G11_detecting_zero_claim_sites_cannot_be_a_pass(self) -> None:
        """G11: a broken detector and clean prose are the same observation."""
        self.write("docs/nothing.md", "Nothing controversial is stated here.\n")
        status, out = self.run_gate()
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("matched 0 lines", out)

    def test_G12_zero_markers_cannot_be_a_pass(self) -> None:
        """G12: with no markers every claim is checked against nothing."""
        self.seed_baseline_claim()
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("0 absence markers", out)


class CensusGuards(Harness):
    def test_G13_a_new_unexpirable_named_claim_exceeds_the_budget(self) -> None:
        """G13: the population of unexpirable claims must not grow silently."""
        self.write(
            "docs/claim.md",
            "The `CReal.integral` split does not exist.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n",
        )
        self.write("docs/new.md", "A lemma about `Rat.sumRange_diagonal` does not exist.\n")
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("BARE", out)
        self.assertIn("docs/new.md", out)

    def test_G14_names_are_derived_from_the_authority_not_a_literal_root_list(self) -> None:
        """G14: `CLAUDE.md` and `PLAN.md` match `Root.identifier` and are not names.

        A hand-written list of namespace roots is the defect this whole gate is
        about, one level down: it would classify a filename as a declaration and
        inflate the budgeted population with sites nothing can ever check.
        """
        self.write("docs/claim.md", "No such helper exists; see CLAUDE.md and PLAN.md.\n")
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))

    def test_G15_a_stale_exclusion_fails(self) -> None:
        """G15: a carve-out for a file that no longer exists reads as considered."""
        self.seed_baseline_claim()
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        census = self.census(
            excluded_paths=[{"path": "gone.md", "reason": "generated, once"}]
        )
        status, out = self.run_gate(census_path=census)
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("STALE-EXCLUSION", out)

    def test_G16_an_exclusion_without_a_reason_is_rejected(self) -> None:
        """G16: an allowlist without reasons is how a gate becomes decoration."""
        self.seed_baseline_claim()
        census = self.census(excluded_paths=[{"path": "docs/baseline.md"}])
        status, out = self.run_gate(census_path=census)
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("no non-empty 'reason'", out)

    def test_an_excluded_path_is_really_not_scanned(self) -> None:
        # The excluded file must carry a claim that NAMES a declaration, or
        # the budget cannot move and this test passes with the exclusion
        # deleted -- which is exactly what mutation testing found it doing.
        self.write("docs/baseline.md", "A helper for this does not exist yet.\n")
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        self.write("docs/gen.md", "A `Rat.sumRange_diagonal` variant does not exist.\n")
        census = self.census(
            bare_named_claim_budget=0,
            excluded_paths=[{"path": "docs/gen.md", "reason": "generated"}],
        )
        status, out = self.run_gate(census_path=census)
        self.assertEqual(status, 0, self.quoted(out))
        self.assertNotIn("docs/gen.md", out)

    def test_update_budget_exits_nonzero_when_the_number_moved(self) -> None:
        self.seed_baseline_claim()
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        self.write("docs/named.md", "A `Nat.add` variant does not exist.\n")
        census = self.census(bare_named_claim_budget=0)
        status, out = self.run_gate(census_path=census, extra=["--update-budget"])
        self.assertEqual(status, 1, self.quoted(out))
        self.assertEqual(json.loads(census.read_text())["bare_named_claim_budget"], 1)


class SurfaceGuards(Harness):
    def test_G17_rust_claims_are_read_from_comments_only(self) -> None:
        """G17: a claim in a string literal or an identifier is not a claim."""
        self.seed_baseline_claim()
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        self.write(
            "crates/a/src/lib.rs",
            'fn f() { let s = "CReal.integral does not exist"; }\n',
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))

    def test_G17_control_a_rust_module_doc_claim_IS_read(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "crates/a/src/lib.rs",
            "//! `CReal.weierstrassMTest` does not exist yet.\n"
            "//! <!-- absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("crates/a/src/lib.rs", out)

    def test_a_marker_attaches_to_its_own_block_not_a_line_window(self) -> None:
        """A marker one blank line away belongs to a different paragraph."""
        self.seed_baseline_claim()
        self.write("docs/other.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        # The marker NAMES the claim's subject, so only the blank line between
        # them keeps the claim bare. Gathering markers file-wide instead of
        # block-wide would silence it.
        self.write(
            "docs/split.md",
            "A lemma about `Nat.add` does not exist.\n"
            "\n"
            "<!-- was-absent: Nat.add -->\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("docs/split.md", out)


class MultiLineMarkerGuards(Harness):
    """A marker is an HTML comment, so it may legitimately span lines.

    Found 2026-08-31 (ADR-1250) on the real tree: a correctly-named
    `was-absent:` marker on a resolved claim was written across three lines --
    the natural thing to do, since a marker carrying a note wraps at the same
    column as the prose it sits in -- and the gate did not see it AT ALL.
    `MARKER_RE`'s body was `.*?` without `re.DOTALL`, applied one line at a
    time in all three readers, so the marker was invisible rather than merely
    unattached: not checked against the kernel, not silencing its claim, and
    reported nowhere. The claim stayed BARE and the only remaining way to
    retire it was `--update-budget`, which is the laundering this gate exists
    to prevent. A marker that cannot attach is the mirror of a checker that
    cannot fail.
    """

    MULTI_LINE_MARKER = (
        "<!-- was-absent: CReal.weierstrassMTest -- a note long enough that it\n"
        "     wraps across three separate source lines of running prose -->\n"
    )

    def test_G25_a_marker_written_across_lines_is_read_and_attaches(self) -> None:
        """G25: both directions of a multi-line marker, in one run.

        Deliberately one test for the two halves. Checking a marker against
        the kernel and letting it silence its claim are separate code paths
        but ONE guard (`re.DOTALL`), and splitting them would report that
        guard as killing two tests without measuring anything more.
        """
        self.seed_baseline_claim()
        # (a) it attaches: the claim in this block is annotated, not bare.
        self.write(
            "docs/resolved.md",
            "A lemma about `CReal.weierstrassMTest` does not exist.\n"
            + self.MULTI_LINE_MARKER,
        )
        # (b) it is checked: this one has EXPIRED and the gate must say so.
        self.write(
            "docs/live.md",
            "<!-- absent: CReal.integral -- wrapped across two lines, and the\n"
            "     declaration it names is present, so this claim has rotted -->\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("EXPIRED", out)
        self.assertIn("docs/live.md", out)
        self.assertNotIn("BARE  docs/resolved.md", out)

    def test_G26_a_multi_line_marker_inside_a_rust_doc_comment_parses(self) -> None:
        """G26: `//!` on the continuation lines is comment syntax, not a name.

        The NAMES LIST is what wraps here, not the note. A marker whose note
        wraps parses either way -- `//!` lands harmlessly after the ` -- `
        separator -- so a fixture built that way looks like a control and
        measures nothing. This one puts the second name on the wrapped line,
        where an unstripped `//!` becomes part of it and the whole marker is
        rejected as malformed (exit 2) instead of checked (exit 1).
        """
        self.seed_baseline_claim()
        self.write(
            "crates/a/src/lib.rs",
            "//! <!-- absent: CReal.integral,\n"
            "//!      CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate()
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("EXPIRED", out)
        self.assertIn("crates/a/src/lib.rs", out)

    def test_G27_a_claim_after_a_multi_line_marker_keeps_its_line_number(
        self,
    ) -> None:
        """G27: stripping the marker must not shift the lines below it.

        Deliberately independent of `re.DOTALL`: without it the marker is not
        stripped at all, so the body keeps every line and the number stays
        right. Only collapsing an N-line marker to one space moves it.
        """
        self.seed_baseline_claim()
        self.write(
            "docs/shifted.md",
            self.MULTI_LINE_MARKER
            + "Alpha beta gamma.\n"
            + "A lemma about `Nat.add` does not exist.\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("docs/shifted.md:4", out)
        self.assertNotIn("docs/shifted.md:2", out)


class AuthoritySubprocessGuards(Harness):
    """The DEFAULT path -- no `--projection-file` -- shells out to the tool.

    Every other test injects a captured projection, so nothing else exercises
    the subprocess plumbing. A `--projection-file`-only suite would leave the
    path the gate actually uses in CI unmeasured.
    """

    def stub(self, body: str) -> str:
        path = self.root / "stub-cargo"
        path.write_text("#!/usr/bin/env bash\n" + body)
        path.chmod(0o755)
        return str(path)

    def run_with_cargo(self, cargo_bin: str) -> tuple[int, str]:
        import contextlib
        import io

        argv = [
            "--root",
            str(self.root),
            "--census",
            str(self.census()),
            "--cargo-bin",
            cargo_bin,
        ]
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = cac.main(argv)
        return status, out.getvalue() + err.getvalue()

    def test_a_failing_authority_is_a_broken_gate_not_a_clean_tree(self) -> None:
        """The tool failing must not read as 'nothing is present, all claims hold'."""
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_with_cargo(self.stub('echo boom >&2; exit 101\n'))
        self.assertEqual(status, 2, self.quoted(out))
        self.assertIn("the tool itself failed", out)

    def test_the_default_path_reads_the_tools_stdout(self) -> None:
        self.seed_baseline_claim()
        self.write(
            "docs/claim.md",
            "The M-test does not exist here.\n<!-- absent: CReal.weierstrassMTest -->\n",
        )
        rows = projection().replace("\\", "\\\\")
        script = "cat <<'TSV'\n" + rows + "TSV\n"
        status, out = self.run_with_cargo(self.stub(script))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("EXPIRED", out)


class ExitStatusGuards(Harness):
    def test_G18_exit_status_depends_on_the_finding(self) -> None:
        """G18: 40 of 162 checker runs in this repository exit 0 on completion.

        Two runs over the same tree, differing only in whether a claim has
        expired, must not produce the same status.
        """
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        clean, _ = self.run_gate()
        self.write(
            "docs/claim.md",
            "It does not exist.\n<!-- absent: CReal.weierstrassMTest -->\n",
        )
        dirty, out = self.run_gate()
        self.assertEqual(clean, 0)
        self.assertEqual(dirty, 1, self.quoted(out))

    def test_coverage_is_always_printed_never_implied(self) -> None:
        """A partial rollout reported as complete is the same defect one level up."""
        self.seed_baseline_claim()
        self.write("docs/claim.md", "It does not exist.\n<!-- absent: CReal.nope -->\n")
        status, out = self.run_gate()
        self.assertEqual(status, 0, self.quoted(out))
        self.assertIn("census:", out)
        self.assertIn("do NOT", out)
        self.assertIn("STRUCTURALLY UNCHECKABLE", out)


class ClaimUnitGuards(Harness):
    """A claim is paired with the names in its OWN unit, not its whole block.

    Block-granular association made the census track NOISE: measured
    2026-08-31 over the real tree, 250 bare named sites against 118
    sentence-granular ones, with one Markdown table contributing a single site
    that harvested **93** candidates. Every guard here is about the surplus,
    and every one has a control in the opposite direction -- a narrowed
    matcher that drops a real claim is a weakening, not an improvement.
    """

    def test_G21_a_neighbouring_sentences_names_are_not_the_claims_subject(
        self,
    ) -> None:
        """G21: the surplus. Present evidence beside a claim is not its subject."""
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/block.md",
            "`Nat.add` and `CReal.integral` are both landed and in daily use.\n"
            "Something else entirely does not exist.\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))
        self.assertNotIn("docs/block.md", out)

    def test_G21_control_a_name_in_the_claims_own_sentence_IS_its_subject(
        self,
    ) -> None:
        """The other direction: narrowing must not drop the real subject."""
        self.seed_baseline_claim()
        self.seed_marker()
        self.write("docs/block.md", "`CReal.integral` does not exist in this kernel.\n")
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.integral", out)

    def test_G22_a_colon_does_not_end_a_claim_unit(self) -> None:
        """G22: a claim routinely names its subjects AFTER a colon.

        `(do not exist in the merged tree): CReal.alternatingBracketUpper, ...`
        is one of the 8 stale claims this gate has caught. Splitting on `:`
        would carry its subjects into the next unit and lose them.
        """
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/colon.md",
            "**NOT registered** (do not exist in the merged tree): "
            "`CReal.integral` -- see Findings below.\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.integral", out)

    def test_G23_a_markdown_table_row_is_its_own_claim_unit(self) -> None:
        """G23: the 93-candidate site. A table row is an independent record."""
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/table.md",
            "| 1 | nothing of that shape exists here |\n"
            "| 2 | `CReal.integral` landed and carries its algebra |\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))
        self.assertNotIn("docs/table.md", out)

    def test_G23_control_a_name_in_the_claims_own_row_IS_attributed(self) -> None:
        """Row-splitting must not blind the gate to a claim inside one row."""
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/table.md",
            "| 1 | `CReal.integral` does not exist |\n"
            "| 2 | `Nat.add` landed and is in daily use |\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.integral", out)
        self.assertNotIn("Nat.add", out)

    def test_G23_a_wrapped_list_item_keeps_its_continuation_lines(self) -> None:
        """Only a line that OPENS a record breaks one; a wrap must not.

        `- ...since `Nat.even_or_odd`\\n  does not exist...` is one of the 8
        stale claims, and its subject sits on the line above the phrase.
        """
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/wrap.md",
            "- a note mentioning `CReal.integral`\n"
            "  which does not exist on this branch\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.integral", out)

    def test_G24_a_marker_only_silences_a_claim_it_NAMES(self) -> None:
        """G24: one block, two claims, a marker answering only one of them.

        At block granularity this distinction was unreachable -- a single
        `annotated` flag covered every claim in the block. Four real sites
        were covered by a marker naming something else.
        """
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/two.md",
            "- `CReal.weierstrassMTest` does not exist.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n"
            "- `CReal.integral` does not exist either.\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 1, self.quoted(out))
        self.assertIn("CReal.integral", out)

    def test_G24_control_the_marker_DOES_silence_the_claim_it_names(self) -> None:
        """The other direction: a marker naming the subject must still cover it."""
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/one.md",
            "`CReal.weierstrassMTest` does not exist.\n"
            "<!-- was-absent: CReal.weierstrassMTest -->\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))

    def test_G24_the_marker_match_is_spelling_normalized(self) -> None:
        """`congr_of_uniformly_continuous` and `congrOfUniformlyContinuous`.

        There is no single spelling in this repository, so a marker written in
        the design-document spelling must still cover prose written in the
        kernel spelling -- or the narrowing invents bare sites out of a naming
        convention.
        """
        self.seed_baseline_claim()
        self.seed_marker()
        self.write(
            "docs/spell.md",
            "`CReal.congrOfUniformlyContinuous` does not exist.\n"
            "<!-- was-absent: CReal.congr_of_uniformly_continuous -->\n",
        )
        status, out = self.run_gate(census_path=self.census(bare_named_claim_budget=0))
        self.assertEqual(status, 0, self.quoted(out))


# The 8 genuinely-stale absence claims the 2026-08-31 `absence-and-orphans`
# lane found and corrected, in their PRE-CORRECTION text, cut verbatim out of
# `335cb3661^` at the block the checker segments. Eleven declarations across
# eight claims. A narrowed matcher that stops attributing any one of these to
# its claim is a WEAKENING, and this is the suite that says so.
STALE_FIXTURES: list[tuple[str, list[str]]] = [
    ("133-uniform-converges-add.md", ["CReal.uniform_converges_add"]),
    ("133-even-or-odd.md", ["Nat.even_or_odd"]),
    (
        "133-alternating.md",
        [
            "CReal.alternatingBracketUpper",
            "CReal.alternatingLowerBound",
            "CReal.alternatingUpperBound",
        ],
    ),
    ("200-asc-desc-factorial.md", ["Nat.ascFactorial", "Nat.descFactorial"]),
    ("206-clog.md", ["Nat.clog"]),
    ("complex-of-int.rs", ["Rat.ofInt"]),
    ("irrational-creal-sqrt.rs", ["CReal.sqrt"]),
    ("gcd-comm.rs", ["Nat.gcd_comm"]),
]

FIXTURE_DIR = ROOT / "scripts" / "tests" / "fixtures" / "absence-stale-claims"


class StaleClaimRegression(Harness):
    """Every declaration of the 8 known-stale claims is still attributed."""

    def _stage(self) -> "cac.Authority":
        names = sorted({n for _, decls in STALE_FIXTURES for n in decls})
        for stem, _ in STALE_FIXTURES:
            src = FIXTURE_DIR / stem
            rel = f"docs/{stem}" if stem.endswith(".md") else f"crates/a/src/{stem}"
            self.write(rel, src.read_text())
        return cac.parse_projection(projection(names + AUTHORITY_NAMES), 1)

    def test_all_eleven_declarations_are_still_attributed_to_their_claim(
        self,
    ) -> None:
        authority = self._stage()
        _, _, sites, errors, _ = cac.scan(self.root)
        self.assertEqual(errors, [])
        missed = []
        for stem, decls in STALE_FIXTURES:
            rel = f"docs/{stem}" if stem.endswith(".md") else f"crates/a/src/{stem}"
            attributed = {n for s in sites if s.path == rel for n in s.names(authority)}
            for decl in decls:
                if decl not in attributed:
                    missed.append(f"{rel}: {decl}")
        self.assertEqual(
            missed,
            [],
            "the narrowed matcher stopped attributing a known-stale claim to "
            "its subject -- that is a weakening, not an improvement:\n"
            + "\n".join(f"    {m}" for m in missed),
        )

    def test_the_fixture_corpus_is_not_silently_empty(self) -> None:
        """A regression suite whose fixtures vanished would pass vacuously."""
        self.assertTrue(FIXTURE_DIR.is_dir(), f"{FIXTURE_DIR} is gone")
        present = sorted(p.name for p in FIXTURE_DIR.iterdir() if p.is_file())
        self.assertEqual(present, sorted(stem for stem, _ in STALE_FIXTURES))
        self.assertEqual(sum(len(d) for _, d in STALE_FIXTURES), 11)

    def test_the_stale_claims_would_have_been_CAUGHT_end_to_end(self) -> None:
        """Restore the stale text, and the gate goes red at a zero budget.

        Attribution alone is not the finding -- the gate has to FAIL. Only the
        `133-alternating` fixture carried a marker at that commit, so seven of
        the eight are bare and the budget guard fires on them.
        """
        names = sorted({n for _, decls in STALE_FIXTURES for n in decls})
        self.seed_baseline_claim()
        self._stage()
        status, out = self.run_gate(
            census_path=self.census(bare_named_claim_budget=0),
            projection_text=projection(names + AUTHORITY_NAMES),
        )
        self.assertEqual(status, 1, self.quoted(out))
        for stem, _ in STALE_FIXTURES:
            if stem == "133-alternating.md":
                continue  # already carried a `was-absent:` marker at that commit
            rel = f"docs/{stem}" if stem.endswith(".md") else f"crates/a/src/{stem}"
            self.assertIn(rel, out, self.quoted(out))


if __name__ == "__main__":
    unittest.main()
