"""Controls for `scripts/lane-merge-additive.py`.

The case that matters is `CutMidItem`: it reproduces, in miniature, the exact
shape that made a real merge produce an unparseable file on 2026-08-25 -- two
sides each ending with a dangling `fn foo(` whose parameter list is the shared
context after the hunk. A suite without that case would let the guard be
deleted while staying green, which is the failure mode this repository cares
most about.
"""

from __future__ import annotations

import importlib.util
import io
import contextlib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("lma", ROOT / "scripts" / "lane-merge-additive.py")
assert SPEC and SPEC.loader
lma = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(lma)


def run_check(text: str, tmp: Path) -> tuple[int, str]:
    p = tmp / "subject.rs"
    p.write_text(text, encoding="utf-8")
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        rc = lma.cmd_check(p)
    return rc, buf.getvalue()


class Balance(unittest.TestCase):
    def test_balanced_text_is_zero(self) -> None:
        self.assertEqual(lma.delimiter_balance("fn a() { b(); }")["{"], 0)

    def test_an_unclosed_brace_is_positive(self) -> None:
        self.assertEqual(lma.delimiter_balance("fn a() {")["{"], 1)

    def test_an_unopened_brace_is_negative(self) -> None:
        self.assertEqual(lma.delimiter_balance("}")["{"], -1)

    def test_parens_are_tracked_separately_from_braces(self) -> None:
        """The real failure dangled an open PAREN, not an open brace."""
        bal = lma.delimiter_balance("pub(super) fn declare_x(")
        self.assertEqual(bal["{"], 0)
        self.assertEqual(bal["("], 1)


class Hunks(unittest.TestCase):
    def test_a_clean_file_reports_no_conflict(self) -> None:
        with TempDir() as tmp:
            rc, out = run_check("fn a() {}\n", tmp)
        self.assertEqual(rc, 0)
        self.assertIn("verdict=no-conflict", out)

    def test_an_unterminated_hunk_is_refused(self) -> None:
        with self.assertRaises(SystemExit):
            lma.parse_hunks("<<<<<<< HEAD\nfn a() {}\n")

    def test_both_sides_are_captured(self) -> None:
        hunks = lma.parse_hunks("<<<<<<< HEAD\nA\n=======\nB\n>>>>>>> other\n")
        self.assertEqual(hunks[0]["ours"], ["A"])
        self.assertEqual(hunks[0]["theirs"], ["B"])


class BothSidesSafe(unittest.TestCase):
    """Additive conflicts whose boundaries fall between items ARE safe, and the
    tool must say so -- a check that refuses everything is as useless as one
    that accepts everything."""

    def test_whole_items_on_both_sides_are_safe(self) -> None:
        text = (
            "fn keep() {}\n"
            "<<<<<<< HEAD\n"
            "fn ours() { let x = 1; }\n"
            "=======\n"
            "fn theirs() { let y = 2; }\n"
            ">>>>>>> branch\n"
            "fn tail() {}\n"
        )
        with TempDir() as tmp:
            rc, out = run_check(text, tmp)
        self.assertEqual(rc, 0)
        self.assertIn("verdict=both-sides-safe", out)
        self.assertIn("cut_sides=0", out)


class CutMidItem(unittest.TestCase):
    """The 2026-08-25 shape: each side ends with a dangling signature whose
    parameter list is the shared context AFTER the hunk."""

    SUBJECT = (
        "fn keep() {}\n"
        "<<<<<<< HEAD\n"
        "fn ours_complete() { let x = 1; }\n"
        "\n"
        "/// doc\n"
        "pub(super) fn declare_ours(\n"
        "=======\n"
        "fn theirs_complete() { let y = 2; }\n"
        "\n"
        "/// doc\n"
        "pub(super) fn declare_theirs(\n"
        ">>>>>>> branch\n"
        "    d: &mut Dev,\n"
        ") -> Result<()> {\n"
        "    Ok(())\n"
        "}\n"
    )

    def test_a_cut_side_is_refused(self) -> None:
        with TempDir() as tmp:
            rc, out = run_check(self.SUBJECT, tmp)
        self.assertEqual(rc, 1)
        self.assertIn("verdict=BOTH-SIDES-UNSAFE", out)

    def test_both_sides_are_reported_as_cut_not_just_one(self) -> None:
        with TempDir() as tmp:
            _, out = run_check(self.SUBJECT, tmp)
        self.assertEqual(out.count("CUT"), 2, out)

    def test_keeping_both_sides_really_does_not_parse(self) -> None:
        """The claim the refusal rests on, asserted rather than assumed: strip
        the markers, keep both sides, and the delimiters no longer balance."""
        kept = "\n".join(
            line
            for line in self.SUBJECT.split("\n")
            if not line.startswith(("<<<<<<< ", ">>>>>>> ")) and line.rstrip() != "======="
        )
        bal = lma.delimiter_balance(kept)
        self.assertNotEqual(bal["("], 0, "the motivating failure must reproduce here")


class Items(unittest.TestCase):
    SRC = (
        "/// doc for a\n"
        "fn a() { one(); }\n"
        "\n"
        "pub(super) fn b(x: u8) -> u8 {\n"
        "    if x > 0 { x } else { 0 }\n"
        "}\n"
    )

    def test_items_are_found_with_their_doc_block(self) -> None:
        got = lma.items(self.SRC)
        self.assertEqual(sorted(got), ["a", "b"])
        self.assertIn("/// doc for a", got["a"])

    def test_a_nested_brace_does_not_end_the_item_early(self) -> None:
        got = lma.items(self.SRC)
        self.assertTrue(got["b"].rstrip().endswith("}"))
        self.assertIn("else", got["b"])

    def test_an_unterminated_item_is_skipped_not_truncated(self) -> None:
        self.assertNotIn("c", lma.items("fn c() { unclosed();\n"))


class TempDir:
    def __enter__(self) -> Path:
        import tempfile

        self._d = tempfile.TemporaryDirectory()
        return Path(self._d.name)

    def __exit__(self, *exc: object) -> None:
        self._d.cleanup()


if __name__ == "__main__":
    unittest.main()
