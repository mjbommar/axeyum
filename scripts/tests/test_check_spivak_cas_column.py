"""Controls for `scripts/check-spivak-cas-column.py`.

One case per defect the gate exists to catch, each reconstructed in a SCRATCH
COPY of the document -- never by mutating the tracked file, which other lanes
read and build from (CLAUDE.md, "mutation testing in the shared worktree").

The case that matters most is `test_r3_blank_c_cell`: it reconstructs chapter 20
as it actually stood before 2026-08-31 and requires the gate to go red. Every
case asserts BOTH a nonzero exit AND the specific guard text, so a guard firing
for the wrong reason cannot read as a pass -- and `test_baseline_passes` pins the
other direction, since a gate that refused everything would satisfy every
refusal test here and be worthless.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
GATE = REPO_ROOT / "scripts" / "check-spivak-cas-column.py"
DOC = REPO_ROOT / "docs" / "curriculum" / "foundational-books" / "spivak.md"
FACTS = REPO_ROOT / "artifacts" / "facts"


def run_gate(doc: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [sys.executable, str(GATE), "--doc", str(doc), "--facts", str(FACTS)],
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    return proc.returncode, proc.stdout + proc.stderr


def doc_lines() -> list[str]:
    return DOC.read_text(encoding="utf-8").split("\n")


def find_row(lines: list[str], prefix: str) -> int:
    for i, line in enumerate(lines):
        if line.startswith(prefix):
            return i
    raise AssertionError(
        f"control is stale: no spine row starting {prefix!r} in {DOC}. "
        "The table changed shape; fix the control rather than deleting it."
    )


class SpivakCasColumnControls(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(prefix="spivak-cas-column-")
        self.work = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    def write(self, name: str, lines: list[str]) -> Path:
        path = self.work / name
        path.write_text("\n".join(lines), encoding="utf-8")
        return path

    def assert_rejected(self, path: Path, needle: str) -> None:
        code, out = run_gate(path)
        self.assertEqual(code, 1, f"gate should reject; got exit {code}\n{out}")
        self.assertIn(needle, out, f"gate rejected for the wrong reason\n{out}")

    # -- the other direction: the committed document must PASS ---------------
    def test_baseline_passes(self) -> None:
        """Without this, every refusal test below could be green on a gate that
        rejects everything."""
        code, out = run_gate(DOC)
        self.assertEqual(code, 0, out)
        self.assertIn("every spine row states a CAS verdict", out)

    # -- R3: the defect this whole lane exists to fix ------------------------
    def test_r3_blank_c_cell(self) -> None:
        """Chapter 20 as it stood before 2026-08-31: nothing said about the CAS,
        while `taylor.rs` shipped Taylor's theorem with the Lagrange remainder."""
        lines = doc_lines()
        i = find_row(lines, "| 20 | Taylor polynomials |")
        cells = lines[i].strip()[1:-1].split(" | ")
        cells[3] = "—"
        lines[i] = "| " + " | ".join(cells) + " |"
        self.assert_rejected(self.write("r3.md", lines), "has an EMPTY `C` cell")

    # -- R6: a whole chapter missing from the table --------------------------
    def test_r6_missing_chapter_row(self) -> None:
        lines = [
            line for line in doc_lines()
            if not line.startswith("| **19** | **Integration in elementary terms**")
        ]
        self.assert_rejected(self.write("r6.md", lines), "no row for Spivak chapter(s) 19")

    # -- R5: a C cell that asserts a route and cites nothing ------------------
    def test_r5_unevidenced_assertion(self) -> None:
        lines = doc_lines()
        i = find_row(lines, "| 5 | Limits |")
        cells = lines[i].strip()[1:-1].split(" | ")
        cells[3] = "Yes, the CAS handles this fragment."
        lines[i] = "| " + " | ".join(cells) + " |"
        self.assert_rejected(self.write("r5.md", lines), "names no module, function or fact id")

    # -- R4: an unexplained "none" is as unfalsifiable as a blank ------------
    def test_r4_bare_audited_none(self) -> None:
        lines = doc_lines()
        i = find_row(lines, "| 30 | Uniqueness of the reals |")
        cells = lines[i].strip()[1:-1].split(" | ")
        cells[3] = "**audited — none.**"
        lines[i] = "| " + " | ".join(cells) + " |"
        self.assert_rejected(self.write("r4.md", lines), "marker with no reason")

    # -- R7: a cited fact that is not cas-certificate evidence ---------------
    def test_r7_dangling_fact_id(self) -> None:
        lines = doc_lines()
        i = find_row(lines, "| **11** | Significance of the derivative")
        lines[i] = lines[i].replace(
            "`F:cas-mvt-cubic-witness-sqrt3`",
            "`F:cas-mvt-cubic-witness-that-never-existed`",
        )
        self.assert_rejected(
            self.write("r7.md", lines),
            "which is not a fact with proof_route == 'cas-certificate'",
        )

    # -- R2: a dropped pipe slides `State` into the `C` slot -----------------
    def test_r2_short_row(self) -> None:
        """Chapter 6's C cell is audited-none, so after the shift the row would
        otherwise look fine to R3, R4 and R5 -- only the cell count sees it."""
        lines = doc_lines()
        i = find_row(lines, "| 6 | Continuous functions |")
        cells = lines[i].strip()[1:-1].split(" | ")
        del cells[3]
        lines[i] = "| " + " | ".join(cells) + " |"
        self.assert_rejected(self.write("r2.md", lines), "cells, header has")

    # -- R8: the legend sentence that produced the wrong answer --------------
    def test_r8_stale_three_routes_legend(self) -> None:
        text = DOC.read_text(encoding="utf-8").replace(
            "**FOUR routes, not three.",
            "Three routes, not two:\n\n**FOUR routes, not three.",
            1,
        )
        path = self.work / "r8.md"
        path.write_text(text, encoding="utf-8")
        self.assert_rejected(path, "still says 'Three routes, not two'")

    # -- R1: no table at all, so every per-row guard iterates over nothing ----
    def test_r1_no_table_is_not_a_pass(self) -> None:
        lines = [
            line for line in doc_lines()
            if not line.startswith("| Spivak | Topic | Route |")
        ]
        self.assert_rejected(self.write("r1.md", lines), "no spine table found")


if __name__ == "__main__":
    unittest.main()
