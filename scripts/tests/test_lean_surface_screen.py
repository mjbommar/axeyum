#!/usr/bin/env python3
"""Control suite for `scripts/lean_surface_screen.py`.

Every fixture here is a REAL pinned Mathlib v4.30 statement whose behaviour was
measured against official Lean 4.30.0 on 2026-09-05 (ADR-1662,
`artifacts/measurements/statement-import-blocker-census-2026-09-05.json`), so
each test asserts a fact about Lean and not about the author's expectation.

The two NEGATIVE fixtures are the point of the suite. A screen that flags every
`↑` would pass a positive-only suite and be useless: 54 of the 756 pinned mirror
statements carry a coercion arrow and 51 of them elaborate. `NEAR_MISS_COERCION`
is one that elaborates for a reason the screen has to see -- an uncoerced
operand of known type in the same group -- and `ASCRIBED_LAMBDA` is the
type-ascribed form of the flagged lambda.

Run:
    python3 -m unittest scripts.tests.test_lean_surface_screen -v
"""

from __future__ import annotations

import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

from lean_surface_screen import screen_statement  # noqa: E402

# --- flagged: measured NOT to elaborate --------------------------------------

# `Nat.le_induction`. The printer replaced two proof terms with `⋯`.
GLYPH = (
    "∀ {m : ℕ} {P : (n : ℕ) → m ≤ n → Prop},\n"
    "  P m ⋯ → (∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯) → "
    "∀ (n : ℕ) (hmn : m ≤ n), P n hmn"
)

# `Int.natAbs_coe_sub_coe_le_of_le`. Lean: invalid coercion notation, expected
# type is not known.
COERCED_PROJECTION = "∀ {a b n : ℕ}, a ≤ n → b ≤ n → (↑a - ↑b).natAbs ≤ n"

# `Nat.choose_mono`. Lean: Invalid field notation: Type of a is not known.
UNASCRIBED_LAMBDA = "∀ (b : ℕ), Monotone fun a => a.choose b"

# --- clean: measured TO elaborate --------------------------------------------

# `Int.add_ediv_of_dvd_left`, one of the 751 that elaborate.
CLEAN = "∀ {a b c : ℤ}, c ∣ a → (a + b) / c = a / c + b / c"

# `Int.gcd_div_gcd_div_gcd`. Dot notation on a group containing a coercion, and
# it elaborates: `i` and `j` are uncoerced operands of known type inside the very
# same group, so the coercion's target is determined.
NEAR_MISS_COERCION = "∀ {i j : ℤ}, 0 < i.gcd j → (i / ↑(i.gcd j)).gcd (j / ↑(i.gcd j)) = 1"

# The ascribed form of UNASCRIBED_LAMBDA. Field notation resolves because the
# binder carries its type.
ASCRIBED_LAMBDA = "∀ (b : ℕ), Monotone fun (a : ℕ) => a.choose b"


def classes(statement: str) -> list[str]:
    return [finding.screen_class for finding in screen_statement(statement)]


def signatures(statement: str) -> list[str]:
    return [finding.signature for finding in screen_statement(statement)]


class GlyphClass(unittest.TestCase):
    def test_elided_proof_glyph_is_flagged(self) -> None:
        self.assertIn("elided-proof-glyph", classes(GLYPH))


class VariableBlockClass(unittest.TestCase):
    def test_coerced_projection_is_flagged(self) -> None:
        self.assertIn("coerced-projection", signatures(COERCED_PROJECTION))

    def test_unascribed_lambda_projection_is_flagged(self) -> None:
        self.assertIn("unascribed-lambda-projection", signatures(UNASCRIBED_LAMBDA))


class NegativeControls(unittest.TestCase):
    def test_clean_statement_is_not_flagged(self) -> None:
        self.assertEqual([], screen_statement(CLEAN))

    def test_coercion_with_a_typed_sibling_is_not_flagged(self) -> None:
        self.assertEqual([], screen_statement(NEAR_MISS_COERCION))

    def test_ascribed_lambda_is_not_flagged(self) -> None:
        self.assertEqual([], screen_statement(ASCRIBED_LAMBDA))


class Statements(unittest.TestCase):
    def test_the_screen_never_rewrites_a_statement(self) -> None:
        """ADR-0615: a preregistered `formal.statement` is never edited."""
        before = COERCED_PROJECTION
        screen_statement(before)
        self.assertEqual(before, COERCED_PROJECTION)
        for finding in screen_statement(before):
            self.assertIn(finding.evidence.split()[0].lstrip("("), before.replace("(", " ("))


class CommandLine(unittest.TestCase):
    """The exit status must depend on the finding, not on the run completing.

    The flagged input carries BOTH classes deliberately. With a single-class
    fixture, disabling any one signature also kills this test, and the mutation
    control can then no longer say whether the exit-status wiring is guarded on
    its own.
    """

    def _run_jsonl(self, rows: list[tuple[str, str]]) -> subprocess.CompletedProcess:
        import json
        import tempfile

        with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as handle:
            for fact_id, statement in rows:
                handle.write(json.dumps({"fact_id": fact_id, "statement": statement}) + "\n")
            path = handle.name
        try:
            return subprocess.run(
                [sys.executable, str(ROOT / "scripts/lean_surface_screen.py"), "--jsonl", path],
                capture_output=True,
                text=True,
            )
        finally:
            pathlib.Path(path).unlink(missing_ok=True)

    def test_a_flagged_population_exits_nonzero(self) -> None:
        completed = self._run_jsonl(
            [
                ("F:fixture-glyph", GLYPH),
                ("F:fixture-coerced", COERCED_PROJECTION),
                ("F:fixture-lambda", UNASCRIBED_LAMBDA),
            ]
        )
        self.assertEqual(1, completed.returncode, completed.stdout + completed.stderr)

    def test_a_clean_population_exits_zero(self) -> None:
        completed = self._run_jsonl(
            [
                # NEAR_MISS_COERCION is deliberately NOT here: it is the
                # discriminating fixture of
                # `test_coercion_with_a_typed_sibling_is_not_flagged`, and
                # including it would make an over-flagging mutation kill two
                # tests instead of naming the one guard it removed.
                ("F:fixture-clean", CLEAN),
                ("F:fixture-ascribed", ASCRIBED_LAMBDA),
            ]
        )
        self.assertEqual(0, completed.returncode, completed.stdout + completed.stderr)


class LedgerCoverage(unittest.TestCase):
    """The screen must actually reach the mirror population, not just fixtures.

    An empty result from a tool never pointed at its subject is indistinguishable
    from a strong negative, so this confirms COVERAGE: the ledger carries mirrors,
    the screen reads their statements, and the classes it emits are the declared
    ones.
    """

    def test_the_screen_reads_the_mirror_population(self) -> None:
        import json

        facts = sorted((ROOT / "artifacts" / "facts").glob("F-ml430-*.json"))
        self.assertGreater(len(facts), 100, "the mirror population is missing")
        seen = 0
        for path in facts:
            statement = (json.loads(path.read_text(encoding="utf-8")).get("formal") or {}).get(
                "statement"
            )
            if not isinstance(statement, str):
                continue
            seen += 1
            for finding in screen_statement(statement):
                self.assertIn(
                    finding.screen_class, {"elided-proof-glyph", "variable-block-dropped"}
                )
        self.assertGreater(seen, 100, "no mirror statement was read")


if __name__ == "__main__":
    unittest.main()
