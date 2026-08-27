"""Tests for `scripts/check-theorem-inventory-completeness.py`.

These exercise the comparison logic against synthetic TSV text -- the same
shapes `kernel_declaration_projection` and `prelude_theorem_inventory` print
-- so the check is verified without a `--release` cargo build of the whole
constructed universe. `test_kdp_only_theorem_is_caught` reproduces the actual
2026-08-27 defect this script exists to catch (see that script's module doc).
"""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_SPEC = importlib.util.spec_from_file_location(
    "check_theorem_inventory_completeness",
    ROOT / "scripts" / "check-theorem-inventory-completeness.py",
)
assert _SPEC is not None and _SPEC.loader is not None
MODULE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(MODULE)


def kdp_row(prelude: str, kind: str, name: str) -> str:
    return "\t".join([prelude, kind, name, "0", "", "", "", "Prop"])


def pti_row(label: str, name: str) -> str:
    return "\t".join([label, name, "0", ""])


class AgreementTests(unittest.TestCase):
    def test_identical_sets_pass(self) -> None:
        kdp = "\n".join([kdp_row("nat", "theorem", "Nat.add_comm")])
        pti = "\n".join([pti_row("nat", "Nat.add_comm")])
        kdp_count, pti_count = MODULE.check(kdp, pti)
        self.assertEqual(kdp_count, 1)
        self.assertEqual(pti_count, 1)

    def test_kdp_only_theorem_is_caught(self) -> None:
        # Reproduces the actual 2026-08-27 defect: a theorem
        # kernel_declaration_projection sees (via build_characterization) that
        # prelude_theorem_inventory's build_groups never built.
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("characterization", "theorem", "Nat.Peano.zero_ne_succ"),
            ]
        )
        pti = "\n".join([pti_row("nat", "Nat.add_comm")])
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check(kdp, pti)
        self.assertIn("Nat.Peano.zero_ne_succ", str(ctx.exception))
        self.assertIn("kernel_declaration_projection only", str(ctx.exception))

    def test_pti_only_theorem_is_also_caught(self) -> None:
        # The opposite direction must fail too -- either tool omitting a
        # group is the same defect class.
        kdp = "\n".join([kdp_row("nat", "theorem", "Nat.add_comm")])
        pti = "\n".join(
            [
                pti_row("nat", "Nat.add_comm"),
                pti_row("nat", "Nat.phantom_theorem"),
            ]
        )
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check(kdp, pti)
        self.assertIn("Nat.phantom_theorem", str(ctx.exception))
        self.assertIn("prelude_theorem_inventory only", str(ctx.exception))

    def test_kdp_non_theorem_kinds_are_excluded_from_the_comparison(self) -> None:
        # A Definition present in kdp but absent from pti (which never emits
        # non-theorem rows) must NOT be reported as a disagreement -- that
        # exclusion is documented and deliberate (prelude_theorem_inventory's
        # own module doc), not the defect this check exists to catch.
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("nat", "definition", "Nat.add"),
                kdp_row("nat", "axiom", "Nat.some_axiom"),
            ]
        )
        pti = "\n".join([pti_row("nat", "Nat.add_comm")])
        kdp_count, pti_count = MODULE.check(kdp, pti)
        self.assertEqual(kdp_count, 1)
        self.assertEqual(pti_count, 1)

    def test_duplicate_rows_across_nested_preludes_are_deduplicated(self) -> None:
        # A theorem the tools' cumulative preludes both print more than once
        # (e.g. a Nat theorem visible from both `nat` and `integer`) must
        # count once, not be flagged as a disagreement.
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("integer", "theorem", "Nat.add_comm"),
            ]
        )
        pti = "\n".join(
            [
                pti_row("nat", "Nat.add_comm"),
                pti_row("integer", "Nat.add_comm"),
            ]
        )
        kdp_count, pti_count = MODULE.check(kdp, pti)
        self.assertEqual(kdp_count, 1)
        self.assertEqual(pti_count, 1)

    def test_empty_kdp_input_is_an_error_not_a_silent_pass(self) -> None:
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.kdp_theorem_names("")

    def test_empty_pti_input_is_an_error_not_a_silent_pass(self) -> None:
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.pti_theorem_names("")

    def test_malformed_kdp_row_is_an_error(self) -> None:
        # A well-formed row is present too, so `names` is non-empty and the
        # "reported ZERO theorems" guard cannot be what raises here -- this
        # isolates the row-shape guard from the empty-result guard. Without
        # that well-formed row, a mutant that silently skips malformed rows
        # instead of rejecting them still "passes" by tripping the OTHER
        # guard on an empty result, which is exactly the false-kill this
        # project's mutation-testing notes warn about.
        text = "\n".join(
            [kdp_row("nat", "theorem", "Nat.add_comm"), "only\tfour\tfields\there"]
        )
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.kdp_theorem_names(text)

    def test_malformed_pti_row_is_an_error(self) -> None:
        # Same isolation as above, on the pti side.
        text = "\n".join([pti_row("nat", "Nat.add_comm"), "onlyonefield"])
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.pti_theorem_names(text)


if __name__ == "__main__":
    unittest.main()
