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


def collision_source(*labels: str) -> str:
    """A minimal `cross_prelude_collision_tests.rs`-shaped source fragment:
    one `Group { label: "...", ... }` literal per label, the only shape
    `collision_group_labels` reads."""
    return "\n".join(f'    Group {{ label: "{label}", all: names }}' for label in labels)


class GroupLabelAgreementTests(unittest.TestCase):
    """Tests for `check_group_labels`, `kdp_prelude_labels`,
    `pti_prelude_labels` and `collision_group_labels` -- the three-way guard
    added alongside the theorem-name comparison above, for the identical gap
    found in `cross_prelude_collision_tests.rs`'s OWN `build_groups`: it too
    never called `build_characterization`, so `characterization` had never
    been checked for a cross-prelude name collision (a different question
    from the theorem-name comparison `check()` answers -- collision-checking
    spans every `Declaration` kind, not only theorems)."""

    def test_all_three_agreeing_passes(self) -> None:
        kdp = "\n".join([kdp_row("nat", "theorem", "Nat.add_comm")])
        pti = "\n".join([pti_row("nat", "Nat.add_comm")])
        source = collision_source("nat")
        count = MODULE.check_group_labels(
            MODULE.kdp_prelude_labels(kdp),
            MODULE.pti_prelude_labels(pti),
            MODULE.collision_group_labels(source),
        )
        self.assertEqual(count, 1)

    def test_collision_tests_missing_a_group_is_caught(self) -> None:
        # Reproduces the actual defect this guard exists for: kdp/pti both
        # build `characterization`, but `cross_prelude_collision_tests.rs`'s
        # own `build_groups` never calls `build_characterization`.
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("characterization", "theorem", "Nat.Peano.zero_ne_succ"),
            ]
        )
        pti = "\n".join(
            [
                pti_row("nat", "Nat.add_comm"),
                pti_row("characterization", "Nat.Peano.zero_ne_succ"),
            ]
        )
        source = collision_source("nat")  # "characterization" omitted
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check_group_labels(
                MODULE.kdp_prelude_labels(kdp),
                MODULE.pti_prelude_labels(pti),
                MODULE.collision_group_labels(source),
            )
        message = str(ctx.exception)
        self.assertIn("'characterization'", message)
        self.assertIn("MISSING from ['cross_prelude_collision_tests']", message)

    def test_kdp_missing_a_group_is_also_caught(self) -> None:
        # The reverse direction: cross_prelude_collision_tests/pti both build
        # a group kdp does not -- must fail too, naming kdp as the gap.
        kdp = "\n".join([kdp_row("nat", "theorem", "Nat.add_comm")])
        pti = "\n".join(
            [
                pti_row("nat", "Nat.add_comm"),
                pti_row("characterization", "Nat.Peano.zero_ne_succ"),
            ]
        )
        source = collision_source("nat", "characterization")
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check_group_labels(
                MODULE.kdp_prelude_labels(kdp),
                MODULE.pti_prelude_labels(pti),
                MODULE.collision_group_labels(source),
            )
        message = str(ctx.exception)
        self.assertIn("'characterization'", message)
        self.assertIn("MISSING from ['kernel_declaration_projection']", message)

    def test_pti_missing_a_group_is_also_caught(self) -> None:
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("characterization", "theorem", "Nat.Peano.zero_ne_succ"),
            ]
        )
        pti = "\n".join([pti_row("nat", "Nat.add_comm")])
        source = collision_source("nat", "characterization")
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check_group_labels(
                MODULE.kdp_prelude_labels(kdp),
                MODULE.pti_prelude_labels(pti),
                MODULE.collision_group_labels(source),
            )
        message = str(ctx.exception)
        self.assertIn("'characterization'", message)
        self.assertIn("MISSING from ['prelude_theorem_inventory']", message)

    def test_negative_control_labels_do_not_mask_a_real_gap(self) -> None:
        # negative_control's synthetic `Group` literals reuse a SUBSET of
        # build_groups's real labels (logic/nat/axreal) -- confirms that
        # scanning the whole file cannot manufacture a false agreement by
        # having negative_control "supply" a label build_groups itself is
        # missing (negative_control never mentions "characterization").
        kdp = "\n".join(
            [
                kdp_row("nat", "theorem", "Nat.add_comm"),
                kdp_row("characterization", "theorem", "Nat.Peano.zero_ne_succ"),
            ]
        )
        pti = "\n".join(
            [
                pti_row("nat", "Nat.add_comm"),
                pti_row("characterization", "Nat.Peano.zero_ne_succ"),
            ]
        )
        # build_groups has "nat" only; negative_control separately mentions
        # "nat" and "axreal" (its own fixture), neither of which is
        # "characterization".
        source = collision_source("nat") + "\n" + collision_source("nat", "axreal")
        with self.assertRaises(MODULE.CompletenessError) as ctx:
            MODULE.check_group_labels(
                MODULE.kdp_prelude_labels(kdp),
                MODULE.pti_prelude_labels(pti),
                MODULE.collision_group_labels(source),
            )
        self.assertIn("'characterization'", str(ctx.exception))

    def test_empty_collision_source_is_an_error_not_a_silent_pass(self) -> None:
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.collision_group_labels("")

    def test_collision_source_with_no_label_literals_is_an_error(self) -> None:
        # The shape changed (or the file is garbage) -- must fail loudly,
        # not silently report "collision tests cover zero preludes" as if
        # that were a measurement.
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.collision_group_labels("struct Group { name: &'static str }")

    def test_constructor_shape_is_recognised(self) -> None:
        # `cross_prelude_collision_tests.rs` was refactored from the
        # `Group { label: "..." }` struct literal to a `Group::of("...", &k)`
        # constructor, and the label regex matched ZERO occurrences afterwards
        # -- so this checker was hard red from the refactor until 2026-08-31,
        # unnoticed because it is registered in no aggregate gate. Both shapes
        # are accepted now, and this pins the constructor half: without it the
        # widening is untested and could be reverted with everything green.
        source = (
            'groups.push(Group::of("logic", &logic));\n'
            'groups.push(Group::of("nat", &nat));\n'
        )
        self.assertEqual(
            MODULE.collision_group_labels(source), {"logic", "nat"}
        )

    def test_both_shapes_together_are_recognised(self) -> None:
        # A file mid-refactor carrying both shapes must yield the union, not
        # whichever one the regex happens to try first.
        source = (
            'Group { label: "axreal", all: Default::default() }\n'
            'groups.push(Group::of("rat", &rat));\n'
        )
        self.assertEqual(
            MODULE.collision_group_labels(source), {"axreal", "rat"}
        )

    def test_empty_kdp_prelude_labels_is_an_error(self) -> None:
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.kdp_prelude_labels("")

    def test_empty_pti_prelude_labels_is_an_error(self) -> None:
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.pti_prelude_labels("")

    def test_malformed_kdp_row_is_an_error_for_prelude_labels_too(self) -> None:
        text = "\n".join(
            [kdp_row("nat", "theorem", "Nat.add_comm"), "only\tfour\tfields\there"]
        )
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.kdp_prelude_labels(text)

    def test_malformed_pti_row_is_an_error_for_prelude_labels_too(self) -> None:
        text = "\n".join([pti_row("nat", "Nat.add_comm"), "onlyonefield"])
        with self.assertRaises(MODULE.CompletenessError):
            MODULE.pti_prelude_labels(text)


if __name__ == "__main__":
    unittest.main()
