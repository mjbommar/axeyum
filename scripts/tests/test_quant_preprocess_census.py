"""Focused tests for `scripts/quant-preprocess-census.py` (ADR-2127).

Same style as `scripts/tests/test_strip_quantified_assertions.py`: synthetic
SMT-LIB text, no subprocess, no corpus dependency.

Two of these tests are the census's SOUNDNESS-NEGATIVE controls, and they are
the reason this file exists rather than a handful of spot checks:

  * `test_occurs_check_refuses_recursive_definition` -- `∀x. f(x) = g(f(x))`
    is NOT a definition of `f`; a census that counted it would size a pass
    that, if built to that size, would inline a non-terminating rewrite.
  * `test_partial_coverage_is_not_a_macro` -- `∀x. f(x, c) = t` constrains
    `f` only on the slice `y = c`. Inlining it at `f(a, b)` is UNSOUND: it
    would turn a satisfiable query unsat.

Both are stated as counts that must be ZERO in the macro column and NONZERO
in the corresponding rejection column, so a mutation that drops the guard
changes the assertion rather than leaving it vacuously true.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "quant-preprocess-census.py"
SPEC = importlib.util.spec_from_file_location("quant_preprocess_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def census(text: str):
    return MODULE.census_text("TEST", "t.smt2", text).row


PRELUDE = (
    "(declare-fun f (Int) Int)\n"
    "(declare-fun g (Int) Int)\n"
    "(declare-fun h (Int Int) Int)\n"
    "(declare-fun p (Int) Bool)\n"
    "(declare-fun c () Int)\n"
    "(declare-fun q () Bool)\n"
)


class MacroPositiveControlTests(unittest.TestCase):
    """The POSITIVE control. Every negative below is only evidence because
    this one passes: a census that found no macro anywhere would make every
    `macro_def == 0` assertion vacuous."""

    def test_simple_definitional_macro_is_found(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (f x) (+ x 1))))\n")
        self.assertEqual(row["macro_def"], 1)
        self.assertEqual(row["macro_def_distinct"], 1)
        self.assertEqual(row["macro_reject_occurs"], 0)
        self.assertEqual(row["macro_reject_coverage"], 0)

    def test_macro_head_on_the_right_is_found(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (+ x 1) (f x))))\n")
        self.assertEqual(row["macro_def"], 1)

    def test_two_argument_macro_is_found(self) -> None:
        row = census(
            PRELUDE + "(assert (forall ((x Int) (y Int)) (= (h x y) (+ x y))))\n"
        )
        self.assertEqual(row["macro_def"], 1)

    def test_negated_boolean_equality_macro_is_found(self) -> None:
        """`∀x. ¬(p(x) = φ)` is `p(x) ↔ ¬φ`; z3 has an explicit branch for it
        at `macro_util.cpp:187-193`."""
        row = census(PRELUDE + "(assert (forall ((x Int)) (not (= (p x) (< x 0)))))\n")
        self.assertEqual(row["macro_def"], 1)

    def test_pattern_annotation_does_not_hide_the_macro(self) -> None:
        row = census(
            PRELUDE
            + "(assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))\n"
        )
        self.assertEqual(row["macro_def"], 1)

    def test_distinct_heads_are_counted_once_each(self) -> None:
        row = census(
            PRELUDE
            + "(assert (forall ((x Int)) (= (f x) (+ x 1))))\n"
            + "(assert (forall ((x Int)) (= (g x) (* x 2))))\n"
        )
        self.assertEqual(row["macro_def"], 2)
        self.assertEqual(row["macro_def_distinct"], 2)


class MacroSoundnessNegativeTests(unittest.TestCase):
    def test_occurs_check_refuses_recursive_definition(self) -> None:
        """`∀x. f(x) = g(f(x))` -- `f` occurs in its own body. Not a macro."""
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (f x) (g (f x)))))\n")
        self.assertEqual(row["macro_def"], 0)
        self.assertEqual(row["macro_reject_occurs"], 1)

    def test_occurs_check_looks_inside_a_let_binding_value(self) -> None:
        """A head hiding in a dead `let` binding still refuses the macro: the
        occurs check is a whole-subtree scan, not a walk of the body only."""
        row = census(
            PRELUDE
            + "(assert (forall ((x Int)) (= (f x) (let ((z (f x))) (+ x 1)))))\n"
        )
        self.assertEqual(row["macro_def"], 0)
        self.assertEqual(row["macro_reject_occurs"], 1)

    def test_partial_coverage_is_not_a_simple_macro(self) -> None:
        """`∀x. h(x, c) = t` defines `h` only on the slice where its second
        argument is `c`. Inlining that at `h(a, b)` would be UNSOUND -- it can
        turn a satisfiable query unsat -- so `is_macro_head` refuses it
        (arity/coverage, `macro_util.cpp:143-152`). It IS a legal QUASI-macro,
        and the difference is the whole point: the quasi path never
        substitutes, it emits `f(v̄) = ite(guard, t, f_else(v̄))`
        (`quasi_macros.cpp:259-270`), leaving `f` unconstrained off the
        slice."""
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (h x c) (+ x 1))))\n")
        self.assertEqual(row["macro_def"], 0)
        self.assertEqual(row["macro_reject_coverage"], 1)
        self.assertEqual(row["macro_quasi"], 1)

    def test_repeated_variable_argument_is_not_a_macro(self) -> None:
        """`∀x. h(x, x) = t` constrains only the diagonal."""
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (h x x) (+ x 1))))\n")
        self.assertEqual(row["macro_def"], 0)

    def test_binder_variable_not_reachable_from_the_head_is_not_a_macro(self) -> None:
        """`∀x y. f(x) = y` -- `y` is universal over the BODY, so the
        assertion is a constraint on `f`, not a definition."""
        row = census(PRELUDE + "(assert (forall ((x Int) (y Int)) (= (f x) y)))\n")
        self.assertEqual(row["macro_def"], 0)

    def test_theory_symbol_head_is_not_a_macro(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (+ x x) (* 2 x))))\n")
        self.assertEqual(row["macro_def"], 0)

    def test_define_fun_name_is_already_a_macro_and_is_not_recounted(self) -> None:
        row = census(
            "(define-fun d ((x Int)) Int (+ x 1))\n"
            "(assert (forall ((x Int)) (= (d x) (+ x 1))))\n"
        )
        self.assertEqual(row["macro_def"], 0)

    def test_datatype_constructor_head_is_interpreted_and_is_not_a_macro(self) -> None:
        row = census(
            "(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))\n"
            "(declare-fun k (Int) Int)\n"
            "(assert (forall ((x Int)) (= (fst (mk x x)) x)))\n"
        )
        self.assertEqual(row["macro_def"], 0)


class UnitLiteralTests(unittest.TestCase):
    """z3's `macro_finder` does NOT recognize `∀x̄. f(x̄)` / `∀x̄. ¬f(x̄)`; only
    `quasi_macros::is_quasi_macro` does (`quasi_macros.cpp:176-186`). Counting
    them as simple macros would attribute to the macro finder a rewrite it
    never performs, so they get their own column."""

    def test_boolean_unit_literal_is_a_unit_macro_not_a_simple_macro(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (p x)))\n")
        self.assertEqual(row["macro_unit"], 1)
        self.assertEqual(row["macro_def"], 0)

    def test_negated_boolean_unit_literal_is_a_unit_macro(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (not (p x))))\n")
        self.assertEqual(row["macro_unit"], 1)
        self.assertEqual(row["macro_def"], 0)


class QuasiMacroTests(unittest.TestCase):
    def test_repeated_variable_head_is_a_quasi_macro(self) -> None:
        """`∀x. h(x, x) = t` -- not a simple macro (the args are not
        distinct), but every binder variable IS a bare direct argument, so
        `fully_depends_on` accepts it and the guarded rewrite applies."""
        row = census(PRELUDE + "(assert (forall ((x Int)) (= (h x x) (+ x 1))))\n")
        self.assertEqual(row["macro_quasi"], 1)
        self.assertEqual(row["macro_def"], 0)

    def test_buried_variable_does_not_cover_it(self) -> None:
        """z3's `fully_depends_on` (`quasi_macros.cpp:110-116`) counts only
        BARE argument variables. `∀x y. h(x, g(y)) = t` leaves `y` uncovered,
        so z3 refuses it -- the weaker "occurs somewhere deep down" version is
        commented out at `quasi_macros.cpp:102-104`."""
        row = census(
            PRELUDE
            + "(assert (forall ((x Int) (y Int)) (= (h x (g y)) (+ x y))))\n"
        )
        self.assertEqual(row["macro_quasi"], 0)

    def test_quasi_macro_occurs_check_applies(self) -> None:
        row = census(
            PRELUDE + "(assert (forall ((x Int)) (= (h x x) (h 1 x))))\n"
        )
        self.assertEqual(row["macro_quasi"], 0)

    def test_is_unique_refuses_a_head_used_twice_non_ground(self) -> None:
        """`is_unique` (`quasi_macros.cpp:80-82`): `f` must have EXACTLY ONE
        non-ground occurrence in the whole problem. A second use elsewhere
        makes the guarded rewrite unsound to apply as a definition."""
        row = census(
            PRELUDE
            + "(assert (forall ((x Int)) (= (h x x) (+ x 1))))\n"
            + "(assert (forall ((y Int)) (> (h y y) 0)))\n"
        )
        self.assertEqual(row["macro_quasi"], 0)


class SkolemPolarityTests(unittest.TestCase):
    def test_negated_universal_at_top_level_is_a_skolem_position(self) -> None:
        """The SPARK goal convention, and the dominant shape in this corpus.
        It reaches the quantifier through one `not` -- which is what MAKES it
        an existential -- so it is TOP, not "under a conjunction"."""
        row = census(PRELUDE + "(assert (not (forall ((x Int)) (p x))))\n")
        self.assertEqual(row["sk_top"], 1)
        self.assertEqual(row["sk_conj"], 0)
        self.assertEqual(row["sk_needs_function"], 0)

    def test_bare_existential_assertion_is_a_skolem_position(self) -> None:
        row = census(PRELUDE + "(assert (exists ((x Int)) (p x)))\n")
        self.assertEqual(row["sk_top"], 1)

    def test_positive_universal_is_not_a_skolem_position(self) -> None:
        row = census(PRELUDE + "(assert (forall ((x Int)) (p x)))\n")
        self.assertEqual(row["sk_top"] + row["sk_conj"] + row["sk_deep"], 0)

    def test_negated_existential_is_not_a_skolem_position(self) -> None:
        row = census(PRELUDE + "(assert (not (exists ((x Int)) (p x))))\n")
        self.assertEqual(row["sk_top"] + row["sk_conj"] + row["sk_deep"], 0)

    def test_under_a_top_level_conjunction_counts_as_conj(self) -> None:
        row = census(
            PRELUDE
            + "(assert (and q (not (forall ((x Int)) (p x)))))\n"
        )
        self.assertEqual(row["sk_conj"], 1)
        self.assertEqual(row["sk_deep"], 0)

    def test_under_a_disjunction_counts_as_deep_not_conj(self) -> None:
        row = census(
            PRELUDE + "(assert (or q (not (forall ((x Int)) (p x)))))\n"
        )
        self.assertEqual(row["sk_conj"], 0)
        self.assertEqual(row["sk_deep"], 1)

    def test_implication_antecedent_flips_polarity(self) -> None:
        """In `(=> (forall ...) q)` the universal is at NEGATIVE polarity, so
        it IS an existential position; in the consequent it is not."""
        row = census(PRELUDE + "(assert (=> (forall ((x Int)) (p x)) q))\n")
        self.assertEqual(row["sk_deep"], 1)
        row2 = census(PRELUDE + "(assert (=> q (forall ((x Int)) (p x))))\n")
        self.assertEqual(row2["sk_deep"], 0)

    def test_enclosing_universal_forces_a_skolem_function(self) -> None:
        """`∀x. ∃y. p(y)` -- the witness for `y` depends on `x`, so it must be
        a Skolem FUNCTION of `x`, never a constant. Getting this wrong is the
        classic unsoundness in a hand-rolled skolemizer."""
        row = census(
            PRELUDE
            + "(assert (forall ((x Int)) (exists ((y Int)) (= (f y) x))))\n"
        )
        self.assertEqual(row["sk_deep"], 1)
        self.assertEqual(row["sk_needs_function"], 1)

    def test_no_enclosing_universal_means_a_skolem_constant(self) -> None:
        row = census(PRELUDE + "(assert (exists ((y Int)) (= (f y) c)))\n")
        self.assertEqual(row["sk_top"], 1)
        self.assertEqual(row["sk_needs_function"], 0)

    def test_quantifier_reachable_only_through_a_let_value_is_not_counted(self) -> None:
        """This corpus nests `let` hundreds deep; a let-bound Boolean has no
        single polarity without expanding the binding. Counted separately and
        NOT as a skolemizable position -- the census under-counts on purpose."""
        row = census(
            PRELUDE
            + "(assert (let ((b (not (forall ((x Int)) (p x))))) (and b q)))\n"
        )
        self.assertEqual(row["sk_under_let"], 1)
        self.assertEqual(row["sk_top"] + row["sk_conj"] + row["sk_deep"], 0)

    def test_boolean_equality_has_no_provable_polarity(self) -> None:
        row = census(
            PRELUDE + "(assert (= q (not (forall ((x Int)) (p x)))))\n"
        )
        self.assertEqual(row["sk_top"] + row["sk_conj"] + row["sk_deep"], 0)


class DriverTests(unittest.TestCase):
    def test_empty_list_is_reported_as_a_failure_not_as_zero(self) -> None:
        """An empty census is indistinguishable from a strong negative, so it
        must exit non-zero rather than write a zero-row TSV."""
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            lst = Path(td) / "empty.list"
            lst.write_text("", encoding="utf-8")
            rc = MODULE.main(
                [
                    "--corpus-root",
                    td,
                    "--division",
                    "TEST",
                    "--list",
                    str(lst),
                    "--out-tsv",
                    str(Path(td) / "out.tsv"),
                ]
            )
        self.assertEqual(rc, 2)

    def test_missing_file_is_a_parse_failure_and_exits_nonzero(self) -> None:
        import tempfile

        with tempfile.TemporaryDirectory() as td:
            good = Path(td) / "a.smt2"
            good.write_text(PRELUDE + "(assert (forall ((x Int)) (= (f x) x)))\n", encoding="utf-8")
            lst = Path(td) / "l.list"
            lst.write_text("a.smt2\nmissing.smt2\n", encoding="utf-8")
            rc = MODULE.main(
                [
                    "--corpus-root",
                    td,
                    "--division",
                    "TEST",
                    "--list",
                    str(lst),
                    "--out-tsv",
                    str(Path(td) / "out.tsv"),
                ]
            )
        self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
