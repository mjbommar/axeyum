"""Guards on ADR-1971's sizing instrument.

`scripts/nested_array_outer_row_surrogate.py` is the rewrite that ADR-1971's
"outer read-over-write is worth zero" rests on.  Its number is only as good
as two properties:

* the **expansion** is the read-over-write axiom, guard and all.  A rewrite in
  which the stored row always wins would turn satisfiable files into surrogate
  `unsat` and the reach would count refutations of true statements.
* the **refusals** are exhaustive.  Every context in which an outer array is
  something other than the base of a read must be refused, because the currying
  silently drops outer extensionality and a file that needs it would otherwise
  be measured as if it did not.

Each test below corresponds to one guard in the subject, and
`scripts/tests/mutation_controls.py` (suite `outer-row-surrogate`) deletes
those guards one at a time and requires that **exactly one** of these dies.

These are shape checks, not solver runs -- the solver-in-the-loop controls are
`bench-results/nested-array-outer-row-20260913/controls/run-controls.sh`, which
needs the CLI, z3 and cvc5 and so cannot live in a unit suite.  The two are
complementary: this file says the rewrite is what it claims, that one says the
instrument reaches something.
"""

import importlib.util
import pathlib
import unittest

SUBJECT = (pathlib.Path(__file__).resolve().parents[1]
           / "nested_array_outer_row_surrogate.py")


def _load():
    spec = importlib.util.spec_from_file_location("outer_row_surrogate", SUBJECT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


S = _load()


def rewrite(src, **kw):
    return S.rewrite(src, **kw)


def refusal(src):
    """Returns the refusal reason, or None if the source was accepted."""
    try:
        rewrite(src)
    except S.Refused as e:
        return str(e)
    return None


NESTED = "(declare-fun M () (Array Int (Array Int Int)))"
SCALARS = ("(declare-fun i () Int) (declare-fun j () Int) "
           "(declare-fun o () Int) (declare-fun r () (Array Int Int))")


class ExpansionIsTheAxiom(unittest.TestCase):
    """The read-over-write expansion must carry its index guard."""

    def test_an_outer_store_expands_to_a_GUARDED_ite(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (= 0 (select (select (store M i r) j) o)))"
                      f" (check-sat)")
        # The guard is the whole soundness argument: without `(= i j)` the
        # stored row would be returned at every index.
        self.assertIn("(ite (= i j)", out,
                      "the expansion lost its index guard, so a write at one "
                      "outer index is visible at every other -- every "
                      "satisfiable file would become surrogate `unsat`")
        self.assertIn("r", out, "the stored row vanished from the expansion")
        self.assertNotIn("(store", out,
                         "the outer store survived; nothing was expanded")

    def test_the_else_branch_reads_the_curried_row(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (= 0 (select (select (store M i r) j) o)))"
                      f" (check-sat)")
        self.assertIn("|M..row| j", out,
                      "the else branch does not read the curried outer row, so "
                      "the unwritten indices are unconstrained and the "
                      "surrogate is weaker than the original in a way the "
                      "one-directional argument does not cover")

    def test_the_outer_array_becomes_a_FUNCTION_declaration(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (= 0 (select (select M j) o)))"
                      f" (check-sat)")
        self.assertIn("(declare-fun |M..row| (Int) (Array Int Int))", out)
        self.assertNotIn("(Array Int (Array Int Int))", out,
                         "a nested array sort survived the currying")


class RefusalsAreExhaustive(unittest.TestCase):
    """Every context that needs an axiom currying does not have is refused."""

    def test_an_equality_between_outer_arrays_is_refused(self):
        why = refusal(f"(set-logic ALIA) {NESTED}"
                      f" (declare-fun N () (Array Int (Array Int Int)))"
                      f" (assert (= M N)) (check-sat)")
        self.assertIsNotNone(
            why, "an outer array equality was ACCEPTED. Currying drops outer "
                 "extensionality, so this file would be measured as if that "
                 "axiom were not needed")
        self.assertIn("non-read position", why)

    def test_a_store_whose_result_is_compared_is_refused(self):
        why = refusal(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (declare-fun N () (Array Int (Array Int Int)))"
                      f" (assert (= (store M i r) N)) (check-sat)")
        self.assertIsNotNone(why, "an outer store reached an equality")
        self.assertIn("non-read position", why)

    def test_a_quantifier_over_an_outer_array_is_refused(self):
        why = refusal(f"(set-logic ALIA) {NESTED}"
                      f" (assert (forall ((w (Array Int (Array Int Int))))"
                      f"   (= 0 (select (select w 0) 0)))) (check-sat)")
        self.assertIsNotNone(why, "a quantified outer array was accepted; "
                                  "currying has no sort to bind it to")
        self.assertIn("OUTER array variable", why)

    def test_an_outer_array_as_a_function_argument_is_refused(self):
        why = refusal(f"(set-logic ALIA) {NESTED}"
                      f" (declare-fun p ((Array Int (Array Int Int))) Bool)"
                      f" (assert (p M)) (check-sat)")
        self.assertIsNotNone(why, "an outer array reached a function argument; "
                                  "this is AUFLIRA's shape and it is why the "
                                  "instrument refuses 187/187 there")
        self.assertIn("outer array argument", why)

    def test_nesting_deeper_than_two_is_refused(self):
        why = refusal("(set-logic ALIA)"
                      " (declare-fun M () (Array Int (Array Int (Array Int Int))))"
                      " (assert (= 0 (select (select (select M 0) 0) 0)))"
                      " (check-sat)")
        self.assertIsNotNone(why, "a triply nested sort was curried one level "
                                  "and the rest measured as if it were flat")
        self.assertIn("nests 3 deep", why)

    def test_a_file_with_no_outer_array_is_refused(self):
        why = refusal("(set-logic ALIA) (declare-fun m () (Array Int Int))"
                      " (assert (= 0 (select m 0))) (check-sat)")
        self.assertIsNotNone(
            why, "a file with no nested array was ACCEPTED, so it would be "
                 "counted in the reach denominator as a nested-array file the "
                 "instrument spoke about")
        self.assertIn("no outer array declaration", why)


class LetInliningIsExactAndScoped(unittest.TestCase):
    """The `let` inlining buys 2 ALIA files; these are its price."""

    def test_a_let_bound_outer_store_is_inlined_not_refused(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (let ((a (store M i r)))"
                      f"   (= 0 (select (select a 0) o)))) (check-sat)")
        self.assertIn("(ite (= i 0)", out,
                      "the alias was not resolved through the read-over-write "
                      "expansion")

    def test_an_inlined_alias_used_as_a_bare_value_is_still_refused(self):
        why = refusal(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (declare-fun N () (Array Int (Array Int Int)))"
                      f" (assert (let ((a (store M i r))) (= a N))) (check-sat)")
        self.assertIsNotNone(
            why, "inlining opened a hole the direct form does not have: an "
                 "outer array compared for equality, which needs outer "
                 "extensionality")
        self.assertIn("non-read position", why)

    def test_a_binder_shadows_an_inlined_alias(self):
        # `a` is bound by the quantifier, so the alias must not leak into the
        # body -- capturing it would constrain a variable the original leaves
        # free and could turn a satisfiable file into surrogate `unsat`.
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (let ((a (store M i r)))"
                      f"   (forall ((a Int)) (> a (select (select M 0) o)))))"
                      f" (check-sat)")
        self.assertIn("(> a ", out,
                      "the quantified `a` was replaced by the outer alias, "
                      "which is variable capture")

    def test_inlining_that_explodes_is_refused_rather_than_measured(self):
        # A cap that never fires is not a cap; this drives it.
        saved = S.Surrogate.MAX_GROWTH
        try:
            S.Surrogate.MAX_GROWTH = 1
            why = refusal(f"(set-logic ALIA) {NESTED} {SCALARS}"
                          f" (assert (let ((a (store M i r)))"
                          f"   (and (= 0 (select (select a 0) o))"
                          f"        (= 0 (select (select a 1) o))"
                          f"        (= 0 (select (select a 2) o))))) (check-sat)")
            self.assertIsNotNone(
                why, "the growth cap did not fire, so a blow-up this "
                     "instrument caused would be measured as a timeout of the "
                     "solver")
            self.assertIn("grew the file", why)
        finally:
            S.Surrogate.MAX_GROWTH = saved


class DistributeIsSeparateAndOptional(unittest.TestCase):
    """`--distribute` is a second instrument, not part of the surrogate."""

    def test_plain_leaves_the_array_sorted_ite_under_the_select(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (= 0 (select (select (store M i r) j) o)))"
                      f" (check-sat)")
        self.assertIn("(select (ite", out,
                      "the plain arm already distributed, so the sweep's two "
                      "arms measure the same thing and the +0 delta is vacuous")

    def test_distribute_pushes_the_select_through(self):
        out = rewrite(f"(set-logic ALIA) {NESTED} {SCALARS}"
                      f" (assert (= 0 (select (select (store M i r) j) o)))"
                      f" (check-sat)", distribute=True)
        self.assertNotIn("(select (ite", out)
        self.assertIn("(ite ", out, "the ite itself was dropped, not moved")


if __name__ == "__main__":
    unittest.main()
