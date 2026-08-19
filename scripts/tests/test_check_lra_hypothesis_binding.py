"""Controls for `check-lra-hypothesis-binding.py`.

The checker's whole claim is that a mis-transcribed constraint cannot reach a
Lean module unnoticed. On the committed corpus it reports 105 instances, 248
hypotheses and zero failures — which, on its own, is indistinguishable from a
function that returns 0.

So every guard is driven to failure here, on a module small enough to read in
full, and the *positive* control is driven too: a consistent global renaming of
the carriers is semantically harmless and must still pass. A checker that
rejects everything discriminates exactly as poorly as one that accepts
everything, and only the pair of tests can tell them apart.

Runs offline. No cargo, no Lean, no dumper binary.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_lra_hypothesis_binding", ROOT / "scripts" / "check-lra-hypothesis-binding.py"
)
assert SPEC and SPEC.loader
HB = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HB)


# A real query and a real module, trimmed to the parts the checker reads. The
# refutation: `s_b ≥ s_a + 5`, `s_a ≥ 6`, `s_b ≤ 9`.
QUERY = """
(set-logic QF_LRA)
(declare-fun s_a () Real)
(declare-fun s_b () Real)
(assert (! (>= s_b (+ s_a 5.0)) :named prec))
(assert (! (>= s_a 6.0) :named release))
(assert (! (<= s_b 9.0) :named deadline))
(check-sat)
"""

X0 = "axeyum.reconstruct.lra.x._0"
X1 = "axeyum.reconstruct.lra.x._1"

MODULE = f"""
axiom Real : Sort (1)
axiom Real.add : ((x0 : Real) -> ((x1 : Real) -> Real))
axiom Real.le : ((x0 : Real) -> ((x1 : Real) -> Prop))
axiom {X0} : Real
axiom {X1} : Real
axiom axeyum.reconstruct.lra.hyp._2 : Real.le (Real.add {X0} (Real.add (Real.neg {X1}) \
(Real.add Real.one (Real.add Real.one (Real.add Real.one (Real.add Real.one \
(Real.add Real.one Real.zero))))))) Real.zero
axiom axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add (Real.neg {X0}) (Real.add Real.one \
(Real.add Real.one (Real.add Real.one (Real.add Real.one (Real.add Real.one \
(Real.add Real.one Real.zero))))))) Real.zero
theorem axeyum_refutation : False := trivial
"""


def run(module: str, query: str = QUERY):
    """`(phi, hypotheses, allowed, detail)` for a module/query pair."""
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as handle:
        handle.write(query)
        path = pathlib.Path(handle.name)
    try:
        sorts, assertions = HB.read_query(path)
    finally:
        path.unlink()
    return HB.check_instance(module, list(range(len(assertions))), sorts, assertions)


def _as_int_module(module: str) -> str:
    """The same module over Lean's `Int`. The Int prelude carries NO axioms in a
    real rendered module (it is fully proved), so the Real prelude's declarations
    are dropped rather than translated — leaving the carriers and the hypotheses
    as the module's entire trusted base, which is what an `IntFarkas` module
    genuinely looks like."""
    kept = [
        line
        for line in module.splitlines()
        if not line.startswith("axiom Real")
    ]
    return (
        "\n".join(kept)
        .replace("Real", "Int")
        .replace("axeyum.reconstruct.lra.x._", "axeyum.reconstruct.lra.int_var._")
        .replace("axeyum.reconstruct.lra.hyp._", "axeyum.reconstruct.lra.int_hyp._")
    )


class TheFixtureItselfBinds(unittest.TestCase):
    """Without this, every failure test below could be passing for the wrong reason."""

    def test_the_pristine_module_binds_to_the_query(self) -> None:
        phi, hypotheses, _allowed, detail = run(MODULE)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(len(hypotheses), 2)
        # `s_b >= s_a + 5` really did render as `s_a - s_b + 5 <= 0`.
        self.assertEqual(phi[X0], "s_a")
        self.assertEqual(phi[X1], "s_b")


class NormalizationIsSemanticNotSyntactic(unittest.TestCase):
    """`x > 5` renders as `-x + 5 < 0`. If the two normalizers disagreed about
    that, the checker would reject every faithful module and get deleted."""

    def test_the_two_sides_agree_on_a_flipped_constraint(self) -> None:
        """`(>= s_a 6.0)` is rendered `-x + 1+1+1+1+1+1 <= 0`. No amount of string
        comparison relates those two; the whole checker rests on this equality."""
        smt = HB.atoms_of([">=", "s_a", "6.0"], True, {})
        rendered = HB.lean_atom(
            f"Real.le (Real.add (Real.neg {X0}) (Real.add Real.one (Real.add Real.one "
            "(Real.add Real.one (Real.add Real.one (Real.add Real.one (Real.add Real.one "
            "Real.zero))))))) Real.zero",
            "Real",
        )
        self.assertEqual(smt, [("<=", ((("s_a",), -1),), 6)])
        self.assertEqual(HB.signature(smt[0]), HB.signature(rendered))

    def test_a_leaf_outside_the_query_namespace_is_not_silently_a_variable(self) -> None:
        """A rendered constant this checker does not know must not become a fresh
        free variable that then matches anything."""
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom("Real.le (Real.add v Real.zero) Real.zero", "Real")

    def test_scaling_by_a_positive_rational_is_the_same_atom(self) -> None:
        half = HB.canonical("<=", {("x",): Fraction(1, 2)}, Fraction(-3, 2))
        whole = HB.canonical("<=", {("x",): Fraction(2)}, Fraction(-6))
        self.assertEqual(half, whole)

    def test_scaling_by_a_negative_rational_is_NOT_the_same_atom(self) -> None:
        """`x ≤ 0` and `−x ≤ 0` are different facts, and a normalizer that
        divided by a signed gcd would fuse them."""
        self.assertNotEqual(
            HB.canonical("<=", {("x",): Fraction(1)}, Fraction(0)),
            HB.canonical("<=", {("x",): Fraction(-1)}, Fraction(0)),
        )


class ACorruptedTranscriptionIsCaught(unittest.TestCase):
    """One mis-rendered constraint per test, each the shape a renderer bug takes."""

    def _mutate_and_expect_rejection(self, old: str, new: str) -> str:
        damaged = MODULE.replace(old, new, 1)
        self.assertNotEqual(damaged, MODULE, "the mutation did not apply")
        phi, _hyps, _allowed, detail = run(damaged)
        self.assertIsNone(phi, "a corrupted transcription was accepted")
        return detail

    def test_a_flipped_relation(self) -> None:
        detail = self._mutate_and_expect_rejection(
            "axeyum.reconstruct.lra.hyp._2 : Real.le",
            "axeyum.reconstruct.lra.hyp._2 : Real.lt",
        )
        self.assertIn("hyp._2", detail)

    def test_a_dropped_negation(self) -> None:
        self._mutate_and_expect_rejection(f"(Real.neg {X1})", X1)

    def test_a_swapped_inequality(self) -> None:
        self._mutate_and_expect_rejection(
            "axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add (Real.neg "
            f"{X0})",
            "axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add ("
            f"{X0}",
        )

    def test_an_off_by_one_bound(self) -> None:
        self._mutate_and_expect_rejection(
            "(Real.add Real.one (Real.add Real.one (Real.add Real.one (Real.add Real.one "
            "(Real.add Real.one Real.zero)))))",
            "(Real.add Real.one (Real.add Real.one (Real.add Real.one (Real.add Real.one "
            "Real.zero))))",
        )

    def test_a_variable_renamed_in_one_hypothesis_only(self) -> None:
        self._mutate_and_expect_rejection(
            f"axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add (Real.neg {X0})",
            f"axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add (Real.neg {X1})",
        )

    def test_an_axiom_smuggled_in_under_an_unrelated_name(self) -> None:
        damaged = MODULE.replace(
            "theorem axeyum_refutation",
            "axiom convenient.premise : Real.le Real.one Real.zero\ntheorem axeyum_refutation",
        )
        phi, _hyps, _allowed, detail = run(damaged)
        self.assertIsNone(phi)
        self.assertIn("convenient.premise", detail)

    def test_a_carrier_declared_as_something_other_than_the_opaque_sort(self) -> None:
        damaged = MODULE.replace(f"axiom {X0} : Real", f"axiom {X0} : False")
        phi, _hyps, _allowed, detail = run(damaged)
        self.assertIsNone(phi)
        self.assertIn(X0, detail)

    def test_a_hypothesis_route_this_checker_does_not_model_is_not_waved_through(
        self,
    ) -> None:
        damaged = MODULE.replace(
            "theorem axeyum_refutation",
            "axiom axeyum.reconstruct.dio.hyp._9 : Nat.le Nat.zero Nat.zero\n"
            "theorem axeyum_refutation",
        )
        phi, _hyps, _allowed, detail = run(damaged)
        self.assertIsNone(phi)
        self.assertIn("dio.hyp._9", detail)


class AHarmlessRenamingIsNotCaught(unittest.TestCase):
    """The other direction. Without this pair, `return None` would pass every
    test above."""

    def test_a_consistent_global_renaming_of_the_carriers_still_binds(self) -> None:
        swapped = MODULE.replace(X0, "TMP").replace(X1, X0).replace("TMP", X1)
        phi, _hyps, _allowed, detail = run(swapped)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(phi[X1], "s_a")
        self.assertEqual(phi[X0], "s_b")

    def test_collapsing_two_carriers_into_one_is_caught(self) -> None:
        """The renaming that is NOT harmless: identifying two variables can make
        a satisfiable query look refuted, so φ must be injective.

        Asserted at BOTH layers. Injectivity is enforced twice — once as pruning
        inside the search, once in `verify_binding` — and a redundant pair like
        that is how six of seven guards in another suite of this repository
        turned out to be removable with everything still green: they all rejected
        through one shared check. So this pins that the SEARCH declines on its
        own; a `SEARCH DEFECT` here would mean the safety net caught what the
        search should have, which is a real regression wearing a passing test.
        """
        collapsed = MODULE.replace(X1, X0)
        phi, _hyps, _allowed, detail = run(collapsed)
        self.assertIsNone(phi)
        self.assertNotIn("SEARCH DEFECT", detail)

    def test_two_carriers_cannot_share_one_query_symbol(self) -> None:
        """Injectivity proper: two DISTINCT carriers both claiming the query's
        single `x ≤ 0` row. Nothing cancels and each hypothesis matches on its
        own, so only the one-to-one requirement rejects this — which is why the
        collapsing test above does not reach it (there the coefficients cancel
        and the atom is refused before injectivity is consulted).

        `SEARCH DEFECT` would mean the search returned the bad φ and only the
        re-check stopped it. Both layers must hold independently.
        """
        query = """
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (<= x 0))
        (assert (>= y 1))
        """
        module = f"""
axiom {X0} : Real
axiom {X1} : Real
axiom axeyum.reconstruct.lra.hyp._2 : Real.le (Real.add {X0} Real.zero) Real.zero
axiom axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add {X1} Real.zero) Real.zero
"""
        phi, _h, _a, detail = run(module, query)
        self.assertIsNone(phi)
        self.assertNotIn("SEARCH DEFECT", detail)

    def test_one_carrier_for_that_one_row_is_fine(self) -> None:
        """The twin: a single carrier claiming the single row binds."""
        query = """
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (assert (<= x 0))
        """
        module = f"""
axiom {X0} : Real
axiom axeyum.reconstruct.lra.hyp._2 : Real.le (Real.add {X0} Real.zero) Real.zero
"""
        phi, _h, _a, detail = run(module, query)
        self.assertIsNotNone(phi, detail)

    def test_an_int_carrier_cannot_borrow_a_real_symbol(self) -> None:
        """Same two-layer argument for sort-soundness. An `Int` carrier standing
        for a `Real`-declared symbol would let the module use integrality the
        query never granted — the direction that is NOT sound."""
        int_module = _as_int_module(MODULE)
        # Sanity: the carriers now declare `Int`, which is what `int_var` should,
        # so this test is about the SORT of the query symbols and not about a
        # mis-declared carrier.
        carriers, _hyps, unaccounted = HB.read_module(int_module)
        self.assertEqual(unaccounted, [])
        self.assertEqual(set(carriers.values()), {"Int"})
        phi, _h, _a, detail = run(int_module)  # QUERY declares s_a, s_b : Real
        self.assertIsNone(phi)
        self.assertNotIn("SEARCH DEFECT", detail)

    def test_the_same_module_binds_when_the_query_declares_them_Int(self) -> None:
        """And the positive twin, so the test above is not passing because an
        `Int` module never binds to anything."""
        int_query = (
            QUERY.replace("Real", "Int").replace("5.0", "5").replace("6.0", "6")
        )
        phi, _h, _a, detail = run(_as_int_module(MODULE), int_query)
        self.assertIsNotNone(phi, detail)


class TheSearchIsComplete(unittest.TestCase):
    """Regression for a defect found while this was being written: the first
    version committed to the first permutation inside a matched atom and could
    not undo it, so it reported a transcription defect on a FAITHFUL module."""

    def test_a_two_variable_row_does_not_lock_in_the_wrong_permutation(self) -> None:
        query = """
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= (+ x y) 1))
        (assert (= x 2))
        (assert (= y 0))
        """
        module = f"""
axiom {X0} : Real
axiom {X1} : Real
axiom axeyum.reconstruct.lra.hyp._2 : Real.le (Real.add {X1} (Real.add {X0} \
(Real.add (Real.neg Real.one) Real.zero))) Real.zero
axiom axeyum.reconstruct.lra.hyp._3 : Real.le (Real.add (Real.neg {X1}) \
(Real.add Real.one (Real.add Real.one Real.zero))) Real.zero
axiom axeyum.reconstruct.lra.hyp._4 : Real.le (Real.add (Real.neg {X0}) Real.zero) Real.zero
"""
        phi, _hyps, _allowed, detail = run(module, query)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(phi[X1], "x")
        self.assertEqual(phi[X0], "y")


class TheReCheckIsIndependentOfTheSearch(unittest.TestCase):
    """`verify_binding` is what makes an accept defensible. Each of its four
    properties is driven to failure directly, because the search will never
    hand it a bad binding while the search is correct — and a guard exercised
    only by a bug is a guard nobody notices going blind."""

    HYPS = [("h", "Real", ("<=", ((("v0",), 1), (("v1",), -1)), 5))]
    CARRIERS = {"v0": "Real", "v1": "Real"}
    SORTS = {"s_a": "Real", "s_b": "Real", "n": "Int"}
    ALLOWED = {("<=", ((("s_a",), 1), (("s_b",), -1)), 5)}

    def test_a_correct_binding_has_no_violations(self) -> None:
        self.assertEqual(
            HB.verify_binding(
                {"v0": "s_a", "v1": "s_b"}, self.HYPS, self.ALLOWED, self.CARRIERS, self.SORTS
            ),
            [],
        )

    def test_a_non_injective_binding_is_rejected(self) -> None:
        problems = HB.verify_binding(
            {"v0": "s_a", "v1": "s_a"}, self.HYPS, self.ALLOWED, self.CARRIERS, self.SORTS
        )
        self.assertTrue(any("NOT injective" in p for p in problems), problems)

    def test_an_unbound_carrier_is_rejected(self) -> None:
        problems = HB.verify_binding(
            {"v0": "s_a"}, self.HYPS, self.ALLOWED, self.CARRIERS, self.SORTS
        )
        self.assertTrue(any("does not bind" in p for p in problems), problems)

    def test_a_binding_onto_an_atom_the_query_lacks_is_rejected(self) -> None:
        problems = HB.verify_binding(
            {"v0": "s_b", "v1": "s_a"}, self.HYPS, self.ALLOWED, self.CARRIERS, self.SORTS
        )
        self.assertTrue(any("no assertion of the query entails" in p for p in problems), problems)

    def test_an_undeclared_target_is_rejected(self) -> None:
        problems = HB.verify_binding(
            {"v0": "s_a", "v1": "ghost"}, self.HYPS, self.ALLOWED, self.CARRIERS, self.SORTS
        )
        self.assertTrue(problems)


class SortSubstitutionIsDirectional(unittest.TestCase):
    """The rendered `Int` is Lean's inductive `Int` and a proof may use
    integrality; the rendered `Real` is an opaque ordered field and cannot."""

    def test_an_int_carrier_may_not_stand_for_a_real_symbol(self) -> None:
        self.assertFalse(HB.sort_compatible("Int", "Real"))

    def test_a_real_carrier_may_stand_for_an_int_symbol(self) -> None:
        self.assertTrue(HB.sort_compatible("Real", "Int"))

    def test_an_undeclared_symbol_is_never_compatible(self) -> None:
        self.assertFalse(HB.sort_compatible("Real", None))

    def test_a_boolean_symbol_is_never_compatible(self) -> None:
        self.assertFalse(HB.sort_compatible("Real", "Bool"))


class AtomExtractionOnlyEmitsWhatIsEntailed(unittest.TestCase):
    """A source atom the query does not entail is the one bug that would make
    this checker bless a wrong module, so the decomposition is fail-closed."""

    def test_a_conjunction_contributes_both_conjuncts(self) -> None:
        atoms = HB.atoms_of(["and", [">=", "x", "0"], ["<=", "x", "1"]], True, {})
        self.assertEqual(len(atoms), 2)

    def test_a_disjunction_contributes_nothing(self) -> None:
        self.assertEqual(HB.atoms_of(["or", [">=", "x", "0"], ["<=", "x", "1"]], True, {}), [])

    def test_an_ite_contributes_nothing(self) -> None:
        self.assertEqual(HB.atoms_of(["ite", "p", [">=", "x", "0"], "false"], True, {}), [])

    def test_a_negated_le_becomes_a_strict_lt_the_other_way(self) -> None:
        # ¬(x ≤ y) is y < x, i.e. `y − x < 0`.
        self.assertEqual(
            HB.atoms_of(["not", ["<=", "x", "y"]], True, {}),
            [("<", ((("x",), -1), (("y",), 1)), 0)],
        )

    def test_an_equality_contributes_both_bounds(self) -> None:
        atoms = HB.atoms_of(["=", "x", "2"], True, {})
        self.assertIn(("<=", ((("x",), 1),), -2), atoms)
        self.assertIn(("<=", ((("x",), -1),), 2), atoms)

    def test_a_disequality_contributes_nothing(self) -> None:
        """`¬(x = 2)` is a DISJUNCTION of two strict bounds, and emitting either
        one alone would be an atom the query does not entail."""
        self.assertEqual(HB.atoms_of(["not", ["=", "x", "2"]], True, {}), [])

    def test_a_degree_two_product_now_contributes_its_monomial(self) -> None:
        """`x·y ≤ 0` was outside this parser until the `Sos` route needed it.

        It is here as a POSITIVE control: the degree-2 extension is only worth
        anything if the atom it produces is the right one, and a checker that
        silently produced `("x",)` or dropped the term would still "pass" the
        fail-closed test below.
        """
        self.assertEqual(
            HB.atoms_of(["<=", ["*", "x", "y"], "0"], True, {}),
            [("<=", ((("x", "y"), 1),), 0)],
        )

    def test_a_square_and_a_cross_term_are_different_atoms(self) -> None:
        """`x² ≤ 0` and `x·y ≤ 0` must not normalize to the same thing.

        They have the same relation, constant and coefficient, so only the
        monomial keeps them apart — and if it did not, a module rendering
        `Real.mul x x` could bind a query row about two different variables.
        """
        square = HB.atoms_of(["<=", ["*", "x", "x"], "0"], True, {})
        cross = HB.atoms_of(["<=", ["*", "x", "y"], "0"], True, {})
        self.assertEqual(square, [("<=", ((("x", "x"), 1),), 0)])
        self.assertNotEqual(square, cross)
        self.assertNotEqual(HB.signature(square[0]), HB.signature(cross[0]))

    def test_a_degree_three_product_contributes_nothing(self) -> None:
        """The fail-closed boundary moved up one degree; it did not disappear.

        `MAX_DEGREE` is 2, so a cubic assertion still yields NO atoms and any
        hypothesis claiming to descend from it stays unmatched.
        """
        self.assertEqual(
            HB.atoms_of(["<=", ["*", "x", ["*", "y", "z"]], "0"], True, {}), []
        )

    def test_a_degree_two_expansion_matches_the_expanded_polynomial(self) -> None:
        """`(x−1)·(x−1) ≤ 0` is `x² − 2x + 1 ≤ 0`.

        This is the shape the shifted SOS row `(x−1)² + (y−2)² + 1 < 0` rests on:
        if this side of the check did not multiply out, the faithful module for
        it could never bind.
        """
        self.assertEqual(
            HB.atoms_of(
                ["<=", ["*", ["-", "x", "1"], ["-", "x", "1"]], "0"], True, {}
            ),
            [("<=", ((("x",), -2), (("x", "x"), 1)), 1)],
        )

    def test_a_let_binding_is_expanded(self) -> None:
        atoms = HB.atoms_of(["let", [["u", ["+", "x", "1"]]], [">=", "u", "0"]], True, {})
        self.assertEqual(atoms, [("<=", ((("x",), -1),), -1)])


class ARenderedShapeThisCheckerCannotReadIsAFailureNotASkip(unittest.TestCase):
    def test_an_unknown_rendered_head_raises(self) -> None:
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom("Real.le (Real.sqrt v) Real.zero", "Real")

    def test_a_degree_three_rendered_product_raises(self) -> None:
        """A rendered product above `MAX_DEGREE` is a shape this checker does not
        model, and an unmodelled hypothesis must FAIL its instance rather than be
        skipped. Degree 2 is read (the `Sos` route renders it); degree 3 is not."""
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom(
                f"Real.le (Real.mul {X0} (Real.mul {X1} {X0})) Real.zero", "Real"
            )

    def test_an_unreadable_hypothesis_fails_the_instance(self) -> None:
        damaged = MODULE.replace(
            "axeyum.reconstruct.lra.hyp._3 : Real.le",
            "axeyum.reconstruct.lra.hyp._3 : Real.mystery",
        )
        phi, _hyps, _allowed, detail = run(damaged)
        self.assertIsNone(phi)
        self.assertIn("hyp._3", detail)


class ASearchDefectIsNotAPass(unittest.TestCase):
    """`check_instance` re-checks whatever `bind` returns. Nothing else exercises
    that guard while the search is correct, so it is exercised here with a search
    replaced by one that lies — the only way a guard against our own bug can be
    known to work."""

    def test_a_binding_the_search_invented_is_rejected(self) -> None:
        original = HB.bind
        HB.bind = lambda *a, **k: ({X0: "s_a", X1: "s_a"}, [], "")
        try:
            phi, _hyps, _allowed, detail = run(MODULE)
        finally:
            HB.bind = original
        self.assertIsNone(phi)
        self.assertIn("SEARCH DEFECT", detail)


class TheManifestIsRealAndOnlyGrows(unittest.TestCase):
    def test_every_pinned_instance_exists(self) -> None:
        pinned = HB.manifest_instances()
        # `corpus/` is excluded from the mutation harness's scratch tree, so its
        # absence there is not a manifest defect; everything else must be present.
        if not (ROOT / "corpus").is_dir():
            pinned = [p for p in pinned if not p.startswith("corpus/")]
        missing = [p for p in pinned if not (ROOT / p).is_file()]
        self.assertEqual(missing, [])

    def test_the_manifest_meets_its_own_floor(self) -> None:
        self.assertGreaterEqual(len(HB.manifest_instances()), HB.MIN_INSTANCES)



# ---------------------------------------------------------------------------
# The Diophantine route (added 2026-08-18)
# ---------------------------------------------------------------------------

D0 = "axeyum.reconstruct.dio.x._0"
D1 = "axeyum.reconstruct.dio.x._1"

# `x = 2 ∧ x + y = 1` with `y = 0` asserted too, so the query is a real system and
# not one row the module could match by accident.
DIO_QUERY = """
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x 2))
(assert (= (+ x y) 1))
(assert (= y 0))
(check-sat)
"""

# The Int prelude is fully proved, so a real Diophantine module's ENTIRE trusted
# base is these carriers and hypotheses. Coefficients are rendered as repeated
# `Int.add`, which is what the route actually emits.
DIO_MODULE = f"""
axiom {D0} : Int
axiom {D1} : Int
axiom axeyum.reconstruct.dio.hyp._2 : Eq.{{1}} Int {D0} (Int.add Int.one Int.one)
axiom axeyum.reconstruct.dio.hyp._3 : Eq.{{1}} Int (Int.add {D0} {D1}) Int.one
theorem axeyum_refutation : False := trivial
"""


class TheDiophantineRouteBinds(unittest.TestCase):
    """`axeyum.reconstruct.dio.hyp._N` renders `Eq.{1} Int` equalities rather than
    the `Real.le`/`Real.lt` bounds the Farkas routes emit. 18 committed instances
    route through it; before 2026-08-18 every one of them failed the run as an
    unmodelled namespace."""

    def test_the_pristine_diophantine_module_binds(self) -> None:
        phi, hypotheses, _allowed, detail = run(DIO_MODULE, DIO_QUERY)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(len(hypotheses), 2)
        self.assertEqual(phi[D0], "x")
        self.assertEqual(phi[D1], "y")

    def test_an_equality_at_the_wrong_sort_is_not_read_as_an_Int_equality(self) -> None:
        """`Eq.{1} α …` is the attestation skeleton's equality over an opaque
        sort. Reading it as an equality between the query's integers would let a
        module that says nothing bind to a module that says something."""
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom(f"Eq.{{1}} α {D0} Int.one", "Int")

    def test_a_shifted_constant_is_caught(self) -> None:
        damaged = DIO_MODULE.replace(
            "(Int.add Int.one Int.one)", "(Int.add Int.one (Int.add Int.one Int.one))"
        )
        self.assertNotEqual(damaged, DIO_MODULE)
        phi, _h, _a, detail = run(damaged, DIO_QUERY)
        self.assertIsNone(phi, "`x = 2` rendered as `x = 3` was accepted")

    def test_a_dropped_summand_is_caught(self) -> None:
        damaged = DIO_MODULE.replace(f"(Int.add {D0} {D1})", D1)
        self.assertNotEqual(damaged, DIO_MODULE)
        phi, _h, _a, detail = run(damaged, DIO_QUERY)
        self.assertIsNone(phi, "`x + y = 1` rendered as `y = 1` was accepted")

    def test_an_equality_weakened_to_a_strict_bound_is_caught(self) -> None:
        """`a = b` does not entail `a < b`. The NON-strict weakening would be a
        faithful consequence, which is why the mutation generator injects the
        strict one."""
        damaged = DIO_MODULE.replace(
            f"Eq.{{1}} Int (Int.add {D0} {D1}) Int.one",
            f"Int.lt (Int.add {D0} {D1}) Int.one",
        )
        self.assertNotEqual(damaged, DIO_MODULE)
        phi, _h, _a, _detail = run(damaged, DIO_QUERY)
        self.assertIsNone(phi)

    def test_swapping_the_two_carriers_in_one_hypothesis_only_is_caught(self) -> None:
        """Against the FULL module. Swapping them in `DIO_MODULE` alone is not a
        corruption at all — with `(= y 0)` unrendered, `y = 2 ∧ y + x = 1` is the
        same system under the renaming that swaps the two carriers, and the
        checker rightly accepts it. Measured while writing this test, and the
        reason the fixture here renders every row: only then is one carrier
        pinned by a second hypothesis and the swap genuinely wrong.
        """
        full = DIO_MODULE.replace(
            "theorem axeyum_refutation",
            f"axiom axeyum.reconstruct.dio.hyp._4 : Eq.{{1}} Int {D1} Int.zero\n"
            "theorem axeyum_refutation",
        )
        intact, _h, _a, detail = run(full, DIO_QUERY)
        self.assertIsNotNone(intact, detail)
        damaged = full.replace(
            f"Eq.{{1}} Int {D0} (Int.add Int.one Int.one)",
            f"Eq.{{1}} Int {D1} (Int.add Int.one Int.one)",
        )
        self.assertNotEqual(damaged, full)
        phi, _h, _a, detail = run(damaged, DIO_QUERY)
        self.assertIsNone(phi)
        self.assertNotIn("SEARCH DEFECT", detail)

    def test_a_real_carrier_route_is_still_rejected_for_an_Int_query_symbol(self) -> None:
        """The dio carrier is `Int`, so the directional sort rule must still bite:
        an `Int` carrier may not stand for a `Real`-declared symbol."""
        real_query = DIO_QUERY.replace("() Int", "() Real")
        phi, _h, _a, detail = run(DIO_MODULE, real_query)
        self.assertIsNone(phi)
        self.assertNotIn("SEARCH DEFECT", detail)


class TheDegreeTwoBindingDiscriminates(unittest.TestCase):
    """The `Sos` route's hypotheses are quadratic, and a looser check would bind
    them to the wrong row.

    Reaching this class was the point of the degree-2 extension: nine `Sos`
    instances used to render `axiom prop._0; axiom Not prop._0` and were pinned
    as transcribing NOTHING. They now render `Real.lt (Real.add Real.one
    (Real.mul x x)) Real.zero` and are pinned as bound — which is only worth
    more than the attestation if the binding can FAIL, so each way it must fail
    is driven here.
    """

    QUERY = """
    (set-logic QF_NRA)
    (declare-fun x1 () Real)
    (declare-fun x2 () Real)
    (assert (< (+ (* x1 x1) (* x2 x2) 1.0) 0.0))
    (check-sat)
    """

    CROSS_QUERY = """
    (set-logic QF_NRA)
    (declare-fun x1 () Real)
    (declare-fun x2 () Real)
    (assert (< (+ (* x1 x2) (* x2 x2) 1.0) 0.0))
    (check-sat)
    """

    def _module(self, lhs: str) -> str:
        return f"""
axiom Real : Sort (1)
axiom Real.add : ((x0 : Real) -> ((x1 : Real) -> Real))
axiom Real.mul : ((x0 : Real) -> ((x1 : Real) -> Real))
axiom Real.lt : ((x0 : Real) -> ((x1 : Real) -> Prop))
axiom {X0} : Real
axiom {X1} : Real
axiom axeyum.reconstruct.lra.hyp._2 : Real.lt {lhs} Real.zero
theorem axeyum_refutation : False := trivial
"""

    SUM_OF_SQUARES = (
        f"(Real.add Real.one (Real.add (Real.mul {X0} {X0}) (Real.mul {X1} {X1})))"
    )

    def test_the_faithful_quadratic_module_binds(self) -> None:
        phi, hypotheses, _allowed, detail = run(
            self._module(self.SUM_OF_SQUARES), self.QUERY
        )
        self.assertIsNotNone(phi, detail)
        self.assertEqual(len(hypotheses), 1)
        self.assertEqual({phi[X0], phi[X1]}, {"x1", "x2"})

    def test_a_rendered_square_does_not_bind_a_cross_term(self) -> None:
        """`x₁² + x₂² + 1 < 0` rendered against a query saying `x₁x₂ + x₂² + 1 < 0`.

        Same relation, same constant, same coefficients — the ONLY difference is
        which monomials they are, so this is exactly the discrimination the
        variable-keyed normalizer could not make.
        """
        phi, _h, _a, detail = run(self._module(self.SUM_OF_SQUARES), self.CROSS_QUERY)
        self.assertIsNone(phi, detail)

    def test_a_rendered_cross_term_does_not_bind_a_square(self) -> None:
        """The converse. `x₁x₂` onto `x₁²` would need both carriers to map to the
        same query symbol, which injectivity refuses — the same rule that stops
        two carriers collapsing anywhere else, not a special case."""
        lhs = (
            f"(Real.add Real.one (Real.add (Real.mul {X0} {X1}) (Real.mul {X1} {X1})))"
        )
        phi, _h, _a, detail = run(self._module(lhs), self.QUERY)
        self.assertIsNone(phi, detail)

    def test_dropping_the_constant_is_caught(self) -> None:
        """`x₁² + x₂² < 0` is a different (and unentailed) row of this query."""
        lhs = f"(Real.add (Real.mul {X0} {X0}) (Real.mul {X1} {X1}))"
        phi, _h, _a, detail = run(self._module(lhs), self.QUERY)
        self.assertIsNone(phi, detail)

    # A query whose cross term forces φ to be ORDER-REVERSING: the linear `zz`
    # pins `x._1 -> zz`, so the rendered `(x._0, x._1)` has to land on the query's
    # `(aa, zz)` with `x._0 -> aa`. Renaming factor-by-factor without re-sorting
    # yields `("zz", "aa")`, which is not the atom the query side produced.
    REVERSING_QUERY = """
    (set-logic QF_NRA)
    (declare-fun aa () Real)
    (declare-fun zz () Real)
    (assert (< (+ (* zz aa) zz) 0.0))
    (check-sat)
    """

    def test_a_renamed_monomial_is_re_sorted_before_it_is_compared(self) -> None:
        """φ need not preserve the order of a monomial's factors.

        `verify_binding` re-derives the atom from φ alone, so if it renamed the
        factors in place and compared without re-sorting, this FAITHFUL module
        would be rejected — the direction of failure that gets a checker deleted
        rather than the one that gets it trusted.
        """
        lhs = f"(Real.add (Real.mul {X0} {X1}) {X1})"
        phi, _h, _a, detail = run(self._module(lhs), self.REVERSING_QUERY)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(phi[X0], "aa")
        self.assertEqual(phi[X1], "zz")

    def test_a_consistent_renaming_of_the_carriers_still_binds(self) -> None:
        """The positive control. A checker that rejects every quadratic module
        discriminates exactly as poorly as one that accepts every one."""
        renamed = (
            self._module(self.SUM_OF_SQUARES)
            .replace(X0, "TMP")
            .replace(X1, X0)
            .replace("TMP", X1)
        )
        phi, _h, _a, detail = run(renamed, self.QUERY)
        self.assertIsNotNone(phi, detail)


class EqualityNormalizationIsRenameInvariant(unittest.TestCase):
    """The regression that made four faithful Diophantine modules fail.

    The obvious canonical form for `E = 0` flips the sign so the lexicographically
    first VARIABLE is positive. The two sides of this check use different names by
    construction — `value` on one side, `dio.x._0` on the other — so that
    normalization is not rename-invariant and rejects faithful modules. Both
    orientations go into the pool instead, which needs no name ordering at all.
    """

    def test_the_two_orientations_are_distinct_atoms(self) -> None:
        """If they were fused, the fusing would have to read a variable name."""
        self.assertNotEqual(
            HB.canonical("=", {("a",): Fraction(1), ("b",): Fraction(-1)}, Fraction(0)),
            HB.canonical("=", {("a",): Fraction(-1), ("b",): Fraction(1)}, Fraction(0)),
        )

    def test_an_equality_assertion_contributes_both_orientations(self) -> None:
        atoms = HB.atoms_of(["=", "value", ["+", "x_squared", "1"]], True, {})
        equalities = [a for a in atoms if a[0] == "="]
        self.assertEqual(len(equalities), 2)
        self.assertIn(("=", ((("value",), 1), (("x_squared",), -1)), -1), equalities)
        self.assertIn(("=", ((("value",), -1), (("x_squared",), 1)), 1), equalities)

    def test_the_orientation_the_renderer_chose_binds_either_way(self) -> None:
        """Names picked so that a sign normalization keyed on the first variable
        would disagree between the two sides: the query normalizes on `value`
        (positive) and the module on `dio.x._0` (negative)."""
        query = """
        (set-logic QF_LIA)
        (declare-fun x_squared () Int)
        (declare-fun value () Int)
        (assert (= value (+ x_squared 1)))
        """
        module = f"""
axiom {D0} : Int
axiom {D1} : Int
axiom axeyum.reconstruct.dio.hyp._3 : Eq.{{1}} Int (Int.add (Int.neg {D0}) {D1}) Int.one
"""
        phi, _h, _a, detail = run(module, query)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(phi[D0], "x_squared")
        self.assertEqual(phi[D1], "value")


class TheNewMutationsActuallyFire(unittest.TestCase):
    """A corruption generator that returns `None` on every input inflates nothing
    and catches nothing, and the run's `mutants_caught` floor would never notice
    because the other generators carry it."""

    HYP = f"Eq.{{1}} Int (Int.add {D0} {D1}) Int.one"

    def test_duplicate_term_counts_a_summand_twice(self) -> None:
        damaged = HB.mutate(self.HYP, "Int", "duplicate-term")
        self.assertIsNotNone(damaged)
        self.assertEqual(
            HB.lean_atom(damaged, "Int"),
            HB.canonical("=", {(D0,): Fraction(2), (D1,): Fraction(1)}, Fraction(-1)),
        )

    def test_shift_constant_falls_back_to_a_bare_one(self) -> None:
        """The Farkas routes end every hypothesis in `.zero`; the Diophantine
        route renders numerals as repeated `.one` and may have no `.zero` at all,
        so without the fallback this generator was silent on the whole route."""
        self.assertNotIn("Int.zero", self.HYP)
        damaged = HB.mutate(self.HYP, "Int", "shift-constant")
        self.assertIsNotNone(damaged)
        self.assertEqual(
            HB.lean_atom(damaged, "Int"),
            HB.canonical("=", {(D0,): Fraction(1), (D1,): Fraction(1)}, Fraction(-2)),
        )

    def test_flip_relation_weakens_an_equality_to_a_strict_bound(self) -> None:
        damaged = HB.mutate(self.HYP, "Int", "flip-relation")
        self.assertIsNotNone(damaged)
        self.assertTrue(damaged.startswith("Int.lt "), damaged)

    def test_swap_arguments_keeps_the_sort_argument_in_place(self) -> None:
        """`Eq.{1} Int a b` has FOUR spine positions. A swapper written for the
        three-position form would produce `Eq.{1} b Int a`, which parses as
        nothing and would be 'caught' for the wrong reason."""
        damaged = HB.mutate(self.HYP, "Int", "swap-arguments")
        self.assertIsNotNone(damaged)
        self.assertTrue(damaged.startswith("Eq.{1} Int "), damaged)
        # Swapping the sides of an equality is FAITHFUL, and the checker must say
        # so rather than manufacture a catch.
        self.assertEqual(
            HB.lean_atom(damaged, "Int"),
            HB.canonical("=", {(D0,): Fraction(-1), (D1,): Fraction(-1)}, Fraction(1)),
        )


# ---------------------------------------------------------------------------
# Opaque-skeleton attestations
# ---------------------------------------------------------------------------

ATTESTATION = """
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.func._2 : ((x0 : α) -> ((x1 : α) -> α))
axiom axeyum.reconstruct.hyp._3 : Eq.{1} α axeyum.reconstruct.atom._0 \
axeyum.reconstruct.atom._1
axiom axeyum.reconstruct.hyp._4 : Not (Eq.{1} α (axeyum.reconstruct.func._2 \
axeyum.reconstruct.atom._0) (axeyum.reconstruct.func._2 axeyum.reconstruct.atom._1))
theorem axeyum_refutation : False := trivial
"""


class AnAttestationIsConfirmedContentFree(unittest.TestCase):
    """124 of the 270 modules the corpus renders transcribe NOTHING: their whole
    vocabulary is `α atom._N prop._N func._N Eq.{1} Not And`. Binding them would
    be a check that cannot fail. What must not be possible is a module that DOES
    carry content slipping into the class, so each way out of it is driven."""

    def test_the_fixture_is_an_attestation(self) -> None:
        ok, why, _vacuous = HB.classify_attestation(ATTESTATION)
        self.assertTrue(ok, why)

    def test_a_smuggled_numeral_takes_it_out_of_the_class(self) -> None:
        damaged = ATTESTATION.replace(
            "Eq.{1} α axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1",
            "Eq.{1} α Int.one axeyum.reconstruct.atom._1",
        )
        self.assertNotEqual(damaged, ATTESTATION)
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)
        self.assertIn("Int.one", why)

    def test_an_undeclared_opaque_name_takes_it_out_of_the_class(self) -> None:
        """`atom._9` is never declared, so a hypothesis mentioning it rests on a
        constant that is not in the module's own trusted base."""
        damaged = ATTESTATION.replace(
            "axeyum.reconstruct.atom._1\n", "axeyum.reconstruct.atom._9\n"
        )
        self.assertNotEqual(damaged, ATTESTATION)
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)
        self.assertIn("atom._9", why)

    def test_an_extra_axiom_takes_it_out_of_the_class(self) -> None:
        damaged = ATTESTATION.replace(
            "theorem axeyum_refutation",
            "axiom convenient.premise : False\ntheorem axeyum_refutation",
        )
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)
        self.assertIn("convenient.premise", why)

    def test_a_carrier_bearing_hypothesis_takes_it_out_of_the_class(self) -> None:
        """The failure mode that matters most: a module with REAL content must
        never be waved through as 'says nothing'."""
        ok, why, _v = HB.classify_attestation(MODULE)
        self.assertFalse(ok)

    def test_a_type_that_spilled_onto_the_next_line_is_refused_not_classified(self) -> None:
        """`AXIOM_LINE` reads one line, so a multi-line type arrives TRUNCATED —
        and a prefix of a content-bearing type reads as a skeleton. The imbalance
        is the only signal available, and it must refuse rather than classify."""
        damaged = ATTESTATION.replace(
            "axiom axeyum.reconstruct.hyp._4 : Not (Eq.{1} α",
            "axiom axeyum.reconstruct.hyp._4 : Not (Eq.{1} α (",
        )
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)
        self.assertIn("not balanced", why)

    def test_an_atom_declared_as_something_other_than_the_opaque_sort(self) -> None:
        damaged = ATTESTATION.replace("axeyum.reconstruct.atom._0 : α", "axeyum.reconstruct.atom._0 : Prop")
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)

    def test_a_func_that_is_not_a_function_over_the_opaque_sort(self) -> None:
        damaged = ATTESTATION.replace(
            "axeyum.reconstruct.func._2 : ((x0 : α) -> ((x1 : α) -> α))",
            "axeyum.reconstruct.func._2 : ((x0 : Int) -> Int)",
        )
        ok, why, _v = HB.classify_attestation(damaged)
        self.assertFalse(ok)

    def test_a_module_with_no_hypothesis_at_all_is_not_an_attestation(self) -> None:
        """Otherwise the emptiest possible module would be blessed, and the class
        would grow to cover anything that renders nothing."""
        decls = "\n".join(
            line for line in ATTESTATION.splitlines() if "hyp._" not in line
        )
        ok, why, _v = HB.classify_attestation(decls)
        self.assertFalse(ok)


# ---------------------------------------------------------------------------
# Structural binding
# ---------------------------------------------------------------------------

STRUCTURAL_QUERY = """
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(declare-const v (_ BitVec 8))
(assert (not (= (select (store a i v) j) (select a j))))
(check-sat)
"""

# `select(store(a, i, v), j)` beside `select(a, j)`: both are subterms of the
# query above, under atom._0 = a, atom._1 = i, atom._2 = v, atom._3 = j,
# func._4 = store, func._5 = select.
STRUCTURAL_MODULE = """
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.atom._2 : α
axiom axeyum.reconstruct.atom._3 : α
axiom axeyum.reconstruct.func._4 : ((x0 : α) -> ((x1 : α) -> ((x2 : α) -> α)))
axiom axeyum.reconstruct.func._5 : ((x0 : α) -> ((x1 : α) -> α))
axiom axeyum.reconstruct.hyp._6 : Eq.{1} α (axeyum.reconstruct.func._5 \
(axeyum.reconstruct.func._4 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1 \
axeyum.reconstruct.atom._2) axeyum.reconstruct.atom._3) \
(axeyum.reconstruct.func._5 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._3)
axiom axeyum.reconstruct.hyp._7 : Not (Eq.{1} α (axeyum.reconstruct.func._5 \
(axeyum.reconstruct.func._4 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1 \
axeyum.reconstruct.atom._2) axeyum.reconstruct.atom._3) \
(axeyum.reconstruct.func._5 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._3))
theorem axeyum_refutation : False := axeyum.reconstruct.hyp._7 axeyum.reconstruct.hyp._6
"""


def _query_file(text: str):
    import tempfile

    handle = tempfile.NamedTemporaryFile(
        "w", suffix=".smt2", delete=False, encoding="utf-8"
    )
    handle.write(text)
    handle.close()
    return pathlib.Path(handle.name)


class AStructuralModuleTranscribesTheQuerysTerms(unittest.TestCase):
    """The array/EUF routes cannot bind a hypothesis to an `(assert …)` line —
    theirs is the conclusion of a congruence derivation, not a constraint. What
    holds is one step weaker and still sharp: every term they equate is a
    SUBTERM of the file, under one injective correspondence."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.query = _query_file(STRUCTURAL_QUERY)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.query.unlink(missing_ok=True)

    def test_the_fixture_binds(self) -> None:
        ok, why, nodes = HB.bind_structural(STRUCTURAL_MODULE, self.query)
        self.assertTrue(ok, why)
        self.assertEqual(nodes, 2 * (6 + 3))

    def test_an_axiom_beyond_the_opaque_sort_is_refused_structurally(self) -> None:
        """The third copy of the opaque-sort guard, which nothing covered.

        `bind_anchored` and `classify_attestation` each carry this check and each
        had a control. `bind_structural`'s copy did not: the mutation harness
        measured it **SURVIVED** on 2026-08-19 — deleting it changed no test
        result — so the structural class could have admitted a module carrying an
        axiom the query never mentions, and the verdict would still have read
        `structural`.

        `structural` is the largest class in the census (102 of 135 instances),
        so an unguarded smuggled axiom there is not a corner case; it is most of
        the coverage this repository claims for transcription binding.
        """
        smuggled = STRUCTURAL_MODULE.replace(
            "axiom α : Sort (1)", "axiom α : Sort (1)\naxiom Int.one : Int"
        )
        ok, why, _n = HB.bind_structural(smuggled, self.query)
        self.assertFalse(ok)
        self.assertIn("opaque sort", why)

    def test_swapping_two_arguments_is_rejected(self) -> None:
        """`store(a, i, v)` becomes `store(i, a, v)`, which the file does not
        contain. No name is added or removed, so only the match can catch it."""
        damaged = HB.mutate_structural_module(STRUCTURAL_MODULE, "swap-arguments")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_structural(damaged, self.query)
        self.assertFalse(ok)

    def test_dropping_an_argument_is_rejected(self) -> None:
        damaged = HB.mutate_structural_module(STRUCTURAL_MODULE, "drop-argument")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_structural(damaged, self.query)
        self.assertFalse(ok)

    def test_collapsing_two_constants_is_rejected(self) -> None:
        """Injectivity: one Lean name cannot stand for two query symbols."""
        damaged = HB.mutate_structural_module(
            STRUCTURAL_MODULE, "collapse-two-constants"
        )
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_structural(damaged, self.query)
        self.assertFalse(ok)

    def test_an_application_must_match_one_of_the_same_arity(self) -> None:
        """Driven on `_match` directly, because the bucket index would reject a
        wrong-arity term before the matcher ever saw it — and a guard that only
        ever fires behind another guard is untested, not redundant."""
        self.assertIsNone(HB._match(["f", "x"], ("store", "a", "i", "v"), {}))
        self.assertIsNotNone(HB._match(["f", "x", "y", "z"], ("store", "a", "i", "v"), {}))

    def test_a_rendered_application_never_matches_a_query_leaf(self) -> None:
        self.assertIsNone(HB._match(["f", "x"], "a", {}))

    def test_a_rendered_constant_never_matches_a_query_application(self) -> None:
        self.assertIsNone(HB._match("atom._0", ("select", "a", "j"), {}))

    def test_one_lean_name_cannot_mean_two_query_symbols(self) -> None:
        self.assertIsNone(HB._bind_name({"atom._0": "a"}, "atom._0", "i"))

    def test_two_lean_names_cannot_mean_one_query_symbol(self) -> None:
        self.assertIsNone(HB._bind_name({"atom._0": "a"}, "atom._1", "a"))

    def test_a_bare_pair_of_constants_carries_no_structure(self) -> None:
        """Both sides opaque constants: an injective map onto two of the query's
        symbols exists for ANY query with two symbols, so a match would show
        nothing. That is the attestation class, and it must not reach this one."""
        ok, why, _n = HB.bind_structural(
            "\n".join(
                [
                    "axiom α : Sort (1)",
                    "axiom axeyum.reconstruct.atom._0 : α",
                    "axiom axeyum.reconstruct.atom._1 : α",
                    "axiom axeyum.reconstruct.hyp._2 : Eq.{1} α "
                    "axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1",
                ]
            ),
            self.query,
        )
        self.assertFalse(ok)
        self.assertIn("carries no structure", why)

    def test_a_declared_constant_no_rendered_term_uses_is_rejected(self) -> None:
        damaged = STRUCTURAL_MODULE.replace(
            "axiom axeyum.reconstruct.func._5 :",
            "axiom axeyum.reconstruct.atom._9 : α\naxiom axeyum.reconstruct.func._5 :",
        )
        ok, why, _n = HB.bind_structural(damaged, self.query)
        self.assertFalse(ok)
        self.assertIn("no rendered term binds it", why)

    def test_an_indexed_literal_is_a_leaf_not_an_application(self) -> None:
        """`(_ bv13 16)` is a literal. Reading it as a 3-argument application
        made every module mentioning one unmatchable — a false negative, which
        pushes a transcribing module into the attestation class."""
        self.assertEqual(HB._smt_term(["_", "bv13", "16"], {}), "_ bv13 16")

    def test_an_indexed_operator_is_still_an_application(self) -> None:
        self.assertEqual(
            HB._smt_term([["_", "zero_extend", "13"], "v"], {}),
            ("_ zero_extend 13", "v"),
        )

    def test_a_let_bound_name_is_expanded(self) -> None:
        self.assertEqual(
            HB._smt_term(["let", [["x", ["f", "a"]]], ["g", "x"]], {}),
            ("g", ("f", "a")),
        )

    def test_a_quantifier_is_opaque_rather_than_guessed_at(self) -> None:
        self.assertEqual(
            HB._smt_term(["forall", [["x", "Int"]], ["p", "x"]], {}), ("!quantified",)
        )


class ASelfRefutingAttestationIsRejected(unittest.TestCase):
    """A module carrying `Not (Eq.{1} α t t)` — an axiom Lean's own `rfl`
    refutes — has a `False` that follows from that one axiom alone: not even the
    propositional step it appears to take is taken, and it would follow just as
    well if the `.smt2` file said something else. One of the corpus's 124
    attestations was such a module (`neg-no-self-negating-proposition.smt2`,
    measured 2026-08-18); it was COUNTED as `attested_vacuous=` and the run still
    exited 0. Counting is not enough — a number nobody's exit status depends on
    is a number a regression can raise — so it is now a failure."""

    def test_a_denied_reflexivity_is_self_refuting(self) -> None:
        self.assertTrue(
            HB._is_self_refuting(
                "Not (Eq.{1} α axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._0)"
            )
        )

    def test_a_denied_equality_between_two_atoms_is_not(self) -> None:
        self.assertFalse(
            HB._is_self_refuting(
                "Not (Eq.{1} α axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1)"
            )
        )

    def test_the_fixture_carries_no_self_refuting_axiom(self) -> None:
        ok, _why, vacuous = HB.classify_attestation(ATTESTATION)
        self.assertTrue(ok)
        self.assertEqual(vacuous, 0)

    def test_denying_reflexivity_in_the_fixture_is_counted(self) -> None:
        ok, why, vacuous = HB.classify_attestation(_self_refuting(ATTESTATION))
        self.assertTrue(ok, why)
        self.assertEqual(vacuous, 1)


def _self_refuting(attestation: str) -> str:
    """The fixture with its denied equality collapsed onto one atom."""
    return attestation.replace(
        "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._1",
        "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0",
    )


class TheConverseDirectionIsMeasured(unittest.TestCase):
    """Binding shows every rendered hypothesis comes FROM the query. It shows
    nothing about the query's rows that were never rendered — so that shortfall
    is counted, from the accepted renaming rather than from the search."""

    def test_an_unrendered_assertion_is_counted_as_unrepresented(self) -> None:
        sorts, assertions = _read(DIO_QUERY)
        phi, hypotheses, _allowed, detail = run(DIO_MODULE, DIO_QUERY)
        self.assertIsNotNone(phi, detail)
        spine, covered, opaque_rows = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual(spine, 3)
        # `(= y 0)` is never rendered: two hypotheses, two represented rows.
        self.assertEqual(covered, 2)
        self.assertEqual(opaque_rows, 0)

    def test_a_module_rendering_every_row_is_fully_represented(self) -> None:
        module = DIO_MODULE.replace(
            "theorem axeyum_refutation",
            f"axiom axeyum.reconstruct.dio.hyp._4 : Eq.{{1}} Int {D1} Int.zero\n"
            "theorem axeyum_refutation",
        )
        sorts, assertions = _read(DIO_QUERY)
        phi, hypotheses, _allowed, detail = run(module, DIO_QUERY)
        self.assertIsNotNone(phi, detail)
        spine, covered, opaque_rows = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual((spine, covered, opaque_rows), (3, 3, 0))

    def test_one_hypothesis_cannot_represent_two_rows_at_once(self) -> None:
        """The count is a maximum MATCHING, not an overlap. Two assertions of the
        same query can entail a common atom -- here `(= x 1)` twice over, which
        `atoms_of` decomposes identically -- and an overlap count would credit
        BOTH to a module that rendered it once. The shortfall this number exists
        to expose would then be smaller than the truth, in the direction nobody
        is checking."""
        query = """
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x 1))
(assert (= x 1))
(assert (= y 0))
(check-sat)
"""
        module = f"""
axiom {D0} : Int
axiom axeyum.reconstruct.dio.hyp._2 : Eq.{{1}} Int {D0} Int.one
theorem axeyum_refutation : False := trivial
"""
        sorts, assertions = _read(query)
        phi, hypotheses, _allowed, detail = run(module, query)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(len(hypotheses), 1)
        spine, covered, opaque_rows = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual((spine, covered, opaque_rows), (3, 1, 0))

    def test_two_hypotheses_from_ONE_row_represent_ONE_row(self) -> None:
        """The sharpest form of the matching requirement, and the only shape that
        can see it: both hypotheses descend from `(= x 2)` -- one as the equality,
        one as the bound it entails -- so together they stand for ONE spine row.
        An adjacency that credited every row to every hypothesis would report 2
        here and go unnoticed in the tests above, where the matching is capped by
        the hypothesis count anyway."""
        module = f"""
axiom {D0} : Int
axiom axeyum.reconstruct.dio.hyp._2 : Eq.{{1}} Int {D0} (Int.add Int.one Int.one)
axiom axeyum.reconstruct.dio.hyp._3 : Int.le (Int.add {D0} \
(Int.neg (Int.add Int.one Int.one))) Int.zero
theorem axeyum_refutation : False := trivial
"""
        sorts, assertions = _read(DIO_QUERY)
        phi, hypotheses, _allowed, detail = run(module, DIO_QUERY)
        self.assertIsNotNone(phi, detail)
        self.assertEqual(len(hypotheses), 2)
        spine, covered, opaque_rows = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual((spine, covered, opaque_rows), (3, 1, 0))

    def test_a_row_this_parser_cannot_decompose_is_reported_separately(self) -> None:
        """A row yielding no atoms is unrepresentable whatever the module
        renders, so folding it into the shortfall would blame the refutation for
        a blind spot in this script. Measured over the corpus the count is zero,
        and the driver fails on any nonzero one -- but the two must be
        distinguishable before that can mean anything."""
        query = DIO_QUERY.replace(
            "(check-sat)", "(assert (or (= x 5) (= x 6)))\n(check-sat)"
        )
        sorts, assertions = _read(query)
        phi, hypotheses, _allowed, detail = run(DIO_MODULE, query)
        self.assertIsNotNone(phi, detail)
        spine, covered, opaque_rows = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual((spine, covered, opaque_rows), (4, 2, 1))

    def test_such_a_row_FAILS_the_run_rather_than_lowering_the_number(self) -> None:
        query = DIO_QUERY.replace(
            "(check-sat)", "(assert (or (= x 5) (= x 6)))\n(check-sat)"
        )
        self.assertEqual(_drive(DIO_MODULE, query), 1)

    def test_the_same_driver_passes_without_the_undecomposable_row(self) -> None:
        """Without this twin the test above would pass against a driver that
        failed every run."""
        self.assertEqual(_drive(DIO_MODULE, DIO_QUERY), 0)


def _drive(module: str, query: str, *extra: str) -> int:
    """`main` over one in-memory instance with every floor released."""
    import tempfile

    with tempfile.TemporaryDirectory() as scratch:
        qpath = pathlib.Path(scratch) / "q.smt2"
        mpath = pathlib.Path(scratch) / "m.lean"
        qpath.write_text(query, encoding="utf-8")
        mpath.write_text(module, encoding="utf-8")
        return HB.main(
            [
                "--instance", str(qpath),
                "--module", str(mpath),
                "--no-build",
                "--no-self-check",
                "--min-instances", "0",
                "--min-hypotheses", "0",
                "--min-required-mutations", "0",
                "--min-attestations", "0",
                "--min-represented", "0",
                "--min-structural", "0",
                "--min-structural-nodes", "0",
                "--min-structural-mutations", "0",
                "--min-anchored", "0",
                "--min-anchored-nodes", "0",
                "--min-anchored-mutations", "0",
                "--min-structural-anchored", "0",
                *extra,
            ]
        )


class AVacuousBindingIsNotAPass(unittest.TestCase):
    """The empty renaming satisfies every requirement the binding imposes, so a
    module with no hypothesis in any bound route BINDS — with nothing bound. A
    pinned instance that degraded to a content-free skeleton would have stayed
    green on the strength of that."""

    def _run_driver(self, module: str, query: str, *extra: str) -> int:
        import tempfile

        with tempfile.TemporaryDirectory() as scratch:
            qpath = pathlib.Path(scratch) / "q.smt2"
            mpath = pathlib.Path(scratch) / "m.lean"
            qpath.write_text(query, encoding="utf-8")
            mpath.write_text(module, encoding="utf-8")
            return HB.main(
                [
                    "--instance", str(qpath),
                    "--module", str(mpath),
                    "--no-build",
                    "--no-self-check",
                    "--min-instances", "0",
                    "--min-hypotheses", "0",
                    "--min-required-mutations", "0",
                    "--min-attestations", "0",
                    "--min-represented", "0",
                    "--min-structural", "0",
                    "--min-structural-nodes", "0",
                    "--min-structural-mutations", "0",
                    "--min-anchored", "0",
                    "--min-anchored-nodes", "0",
                    "--min-anchored-mutations", "0",
                    "--min-structural-anchored", "0",
                    *extra,
                ]
            )

    def test_a_module_with_no_bound_route_hypothesis_fails(self) -> None:
        stripped = "\n".join(
            line for line in DIO_MODULE.splitlines() if "dio.hyp._" not in line
        )
        self.assertEqual(self._run_driver(stripped, DIO_QUERY), 1)

    def test_the_same_driver_passes_on_the_intact_module(self) -> None:
        """Without this twin, the test above would pass against a driver that
        always returns 1."""
        self.assertEqual(self._run_driver(DIO_MODULE, DIO_QUERY), 0)

    def test_an_attestation_pinned_as_bound_fails(self) -> None:
        self.assertEqual(self._run_driver(ATTESTATION, DIO_QUERY), 1)

    def test_the_same_attestation_passes_when_pinned_as_attested(self) -> None:
        self.assertEqual(
            self._run_driver(ATTESTATION, DIO_QUERY, "--expect", "attested"), 0
        )

    def test_a_content_bearing_module_pinned_as_attested_fails(self) -> None:
        self.assertEqual(
            self._run_driver(DIO_MODULE, DIO_QUERY, "--expect", "attested"), 1
        )

    def test_a_structural_module_pinned_as_attested_fails(self) -> None:
        """The anti-absorption guard. An attestation's claim is that NOTHING
        relates the module to the query; if the structural binder can relate it,
        that claim is false. Without this, a renderer that started transcribing
        would leave every pinned attestation green while the words `transcribes
        NOTHING` quietly stopped being true — which is exactly what happened to
        the 6 `QfAbv`/`QfUf` instances that were structural all along."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE, STRUCTURAL_QUERY, "--expect", "attested"
            ),
            1,
        )

    def test_the_same_structural_module_passes_when_pinned_structural_anchored(
        self,
    ) -> None:
        """`STRUCTURAL_QUERY` asserts the disequality outright, so this module
        earns BOTH verdicts and `structural-anchored` is its pin. `structural`
        alone is now REFUSED for it — see
        `TheFourVerdictsCannotAbsorbEachOther`."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE, STRUCTURAL_QUERY, "--expect", "structural-anchored"
            ),
            0,
        )

    def test_a_structural_module_passes_as_structural_on_a_congruence_conclusion(
        self,
    ) -> None:
        """The twin, and the case `structural` alone still exists for: both
        rendered terms are subterms of this query, but no assertion forces them
        unequal, so nothing anchors. Without this the test above would pass
        against a driver that refused every `structural` pin."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "structural",
            ),
            0,
        )

    def test_a_self_refuting_attestation_fails_the_run(self) -> None:
        """The twin above passes on the intact attestation, so this is the
        `rfl`-refutable axiom failing and not the driver failing everything."""
        self.assertEqual(
            self._run_driver(
                _self_refuting(ATTESTATION), DIO_QUERY, "--expect", "attested"
            ),
            1,
        )


class ANonArithmeticLetBindingIsNotAFreeVariable(unittest.TestCase):
    """`(let ((a (forall …))) …)` raised `Unsupported: arithmetic head 'forall'`
    out of `read_query` and ended the whole run in a traceback — neither a pass
    nor an honest decline (`006-cbqi-ite.smt2`, measured 2026-08-18). The fix must
    not go the other way either: binding `a` as a fresh VARIABLE would invent a
    symbol a rendered hypothesis could match against."""

    def test_the_query_parses_instead_of_raising(self) -> None:
        sorts, assertions = _read(
            """
            (set-logic LIA)
            (declare-fun x () Int)
            (assert (let ((a (forall ((z Int)) (>= z 0)))) (and a (>= x 1))))
            """
        )
        self.assertEqual(len(assertions), 1)

    def test_the_opaque_name_contributes_no_atom(self) -> None:
        """`(>= a 0)` over an opaquely-bound `a` must yield nothing, not an atom
        about a variable named `a`."""
        atoms = HB.atoms_of(
            ["let", [["a", ["forall", [["z", "Int"]], [">=", "z", "0"]]]], [">=", "a", "0"]],
            True,
            {},
        )
        self.assertEqual(atoms, [])

    def test_an_arithmetic_let_binding_still_expands(self) -> None:
        atoms = HB.atoms_of(
            ["let", [["a", ["+", "x", "1"]]], [">=", "a", "0"]], True, {}
        )
        self.assertEqual(atoms, [("<=", ((("x",), -1),), -1)])


class TheAttestationManifestIsRealAndOnlyGrows(unittest.TestCase):
    def test_every_pinned_attestation_exists(self) -> None:
        pinned = HB.attestation_instances()
        if not (ROOT / "corpus").is_dir():
            pinned = [p for p in pinned if not p.startswith("corpus/")]
        missing = [p for p in pinned if not (ROOT / p).is_file()]
        self.assertEqual(missing, [])

    def test_the_attestation_manifest_meets_its_own_floor(self) -> None:
        self.assertGreaterEqual(
            len(HB.attestation_instances()), HB.MIN_ATTESTATIONS
        )

    def test_no_instance_is_pinned_as_both_bound_and_attested(self) -> None:
        """They are mutually exclusive verdicts. An instance in both files would
        pass whichever check it happened to satisfy."""
        both = set(HB.manifest_instances()) & set(HB.attestation_instances())
        self.assertEqual(both, set())


def _read(query: str):
    """`read_query` on an in-memory query string."""
    import tempfile

    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as handle:
        handle.write(query)
        path = pathlib.Path(handle.name)
    try:
        return HB.read_query(path)
    finally:
        path.unlink()


# ---------------------------------------------------------------------------
# Assertion anchoring
# ---------------------------------------------------------------------------

# The BTOR-derived shape the 7 bare-pair `ArrayAxiom` rows have: `a0 = a1` and
# `a1 = a2` are forced TRUE, `a0 = a2` is forced FALSE, and the whole thing is
# encoded as one-bit vectors under `(= #b1 …)`.
ANCHOR_QUERY = """
(set-logic QF_ABV)
(declare-const a0 (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const a1 (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const a2 (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= #b1 (bvnot (bvor (bvnot (bvand (ite (= a0 a1) #b1 #b0) \
(ite (= a1 a2) #b1 #b0))) (ite (= a0 a2) #b1 #b0)))))
(check-sat)
"""

# Both sides bare: the structural binder refuses this, and is right to.
ANCHOR_MODULE = """
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.hyp._2 : Eq.{1} α axeyum.reconstruct.atom._0 \
axeyum.reconstruct.atom._1
axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α axeyum.reconstruct.atom._0 \
axeyum.reconstruct.atom._1)
theorem axeyum_refutation : False := axeyum.reconstruct.hyp._3 axeyum.reconstruct.hyp._2
"""

# The `TermIdentity` shape, whose sides DO carry structure: `x` against
# `(ite true x y)`, and the disequality is the whole `(assert …)` line.
IDENTITY_QUERY = """
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (= x (ite true x y))))
(check-sat)
"""

IDENTITY_MODULE = """
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.atom._2 : α
axiom axeyum.reconstruct.func._3 : ((x0 : α) -> ((x1 : α) -> ((x2 : α) -> α)))
axiom axeyum.reconstruct.hyp._4 : Eq.{1} α axeyum.reconstruct.atom._0 \
(axeyum.reconstruct.func._3 axeyum.reconstruct.atom._1 axeyum.reconstruct.atom._0 \
axeyum.reconstruct.atom._2)
axiom axeyum.reconstruct.hyp._5 : Not (Eq.{1} α axeyum.reconstruct.atom._0 \
(axeyum.reconstruct.func._3 axeyum.reconstruct.atom._1 axeyum.reconstruct.atom._0 \
axeyum.reconstruct.atom._2))
theorem axeyum_refutation : False := axeyum.reconstruct.hyp._5 axeyum.reconstruct.hyp._4
"""


class ForcedDisequalitiesPropagateOnlyWhereForced(unittest.TestCase):
    """The half of anchoring that reads the `.smt2` file. It must find the
    disequalities the assertions ENTAIL and, much more importantly, must not
    invent one from a shape that entails only a disjunction."""

    def _forced(self, query: str):
        path = _query_file(query)
        try:
            return HB.forced_disequalities(path)
        finally:
            path.unlink(missing_ok=True)

    def test_a_negated_equality_is_forced(self) -> None:
        self.assertEqual(
            self._forced("(assert (not (= a b)))"), [("a", "b")]
        )

    def test_a_binary_distinct_is_forced(self) -> None:
        self.assertEqual(self._forced("(assert (distinct a b))"), [("a", "b")])

    def test_an_n_ary_distinct_forces_every_pair(self) -> None:
        self.assertEqual(
            sorted(self._forced("(assert (distinct a b c))")),
            [("a", "b"), ("a", "c"), ("b", "c")],
        )

    def test_a_conjunct_of_an_asserted_and_is_forced(self) -> None:
        self.assertEqual(
            self._forced("(assert (and (> a 0) (not (= a b))))"), [("a", "b")]
        )

    def test_a_disjunct_of_an_asserted_or_is_NOT_forced(self) -> None:
        """`(or ¬(a = b) φ)` entails a disjunction, not a fact. Reading one
        branch of it as forced is precisely the transcription bug this file
        exists to catch, so the walk stops."""
        self.assertEqual(self._forced("(assert (or (not (= a b)) (> a 0)))"), [])

    def test_an_ite_without_the_boolean_branch_pair_is_NOT_descended(self) -> None:
        self.assertEqual(
            self._forced("(assert (= #b1 (ite (not (= a b)) c d)))"), []
        )

    def test_an_asserted_equality_is_not_a_disequality(self) -> None:
        self.assertEqual(self._forced("(assert (= a b))"), [])

    def test_a_distinct_under_a_FALSE_polarity_forces_nothing(self) -> None:
        """`¬(distinct a b)` says they ARE equal. Reading `distinct` as a
        disequality wherever it appears, rather than only where the assertions
        force it true, would invent the exact opposite fact."""
        self.assertEqual(self._forced("(assert (not (distinct a b)))"), [])

    def test_an_n_ary_distinct_under_a_FALSE_polarity_forces_nothing(self) -> None:
        self.assertEqual(self._forced("(assert (not (distinct a b c)))"), [])

    def test_an_n_ary_equality_under_a_negation_is_NOT_forced(self) -> None:
        """`¬(a = b = c)` says SOME pair differs, not which. Fail-closed."""
        self.assertEqual(self._forced("(assert (not (= a b c)))"), [])

    def test_the_one_bit_vector_encoding_of_a_negation(self) -> None:
        """`(= #b1 (bvnot (ite (= a b) #b1 #b0)))` is how a BTOR-derived file
        writes `¬(a = b)`. Three separate rules have to compose to see it."""
        self.assertEqual(
            self._forced("(assert (= #b1 (bvnot (ite (= a b) #b1 #b0))))"),
            [("a", "b")],
        )

    def test_the_same_shape_without_the_bvnot_forces_nothing(self) -> None:
        """The twin of the test above: without it, a propagator that ignored
        polarity entirely would pass both."""
        self.assertEqual(
            self._forced("(assert (= #b1 (ite (= a b) #b1 #b0)))"), []
        )

    def test_a_bvor_under_a_true_polarity_is_NOT_descended(self) -> None:
        self.assertEqual(
            self._forced(
                "(assert (= #b1 (bvor (bvnot (ite (= a b) #b1 #b0)) (ite (= c d) #b1 #b0))))"
            ),
            [],
        )

    def test_a_bvor_under_a_false_polarity_IS_descended(self) -> None:
        self.assertEqual(
            self._forced(
                "(assert (= #b0 (bvor (ite (= a b) #b1 #b0) (ite (= c d) #b1 #b0))))"
            ),
            [("c", "d"), ("a", "b")],
        )

    def test_a_wider_literal_never_enters_the_one_bit_fragment(self) -> None:
        """`bvand` is conjunction only at width 1. The propagation can only be
        entered through `#b1`/`#b0`, so a wide equality contributes nothing."""
        self.assertEqual(
            self._forced("(assert (= #b1111 (bvand p q)))"), []
        )

    def test_a_let_binding_is_expanded_before_propagating(self) -> None:
        self.assertEqual(
            self._forced("(assert (let ((t (= a b))) (not t)))"), [("a", "b")]
        )


class AnAnchoredModuleAssumesWhatTheQueryEntails(unittest.TestCase):
    """A module whose two sides are bare constants carries no structure to match
    — `bind_structural` refuses it and is right to. What it DOES claim is that
    the query entails `¬(lhs = rhs)`, and nothing in Lean checks that. Anchoring
    does, and pins the correspondence by requiring the query to force exactly one
    disequality the module could stand for."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.query = _query_file(ANCHOR_QUERY)
        cls.identity = _query_file(IDENTITY_QUERY)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.query.unlink(missing_ok=True)
        cls.identity.unlink(missing_ok=True)

    def test_the_bare_fixture_anchors(self) -> None:
        ok, why, nodes = HB.bind_anchored(ANCHOR_MODULE, self.query)
        self.assertTrue(ok, why)
        self.assertEqual(nodes, 2)

    def test_the_bare_fixture_is_NOT_structurally_bindable(self) -> None:
        """The two verdicts are answers to different questions, and this fixture
        is the case that separates them. Without this the anchored class could be
        quietly folded into the structural one."""
        ok, why, _n = HB.bind_structural(ANCHOR_MODULE, self.query)
        self.assertFalse(ok)
        self.assertIn("carries no structure", why)

    def test_the_same_query_with_the_negation_REMOVED_does_not_anchor(self) -> None:
        """The sharpest control here: identical symbols, identical equalities,
        identical module — only the polarity differs. A checker that matched the
        pair against any `(= L R)` in the file, rather than against the ones the
        file FORCES false, passes this and must not."""
        flipped = _query_file(
            ANCHOR_QUERY.replace(
                "(bvnot (bvor (bvnot (bvand (ite (= a0 a1) #b1 #b0) "
                "(ite (= a1 a2) #b1 #b0))) (ite (= a0 a2) #b1 #b0)))",
                "(bvand (bvand (ite (= a0 a1) #b1 #b0) (ite (= a1 a2) #b1 #b0)) "
                "(ite (= a0 a2) #b1 #b0))",
            )
        )
        try:
            ok, why, _n = HB.bind_anchored(ANCHOR_MODULE, flipped)
            self.assertFalse(ok)
            self.assertIn("force 0 disequalities", why)
        finally:
            flipped.unlink(missing_ok=True)

    def test_a_query_forcing_several_is_refused_as_ambiguous(self) -> None:
        """`solver__array__ext27.btor.smt2`, in miniature: four forced leaf
        disequalities and a module that does not say which it means. An anchor
        that picks one of several is not an anchor — this is the requirement that
        keeps the class from being a formality, and it declines a real corpus
        instance."""
        ambiguous = _query_file(
            "(assert (and (not (= i0 i1)) (not (= v5 v6)) (not (= i0 i2))))"
        )
        try:
            ok, why, _n = HB.bind_anchored(ANCHOR_MODULE, ambiguous)
            self.assertFalse(ok)
            self.assertIn("3 different disequalities", why)
        finally:
            ambiguous.unlink(missing_ok=True)

    def test_a_query_forcing_none_is_refused(self) -> None:
        """The two `unsat__replace_all__not-first-only` rows, in miniature."""
        none = _query_file("(assert (= a b))")
        try:
            ok, why, _n = HB.bind_anchored(ANCHOR_MODULE, none)
            self.assertFalse(ok)
            self.assertIn("force 0 disequalities", why)
        finally:
            none.unlink(missing_ok=True)

    def test_a_forced_pair_of_equal_sides_cannot_bind_two_names(self) -> None:
        """`solver__array__ext10.btor.smt2` forces `¬(a0 = a0)` and nothing else.
        Injectivity refuses it, which is why that instance stays attested."""
        reflexive = _query_file("(assert (not (= a0 a0)))")
        try:
            ok, _why, _n = HB.bind_anchored(ANCHOR_MODULE, reflexive)
            self.assertFalse(ok)
        finally:
            reflexive.unlink(missing_ok=True)

    def test_a_bare_side_never_stands_for_a_compound_forced_term(self) -> None:
        """`cvc5__redand-eliminate.smt2` forces one disequality, between two
        APPLICATIONS the rewriter produced. A bare constant cannot stand for
        one, so that instance stays attested rather than anchoring vacuously."""
        compound = _query_file("(assert (not (= (bvredand x) (bvcomp x #b111111))))")
        try:
            ok, _why, _n = HB.bind_anchored(ANCHOR_MODULE, compound)
            self.assertFalse(ok)
        finally:
            compound.unlink(missing_ok=True)

    def test_a_module_stating_no_disequality_is_refused(self) -> None:
        positive = "\n".join(
            line
            for line in ANCHOR_MODULE.splitlines()
            if "hyp._3" not in line and "theorem" not in line
        )
        ok, why, _n = HB.bind_anchored(positive, self.query)
        self.assertFalse(ok)
        self.assertIn("assumes no DISEQUALITY", why)

    def test_two_hypotheses_over_DIFFERENT_pairs_are_refused(self) -> None:
        """Anchoring identifies one pair. A module equating two different pairs
        would need the query to entail a specific one of them, and nothing here
        says which — so the shape is refused rather than guessed at."""
        mixed = ANCHOR_MODULE.replace(
            "axiom axeyum.reconstruct.hyp._2 : Eq.{1} α axeyum.reconstruct.atom._0 "
            "axeyum.reconstruct.atom._1",
            "axiom axeyum.reconstruct.hyp._2 : Eq.{1} α axeyum.reconstruct.atom._1 "
            "axeyum.reconstruct.atom._0",
        )
        self.assertNotEqual(mixed, ANCHOR_MODULE)
        ok, why, _n = HB.bind_anchored(mixed, self.query)
        self.assertFalse(ok)
        self.assertIn("a different pair", why)

    def test_an_axiom_beyond_the_opaque_sort_is_refused(self) -> None:
        smuggled = ANCHOR_MODULE.replace(
            "axiom α : Sort (1)", "axiom α : Sort (1)\naxiom Int.one : Int"
        )
        ok, why, _n = HB.bind_anchored(smuggled, self.query)
        self.assertFalse(ok)
        self.assertIn("opaque sort", why)

    def test_a_declared_constant_no_rendered_term_uses_is_refused(self) -> None:
        spare = ANCHOR_MODULE.replace(
            "axiom axeyum.reconstruct.hyp._2",
            "axiom axeyum.reconstruct.atom._9 : α\naxiom axeyum.reconstruct.hyp._2",
        )
        ok, why, _n = HB.bind_anchored(spare, self.query)
        self.assertFalse(ok)
        self.assertIn("no rendered term binds it", why)

    def test_retargeting_a_leaf_is_caught(self) -> None:
        damaged = HB.mutate_structural_module(ANCHOR_MODULE, "retarget-leaf")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_anchored(damaged, self.query)
        self.assertFalse(ok)

    def test_collapsing_two_constants_is_caught(self) -> None:
        damaged = HB.mutate_structural_module(ANCHOR_MODULE, "collapse-two-constants")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_anchored(damaged, self.query)
        self.assertFalse(ok)

    def test_the_structured_identity_fixture_anchors(self) -> None:
        ok, why, nodes = HB.bind_anchored(IDENTITY_MODULE, self.identity)
        self.assertTrue(ok, why)
        self.assertEqual(nodes, 1 + 4)

    def test_swapping_the_identity_arguments_is_caught(self) -> None:
        """`(ite true x y)` becomes `(ite x true y)`, which the file does not
        contain. Only the match against the query can catch it — no name is
        added or removed — and it is the structure that makes THIS module's
        correspondence pinned by more than uniqueness."""
        damaged = HB.mutate_structural_module(IDENTITY_MODULE, "swap-arguments")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_anchored(damaged, self.identity)
        self.assertFalse(ok)

    def test_dropping_an_identity_argument_is_caught(self) -> None:
        damaged = HB.mutate_structural_module(IDENTITY_MODULE, "drop-argument")
        self.assertIsNotNone(damaged)
        ok, _why, _n = HB.bind_anchored(damaged, self.identity)
        self.assertFalse(ok)

    def test_the_bare_module_does_NOT_anchor_against_the_identity_query(self) -> None:
        """The honest limit, driven rather than asserted. The identity query
        forces exactly one disequality, but its sides are `x` and a four-node
        `ite`, so a bare pair cannot stand for it. Two queries whose forced pairs
        are both LEAVES would accept each other's bare module — that is what the
        anchored manifest says out loud."""
        ok, _why, _n = HB.bind_anchored(ANCHOR_MODULE, self.identity)
        self.assertFalse(ok)


# ---------------------------------------------------------------------------
# A negated conjunction of equalities — the `FiniteArrayExtensionality` shape
# ---------------------------------------------------------------------------

CONJUNCTION_QUERY = """
(set-logic QF_AUFBV)
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun b () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= (select a (_ bv0 1)) (select b (_ bv0 1))))
(assert (= (select a (_ bv1 1)) (select b (_ bv1 1))))
(assert (not (= a b)))
(check-sat)
"""

# The module `ProofFragment::FiniteArrayExtensionality` renders for that query:
# every read spelled out, and the refutation `¬(r₀ ∧ r₁)` rather than one
# equality and its negation. atom._0 = a, atom._1 = (_ bv0 1), func._2 = select,
# atom._3 = b, atom._5 = (_ bv1 1).
_R0 = (
    "(axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1) "
    "(axeyum.reconstruct.func._2 axeyum.reconstruct.atom._3 axeyum.reconstruct.atom._1)"
)
_R1 = (
    "(axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._5) "
    "(axeyum.reconstruct.func._2 axeyum.reconstruct.atom._3 axeyum.reconstruct.atom._5)"
)
CONJUNCTION_MODULE = f"""
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.func._2 : ((x0 : α) -> ((x1 : α) -> α))
axiom axeyum.reconstruct.atom._3 : α
axiom axeyum.reconstruct.atom._5 : α
axiom axeyum.reconstruct.hyp._4 : Eq.{{1}} α {_R0}
axiom axeyum.reconstruct.hyp._6 : Eq.{{1}} α {_R1}
axiom axeyum.reconstruct.hyp._7 : Not (And (Eq.{{1}} α {_R0}) (Eq.{{1}} α {_R1}))
theorem axeyum_refutation : False := trivial
"""


class ANegatedConjunctionOfEqualitiesIsStructural(unittest.TestCase):
    """`FiniteArrayExtensionality` refutes `¬(r₁ ∧ … ∧ rₙ)`, not `t = u` and its
    negation. All four committed instances were pinned as transcribing NOTHING
    until 2026-08-18 — not because the certificate lacked the terms (its reads
    are the query's own `TermId`s) but because the emitter collapsed each
    `(select a i)` into one opaque constant, and then no checker could see the
    shape either. Both halves are fixed; this pins the checker half."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.query = _query_file(CONJUNCTION_QUERY)

    def test_the_conjunction_module_binds_structurally(self) -> None:
        ok, why, nodes = HB.bind_structural(CONJUNCTION_MODULE, self.query)
        self.assertTrue(ok, why)
        # Four rendered terms of three nodes each, counted twice: once in the
        # two `Eq` hypotheses and once inside the negated conjunction.
        self.assertEqual(nodes, 24)

    def test_it_does_NOT_anchor(self) -> None:
        """A negated conjunction is not a fact about either conjunct, so there is
        no single disequality for the query to have to force. `structural` is the
        whole verdict these four earn, and the anchored pin must be refused."""
        ok, why, _n = HB.bind_anchored(CONJUNCTION_MODULE, self.query)
        self.assertFalse(ok)
        self.assertIn("equates a different pair", why)

    def test_a_term_the_file_does_not_contain_is_refused(self) -> None:
        """The twin for the acceptance above. `(select (_ bv1 1) a)` is a
        three-node application of the same arity, so only the match against the
        query's own subterms can reject it."""
        damaged = CONJUNCTION_MODULE.replace(
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._5",
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._5 axeyum.reconstruct.atom._0",
        )
        self.assertNotEqual(damaged, CONJUNCTION_MODULE)
        ok, _why, _n = HB.bind_structural(damaged, self.query)
        self.assertFalse(ok)

    def test_EVERY_conjunct_is_checked_not_just_the_first(self) -> None:
        """The conjunction walker must collect both sides of both conjuncts. If
        it short-circuited, a module whose SECOND conjunct names a term the file
        does not contain would still bind — and the corruption above would be
        caught only by the standalone `hyp._6`, which a renderer need not emit."""
        second_only = "\n".join(
            line
            for line in CONJUNCTION_MODULE.splitlines()
            if "axeyum.reconstruct.hyp._6" not in line
            and "axeyum.reconstruct.hyp._4" not in line
        ).replace(
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._5",
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._5 axeyum.reconstruct.atom._0",
        )
        ok, _why, _n = HB.bind_structural(second_only, self.query)
        self.assertFalse(ok)

    def test_the_same_module_without_the_corruption_still_binds(self) -> None:
        """Without this twin the test above would pass against a binder that
        refused every module carrying only the conjunction."""
        conjunction_only = "\n".join(
            line
            for line in CONJUNCTION_MODULE.splitlines()
            if "axeyum.reconstruct.hyp._6" not in line
            and "axeyum.reconstruct.hyp._4" not in line
        )
        ok, why, nodes = HB.bind_structural(conjunction_only, self.query)
        self.assertTrue(ok, why)
        self.assertEqual(nodes, 12)

    def test_a_connective_outside_the_grammar_is_refused(self) -> None:
        """The grammar is `Not`, `And` and `Eq`, and it is CLOSED. `Or` is not a
        typo for `And`: a disjunction of equalities says something weaker, and
        admitting it here would let a module state a weaker fact while its terms
        went on matching."""
        widened = CONJUNCTION_MODULE.replace("Not (And ", "Not (Or ")
        ok, why, _n = HB.bind_structural(widened, self.query)
        self.assertFalse(ok)
        self.assertIn("is not built from", why)

    def test_every_corruption_of_the_conjunction_is_caught(self) -> None:
        applied = 0
        for kind in HB.STRUCTURAL_MUTATIONS:
            mutant = HB.mutate_structural_module(CONJUNCTION_MODULE, kind)
            if mutant is None:
                continue
            applied += 1
            ok, _why, _n = HB.bind_structural(mutant, self.query)
            self.assertFalse(ok, kind)
        self.assertEqual(applied, len(HB.STRUCTURAL_MUTATIONS))


class TheStructuralSearchHasABudget(unittest.TestCase):
    """A backtracking matcher over sixteen same-sized sides and sixteen same-sized
    candidates is not obviously terminating in useful time, and the
    `FiniteArrayExtensionality` modules are exactly that shape — measured
    2026-08-18, `smtextarrayaxiom3` ran unbounded for minutes under the old
    static side ordering. A budget without a distinct verdict would be worse than
    none: a search that gave up must read as neither a pass NOR a refutation."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.query = _query_file(CONJUNCTION_QUERY)

    def test_an_exhausted_budget_is_not_a_pass(self) -> None:
        ok, why, nodes = HB.bind_structural(CONJUNCTION_MODULE, self.query, budget=1)
        self.assertFalse(ok)
        self.assertIn("exhausted", why)
        self.assertEqual(nodes, 0)

    def test_the_same_module_binds_inside_the_real_budget(self) -> None:
        ok, why, _n = HB.bind_structural(CONJUNCTION_MODULE, self.query)
        self.assertTrue(ok, why)

    def test_the_exhaustion_verdict_is_distinguishable_from_a_refutation(self) -> None:
        """The two failures must not be told apart only by a human reading prose:
        an exhausted budget is this checker failing to decide, a refusal is the
        module failing to transcribe, and a regression that turned every instance
        into the former would otherwise look like a corpus of caught defects."""
        _ok, exhausted, _n = HB.bind_structural(
            CONJUNCTION_MODULE, self.query, budget=1
        )
        widened = CONJUNCTION_MODULE.replace(
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._5",
            "axeyum.reconstruct.func._2 axeyum.reconstruct.atom._5 axeyum.reconstruct.atom._0",
        )
        _ok, refused, _n = HB.bind_structural(widened, self.query)
        self.assertNotEqual(exhausted, refused)
        self.assertNotIn("exhausted", refused)


class TheAnchoredManifestIsRealAndOnlyGrows(unittest.TestCase):
    def test_every_pinned_instance_exists(self) -> None:
        pinned = HB.anchored_instances()
        # `corpus/` is excluded from the mutation harness's scratch tree, so its
        # absence there is not a manifest defect; everything else must be present.
        if not (ROOT / "corpus").is_dir():
            pinned = [p for p in pinned if not p.startswith("corpus/")]
        missing = [p for p in pinned if not (ROOT / p).is_file()]
        self.assertEqual(missing, [])

    def test_the_manifest_meets_its_own_floor(self) -> None:
        """`MIN_ANCHORED` floors how many modules ANCHOR, which since the four
        verdicts became a partition is this manifest PLUS the dual one -- those
        rows anchor too, they simply also bind structurally. Comparing the floor
        against this file alone would read the split as a collapse."""
        self.assertGreaterEqual(
            len(HB.anchored_instances()) + len(HB.structural_anchored_instances()),
            HB.MIN_ANCHORED,
        )

    def test_the_dual_manifest_meets_its_own_floor(self) -> None:
        self.assertGreaterEqual(
            len(HB.structural_anchored_instances()), HB.MIN_STRUCTURAL_ANCHORED
        )

    def test_every_pinned_dual_instance_exists(self) -> None:
        pinned = HB.structural_anchored_instances()
        if not (ROOT / "corpus").is_dir():
            pinned = [p for p in pinned if not p.startswith("corpus/")]
        self.assertEqual([p for p in pinned if not (ROOT / p).is_file()], [])

    def test_no_instance_is_pinned_in_two_classes(self) -> None:
        """The four verdicts are a PARTITION of the instances that render a
        module. An instance in two manifests would be checked twice and would
        pass on whichever half it happened to satisfy -- and the dual verdict is
        deliberately NOT expressed that way, as membership of both the
        `structural` and `anchored` files, for exactly that reason: it is its own
        manifest with its own two-sided pin."""
        classes = {
            "bound": set(HB.manifest_instances()),
            "structural": set(HB.structural_instances()),
            "structural-anchored": set(HB.structural_anchored_instances()),
            "anchored": set(HB.anchored_instances()),
            "attested": set(HB.attestation_instances()),
            "declined": set(HB.declined_instances()),
        }
        names = sorted(classes)
        for i, left in enumerate(names):
            for right in names[i + 1 :]:
                self.assertEqual(
                    classes[left] & classes[right], set(), f"{left} vs {right}"
                )


class TheFourVerdictsCannotAbsorbEachOther(unittest.TestCase):
    """Each verdict is a different claim, and the run must refuse an instance
    pinned to the wrong one. The `attested` claim is the fragile one: it says the
    module relates to the query in NO way, and it silently stopped being true for
    six instances once before."""

    def _run_driver(self, module: str, query: str, *extra: str) -> int:
        import tempfile

        with tempfile.TemporaryDirectory() as scratch:
            qpath = pathlib.Path(scratch) / "q.smt2"
            mpath = pathlib.Path(scratch) / "m.lean"
            qpath.write_text(query, encoding="utf-8")
            mpath.write_text(module, encoding="utf-8")
            return HB.main(
                [
                    "--instance", str(qpath),
                    "--module", str(mpath),
                    "--no-build",
                    "--no-self-check",
                    "--min-instances", "0",
                    "--min-hypotheses", "0",
                    "--min-required-mutations", "0",
                    "--min-attestations", "0",
                    "--min-represented", "0",
                    "--min-structural", "0",
                    "--min-structural-nodes", "0",
                    "--min-structural-mutations", "0",
                    "--min-anchored", "0",
                    "--min-anchored-nodes", "0",
                    "--min-anchored-mutations", "0",
                    "--min-structural-anchored", "0",
                    *extra,
                ]
            )

    def test_the_anchored_fixture_passes_when_pinned_anchored(self) -> None:
        self.assertEqual(
            self._run_driver(ANCHOR_MODULE, ANCHOR_QUERY, "--expect", "anchored"), 0
        )

    def test_an_anchorable_module_pinned_as_attested_fails(self) -> None:
        """The anti-absorption guard for the new class. An attestation claims the
        query says nothing about what the module assumes; if the query FORCES it,
        uniquely, that claim is false. Without this the anchored class could
        never grow, because an instance that became anchorable would sit green in
        the attested one."""
        self.assertEqual(
            self._run_driver(ANCHOR_MODULE, ANCHOR_QUERY, "--expect", "attested"), 1
        )

    def test_the_same_module_IS_attested_against_a_query_that_forces_nothing(
        self,
    ) -> None:
        """The twin. Without it the test above would pass against a driver that
        failed every `attested` run."""
        self.assertEqual(
            self._run_driver(ANCHOR_MODULE, "(assert (= a b))", "--expect", "attested"),
            0,
        )

    def test_an_unanchorable_module_pinned_as_anchored_fails(self) -> None:
        self.assertEqual(
            self._run_driver(ANCHOR_MODULE, "(assert (= a b))", "--expect", "anchored"),
            1,
        )

    def test_a_structural_module_pinned_as_attested_fails_without_anchoring(
        self,
    ) -> None:
        """The OTHER anti-absorption guard, driven where only it can fire. The
        structural fixture's own query also anchors, so a test using it would
        pass with the structural guard removed — the anchored guard would catch
        it instead, and the structural one would sit there untested. This query
        contains both rendered terms and forces no disequality at all, so only
        `bind_structural` can refuse the `attested` pin."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "attested",
            ),
            1,
        )

    def test_a_structural_module_ALSO_anchors_when_the_query_forces_it(self) -> None:
        """The two verdicts are not nested but they do overlap, and the overlap
        is now its own verdict. `STRUCTURAL_QUERY` asserts the disequality
        outright, so this module is both structurally bound AND anchored.
        Measured over the corpus, 66 instances are in that position -- the
        largest of the four classes."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE, STRUCTURAL_QUERY, "--expect", "structural-anchored"
            ),
            0,
        )

    def test_a_dual_module_pinned_as_structural_ONLY_fails(self) -> None:
        """The anti-absorption guard in the direction that did not exist before:
        a row that also anchors must not go on being recorded as merely
        structural. Without it the dual class can only be entered by hand, and a
        stronger statement that becomes true stays unrecorded forever -- which is
        precisely the state 66 instances were in until this was measured."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE, STRUCTURAL_QUERY, "--expect", "structural"
            ),
            1,
        )

    def test_a_dual_module_pinned_as_anchored_ONLY_fails(self) -> None:
        """The same guard from the other side. `anchored` alone claims the
        structural binder cannot grip the module, and for the 7 bare-pair rows
        left in that class it genuinely cannot -- that admission is the whole
        content of the class, so it must be checked and not asserted."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE, STRUCTURAL_QUERY, "--expect", "anchored"
            ),
            1,
        )

    def test_a_bare_pair_module_is_STILL_anchored_only(self) -> None:
        """The twin for both guards above: they must not degrade into a driver
        that refuses `structural` and `anchored` outright. `ANCHOR_MODULE` is a
        bare pair, which `bind_structural` refuses by design, so `anchored`
        alone is its correct pin and must pass."""
        self.assertEqual(
            self._run_driver(ANCHOR_MODULE, ANCHOR_QUERY, "--expect", "anchored"), 0
        )

    def test_a_structural_module_does_NOT_anchor_on_a_congruence_conclusion(
        self,
    ) -> None:
        """The other 32, and the reason `structural` exists as its own verdict:
        the module's equality is the CONCLUSION of a congruence derivation, and
        no assertion says the query forces it false. Both of the module's terms
        are still subterms of this query — so only the polarity separates this
        case from the one above."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "anchored",
            ),
            1,
        )


# The shape that shipped: `cvc5__cli__regress0__bv__holes__extract-concat.smt2`
# rendered eleven reflexive `Iff`s under one negation. `Iff p p` is provable, so
# the conjunction is provable, so this ONE axiom refutes itself and the module's
# `False` needs nothing from the query. Trimmed to three conjuncts.
REFL_IFF_MODULE = """
axiom α : Sort (1)
axiom axeyum.reconstruct.prop._0 : Prop
axiom axeyum.reconstruct.prop._1 : Prop
axiom axeyum.reconstruct.prop._2 : Prop
axiom axeyum.reconstruct.hyp._3 : Not (And (Iff axeyum.reconstruct.prop._0 \
axeyum.reconstruct.prop._0) (And (Iff axeyum.reconstruct.prop._1 \
axeyum.reconstruct.prop._1) (Iff axeyum.reconstruct.prop._2 \
axeyum.reconstruct.prop._2)))
theorem axeyum_refutation : False := trivial
"""

# The SAME module with one conjunct relating two DIFFERENT props. That
# conjunction is not provable by reflexivity, so the axiom is a real assumption
# about the query and this must NOT be reported.
HONEST_IFF_MODULE = REFL_IFF_MODULE.replace(
    "(Iff axeyum.reconstruct.prop._1 axeyum.reconstruct.prop._1)",
    "(Iff axeyum.reconstruct.prop._1 axeyum.reconstruct.prop._2)",
)


# A module whose two equated sides are the SAME structured term. It binds
# structurally -- both sides really are `select(store(a,i,v), j)`, a subterm of
# the query -- and it is self-refuting, because `Not (Eq α t t)` is `rfl`. Only
# the run-wide check sees it: `classify_attestation`'s copy was never consulted
# for an instance pinned `structural`.
SELF_REFUTING_STRUCTURAL_MODULE = """
axiom α : Sort (1)
axiom axeyum.reconstruct.atom._0 : α
axiom axeyum.reconstruct.atom._1 : α
axiom axeyum.reconstruct.atom._2 : α
axiom axeyum.reconstruct.atom._3 : α
axiom axeyum.reconstruct.func._4 : ((x0 : α) -> ((x1 : α) -> ((x2 : α) -> α)))
axiom axeyum.reconstruct.func._5 : ((x0 : α) -> ((x1 : α) -> α))
axiom axeyum.reconstruct.hyp._6 : Not (Eq.{1} α (axeyum.reconstruct.func._5 \
(axeyum.reconstruct.func._4 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1 \
axeyum.reconstruct.atom._2) axeyum.reconstruct.atom._3) (axeyum.reconstruct.func._5 \
(axeyum.reconstruct.func._4 axeyum.reconstruct.atom._0 axeyum.reconstruct.atom._1 \
axeyum.reconstruct.atom._2) axeyum.reconstruct.atom._3))
theorem axeyum_refutation : False := trivial
"""

# `STRUCTURAL_MODULE` with one leaf renamed to a token the skeleton grammar does
# not admit. It still binds structurally (`Int.one` stands for `j`) but it is no
# longer a content-free attestation -- which is what makes it the fixture that
# isolates the DECLINED class's structural guard from its attestation guard.
STRUCTURAL_NOT_ATTESTED_MODULE = "\n".join(
    line
    for line in STRUCTURAL_MODULE.replace(
        "axeyum.reconstruct.atom._3", "Int.one"
    ).splitlines()
    if line.strip() != "axiom Int.one : α"
)


class AModuleThatRefutesItselfCorroboratesNothing(unittest.TestCase):
    """`Not X` with `X` provable by reflexivity alone.

    Lean accepts such a module, `#print axioms` is clean, and the identical
    module would be accepted for a query that said something else — the
    derivation never reads the file. Two have existed in this corpus. The first
    (`Not (Eq.{1} α t t)`) was found in 2026-08-18's attestation sweep and its
    route made to decline; the second was found only by widening the predicate
    from that one shape to the property, and it was sitting in the DECLINED list
    where no check ran at all.

    Both halves are driven: the discriminating test is not that reflexive
    conjunctions are caught, it is that a conjunction with ONE honest conjunct is
    not.
    """

    def test_the_narrow_rfl_shape_is_still_recognized(self) -> None:
        self.assertTrue(HB._is_self_refuting("Not (Eq.{1} α a a)"))

    def test_a_negated_conjunction_of_reflexive_iffs_is_recognized(self) -> None:
        self.assertTrue(HB._is_self_refuting("Not (And (Iff p p) (And (Iff q q) (Iff r r)))"))

    def test_ONE_honest_conjunct_makes_it_a_real_assumption(self) -> None:
        self.assertFalse(HB._is_self_refuting("Not (And (Iff p p) (And (Iff q r) (Iff s s)))"))

    def test_a_disequality_between_DIFFERENT_terms_is_a_real_assumption(self) -> None:
        self.assertFalse(HB._is_self_refuting("Not (Eq.{1} α a b)"))

    def test_an_Or_is_refused_even_though_one_disjunct_is_reflexive(self) -> None:
        """The grammar is CLOSED on purpose. `Or (Iff p p) X` really is provable,
        but admitting `Or` here would start this predicate reasoning rather than
        recognizing, and a wrong yes takes down a sound route."""
        self.assertFalse(HB._is_self_refuting("Not (Or (Iff p p) (Iff q q))"))

    def test_an_unnegated_reflexive_conjunction_is_not_self_refuting(self) -> None:
        """`And (Iff p p) (Iff q q)` is provable, which makes it useless, not
        contradictory. Only its NEGATION hands the module a free `False`."""
        self.assertFalse(HB._is_self_refuting("And (Iff p p) (Iff q q)"))

    def test_the_scan_reads_EVERY_axiom_not_only_the_hypotheses(self) -> None:
        """`classify_attestation` could only ever see the class it was already
        looking at. The corpus's second self-refuting module was in the declined
        list; nothing ran on it."""
        found = HB.self_refuting_axioms(REFL_IFF_MODULE)
        self.assertEqual(found, ["axeyum.reconstruct.hyp._3"])

    def test_the_honest_twin_is_reported_clean(self) -> None:
        self.assertEqual(HB.self_refuting_axioms(HONEST_IFF_MODULE), [])

    def test_a_module_with_no_axiom_at_all_is_reported_clean(self) -> None:
        self.assertEqual(HB.self_refuting_axioms("theorem t : False := trivial"), [])


class TheDeclinedClassIsPinnedAndTwoSided(unittest.TestCase):
    """The residue nothing used to run on.

    Until 2026-08-18 the declined instances were a comment inside the attestation
    manifest, explicitly "NOT checked". A class nothing runs on can only be
    entered: an instance that becomes bindable stays declined forever. The pin
    can therefore only fail by an instance getting BETTER, which is the direction
    this repository has twice found by measurement rather than by a check.
    """

    def _run_driver(self, module: str, query: str, *extra: str) -> int:
        import tempfile

        with tempfile.TemporaryDirectory() as scratch:
            qpath = pathlib.Path(scratch) / "q.smt2"
            mpath = pathlib.Path(scratch) / "m.lean"
            qpath.write_text(query, encoding="utf-8")
            mpath.write_text(module, encoding="utf-8")
            return HB.main(
                [
                    "--instance", str(qpath),
                    "--module", str(mpath),
                    "--no-build",
                    "--no-self-check",
                    "--min-instances", "0",
                    "--min-hypotheses", "0",
                    "--min-required-mutations", "0",
                    "--min-attestations", "0",
                    "--min-represented", "0",
                    "--min-structural", "0",
                    "--min-structural-nodes", "0",
                    "--min-structural-mutations", "0",
                    "--min-anchored", "0",
                    "--min-anchored-nodes", "0",
                    "--min-anchored-mutations", "0",
                    "--min-structural-anchored", "0",
                    "--min-declined", "0",
                    *extra,
                ]
            )

    def test_every_pinned_instance_exists(self) -> None:
        pinned = HB.declined_instances()
        if not (ROOT / "corpus").is_dir():
            pinned = [p for p in pinned if not p.startswith("corpus/")]
        self.assertEqual([p for p in pinned if not (ROOT / p).is_file()], [])

    def test_the_manifest_meets_its_own_floor(self) -> None:
        self.assertGreaterEqual(len(HB.declined_instances()), HB.MIN_DECLINED)

    def test_a_declined_pin_is_refused_when_the_module_binds_structurally(self) -> None:
        """The whole point: an instance that got better must not stay filed as
        beyond reach."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "declined",
            ),
            1,
        )

    def test_a_declined_pin_is_refused_when_the_module_is_an_attestation(self) -> None:
        self.assertEqual(
            self._run_driver(
                ANCHOR_MODULE,
                "(assert (bvult p q))",
                "--expect",
                "declined",
            ),
            1,
        )

    def test_a_self_refuting_module_that_BINDS_still_fails(self) -> None:
        """The case only the run-wide check catches. This module's rendered terms
        ARE the query's, injectively -- so `structural` passes on it -- and its
        `False` is still free. The old check lived inside `classify_attestation`
        and was never consulted for an instance pinned to another class."""
        self.assertEqual(
            self._run_driver(
                SELF_REFUTING_STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "structural",
            ),
            1,
        )

    def test_the_same_module_with_DIFFERENT_sides_passes_as_structural(self) -> None:
        """The twin. Without it the test above is satisfied by a checker that
        refuses every structural module."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "structural",
            ),
            0,
        )

    def test_a_declined_pin_is_refused_when_a_NON_attestation_binds(self) -> None:
        """Isolates the DECLINED class's structural guard. `STRUCTURAL_MODULE`
        itself is also a content-free skeleton, so the attestation guard would
        catch it either way and the structural guard could be deleted with every
        test still green -- which is what the mutation control reported."""
        self.assertEqual(
            self._run_driver(
                STRUCTURAL_NOT_ATTESTED_MODULE,
                "(assert (bvult (select (store a i v) j) (select a j)))",
                "--expect",
                "declined",
            ),
            1,
        )

    def test_a_self_refuting_module_fails_whatever_class_it_is_pinned_to(self) -> None:
        """The check runs BEFORE the verdict, so `declined` cannot shelter it."""
        for want in ("declined", "attested", "structural", "bound"):
            with self.subTest(want=want):
                self.assertEqual(
                    self._run_driver(
                        REFL_IFF_MODULE, "(assert (bvult p q))", "--expect", want
                    ),
                    1,
                )


if __name__ == "__main__":
    unittest.main()
