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
        self.assertEqual(smt, [("<=", (("s_a", -1),), 6)])
        self.assertEqual(HB.signature(smt[0]), HB.signature(rendered))

    def test_a_leaf_outside_the_query_namespace_is_not_silently_a_variable(self) -> None:
        """A rendered constant this checker does not know must not become a fresh
        free variable that then matches anything."""
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom("Real.le (Real.add v Real.zero) Real.zero", "Real")

    def test_scaling_by_a_positive_rational_is_the_same_atom(self) -> None:
        half = HB.canonical("<=", {"x": Fraction(1, 2)}, Fraction(-3, 2))
        whole = HB.canonical("<=", {"x": Fraction(2)}, Fraction(-6))
        self.assertEqual(half, whole)

    def test_scaling_by_a_negative_rational_is_NOT_the_same_atom(self) -> None:
        """`x ≤ 0` and `−x ≤ 0` are different facts, and a normalizer that
        divided by a signed gcd would fuse them."""
        self.assertNotEqual(
            HB.canonical("<=", {"x": Fraction(1)}, Fraction(0)),
            HB.canonical("<=", {"x": Fraction(-1)}, Fraction(0)),
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

    HYPS = [("h", "Real", ("<=", (("v0", 1), ("v1", -1)), 5))]
    CARRIERS = {"v0": "Real", "v1": "Real"}
    SORTS = {"s_a": "Real", "s_b": "Real", "n": "Int"}
    ALLOWED = {("<=", (("s_a", 1), ("s_b", -1)), 5)}

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
            [("<", (("x", -1), ("y", 1)), 0)],
        )

    def test_an_equality_contributes_both_bounds(self) -> None:
        atoms = HB.atoms_of(["=", "x", "2"], True, {})
        self.assertIn(("<=", (("x", 1),), -2), atoms)
        self.assertIn(("<=", (("x", -1),), 2), atoms)

    def test_a_disequality_contributes_nothing(self) -> None:
        """`¬(x = 2)` is a DISJUNCTION of two strict bounds, and emitting either
        one alone would be an atom the query does not entail."""
        self.assertEqual(HB.atoms_of(["not", ["=", "x", "2"]], True, {}), [])

    def test_a_nonlinear_product_contributes_nothing(self) -> None:
        self.assertEqual(HB.atoms_of(["<=", ["*", "x", "y"], "0"], True, {}), [])

    def test_a_let_binding_is_expanded(self) -> None:
        atoms = HB.atoms_of(["let", [["u", ["+", "x", "1"]]], [">=", "u", "0"]], True, {})
        self.assertEqual(atoms, [("<=", (("x", -1),), -1)])


class ARenderedShapeThisCheckerCannotReadIsAFailureNotASkip(unittest.TestCase):
    def test_an_unknown_rendered_head_raises(self) -> None:
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom("Real.le (Real.sqrt v) Real.zero", "Real")

    def test_a_nonlinear_rendered_product_raises(self) -> None:
        with self.assertRaises(HB.Unsupported):
            HB.lean_atom("Real.le (Real.mul v0 v1) Real.zero", "Real")

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


if __name__ == "__main__":
    unittest.main()
