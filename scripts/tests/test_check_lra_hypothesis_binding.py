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
            HB.canonical("=", {"a": Fraction(1), "b": Fraction(-1)}, Fraction(0)),
            HB.canonical("=", {"a": Fraction(-1), "b": Fraction(1)}, Fraction(0)),
        )

    def test_an_equality_assertion_contributes_both_orientations(self) -> None:
        atoms = HB.atoms_of(["=", "value", ["+", "x_squared", "1"]], True, {})
        equalities = [a for a in atoms if a[0] == "="]
        self.assertEqual(len(equalities), 2)
        self.assertIn(("=", (("value", 1), ("x_squared", -1)), -1), equalities)
        self.assertIn(("=", (("value", -1), ("x_squared", 1)), 1), equalities)

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
            HB.canonical("=", {D0: Fraction(2), D1: Fraction(1)}, Fraction(-1)),
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
            HB.canonical("=", {D0: Fraction(1), D1: Fraction(1)}, Fraction(-2)),
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
            HB.canonical("=", {D0: Fraction(-1), D1: Fraction(-1)}, Fraction(1)),
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
        spine, covered = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual(spine, 3)
        # `(= y 0)` is never rendered: two hypotheses, two represented rows.
        self.assertEqual(covered, 2)

    def test_a_module_rendering_every_row_is_fully_represented(self) -> None:
        module = DIO_MODULE.replace(
            "theorem axeyum_refutation",
            f"axiom axeyum.reconstruct.dio.hyp._4 : Eq.{{1}} Int {D1} Int.zero\n"
            "theorem axeyum_refutation",
        )
        sorts, assertions = _read(DIO_QUERY)
        phi, hypotheses, _allowed, detail = run(module, DIO_QUERY)
        self.assertIsNotNone(phi, detail)
        spine, covered = HB.represented_assertions(
            phi, hypotheses, list(range(len(assertions))), assertions
        )
        self.assertEqual((spine, covered), (3, 3))


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
        self.assertEqual(atoms, [("<=", (("x", -1),), -1)])


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


if __name__ == "__main__":
    unittest.main()
