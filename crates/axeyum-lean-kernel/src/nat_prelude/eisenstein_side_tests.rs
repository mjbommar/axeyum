//! Tests for [`nat_prelude::eisenstein_side`](super::eisenstein_side).
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! per this repository's standing merge-hazard note: two lanes editing that one
//! file at once produce a conflict git cuts mid-item.
//!
//! Three kinds of check, because they fail on disjoint defect classes:
//!
//! 1. **Concrete instantiation, with every hypothesis actually discharged.**
//!    The statement is a negation, so there is no value to evaluate — what a
//!    numeral check buys here is that the theorem *applies*: the coprimality
//!    proof is `Eq.refl` (so `Nat.gcd` really does reduce to `1` at the pair),
//!    the positivity and bound proofs are built from the `Nat.le` constructors,
//!    and the inferred conclusion is checked against the arithmetic negation it
//!    is supposed to be. Two prime pairs, `(3,5)` and `(5,7)`, with small
//!    magnitudes because every numeral in this prelude is unary.
//! 2. **The declared types, rendered.** This is the probe for *admitted, true,
//!    and not your theorem*: the four binders can be transposed consistently in
//!    both the type and the value, and only the stated type sees it.
//! 3. **A negative control that fires on the transposition.** Putting the
//!    bound on `y` instead of `x` gives a FALSE statement, and `3·5 = 5·3` is
//!    the witness: the test asserts that equation holds, so the transposed
//!    reading would be refuted at an instance the intended reading never
//!    reaches.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// A proof of `Le a b` for concrete `a <= b`, by `Nat.le.refl` followed by
    /// `b - a` applications of `Nat.le.step`. Built here rather than taken from
    /// a lemma so the test depends on the two `Nat.le` constructors only.
    fn le_proof(&mut self, a: u32, b: u32) -> ExprId {
        assert!(a <= b, "le_proof needs a <= b");
        let p = self.p;
        let a_term = self.num(a);
        let mut proof = self.lemma(p.le_refl, &[a_term]);
        for step in a..b {
            let upper = self.num(step);
            proof = self.lemma(p.le_step, &[a_term, upper, proof]);
        }
        proof
    }
}

/// The general side condition applies at concrete coprime pairs, with the
/// coprimality, positivity and bound hypotheses all discharged.
///
/// `(pp, q, x, y) = (3, 5, 2, 3)`: `0 < 2 < 3`, `gcd 3 5 = 1`, and the
/// conclusion is `3·3 ≠ 5·2`, i.e. `9 ≠ 10`.
/// `(pp, q, x, y) = (5, 7, 3, 4)`: `0 < 3 < 5`, `gcd 5 7 = 1`, and the
/// conclusion is `5·4 ≠ 7·3`, i.e. `20 ≠ 21`.
#[test]
fn the_general_side_condition_applies_at_two_concrete_prime_pairs() {
    let mut f = Fixture::new();
    let p = f.p;

    for (pp_v, q_v, x_v, y_v) in [(3u32, 5u32, 2u32, 3u32), (5, 7, 3, 4)] {
        let pp = f.num(pp_v);
        let q = f.num(q_v);
        let x = f.num(x_v);
        let y = f.num(y_v);

        // `gcd pp q = 1` by reflexivity — this is where `Nat.gcd` must compute.
        let one = f.num(1);
        let cop = f.refl(one);
        // `0 < x`: `x = succ (x-1)`, so `zero_lt_succ` at `x-1`.
        let x_pred = f.num(x_v - 1);
        let pos = f.zero_lt_succ(x_pred);
        // `x < pp`, i.e. `Le (succ x) pp`.
        let bound = f.le_proof(x_v + 1, pp_v);

        let instance = f.lemma(
            p.mul_ne_mul_of_coprime_of_lt,
            &[pp, q, x, y, cop, pos, bound],
        );
        let inferred =
            f.k.infer(instance)
                .expect("the concrete instance must type-check");

        let ppy = f.mul(pp, y);
        let qx = f.mul(q, x);
        let eq_ty = f.eq(ppy, qx);
        let expected = f.const_app(p.logic.not, &[eq_ty]);
        assert!(
            f.k.def_eq(inferred, expected),
            "at (pp,q,x,y) = ({pp_v},{q_v},{x_v},{y_v}) the conclusion must be \
             `{pp_v}*{y_v} <> {q_v}*{x_v}`"
        );

        // The arithmetic the conclusion asserts is genuinely true at these
        // arguments: the two products differ. Without this the instantiation
        // could be checking a vacuous shape.
        assert!(
            !f.k.def_eq(ppy, qx),
            "{pp_v}*{y_v} and {q_v}*{x_v} must be different numerals"
        );
    }
}

/// The `1`-based corollary applies at the same two pairs, with only
/// coprimality and the bound supplied — its positivity obligation is
/// discharged by the `succ` shape and never reaches the caller.
///
/// `(3, 5, x=1, y=2)`: conclusion `3·3 ≠ 5·2`.
/// `(5, 7, x=2, y=3)`: conclusion `5·4 ≠ 7·3`.
#[test]
fn the_succ_corollary_applies_without_a_positivity_hypothesis() {
    let mut f = Fixture::new();
    let p = f.p;

    for (pp_v, q_v, x_v, y_v) in [(3u32, 5u32, 1u32, 2u32), (5, 7, 2, 3)] {
        let pp = f.num(pp_v);
        let q = f.num(q_v);
        let x = f.num(x_v);
        let y = f.num(y_v);

        let one = f.num(1);
        let cop = f.refl(one);
        // `succ x < pp`, i.e. `Le (succ (succ x)) pp`.
        let bound = f.le_proof(x_v + 2, pp_v);

        let instance = f.lemma(
            p.mul_succ_ne_mul_succ_of_coprime,
            &[pp, q, x, y, cop, bound],
        );
        let inferred =
            f.k.infer(instance)
                .expect("the concrete instance must type-check");

        let sx = f.succ(x);
        let sy = f.succ(y);
        let ppy = f.mul(pp, sy);
        let qx = f.mul(q, sx);
        let eq_ty = f.eq(ppy, qx);
        let expected = f.const_app(p.logic.not, &[eq_ty]);
        assert!(
            f.k.def_eq(inferred, expected),
            "at (pp,q,x,y) = ({pp_v},{q_v},{x_v},{y_v}) the corollary's conclusion is wrong"
        );
        assert!(
            !f.k.def_eq(ppy, qx),
            "the corollary's two products must be different numerals"
        );
    }
}

/// The transposed reading — bound on `y`, the index paired with `pp` — is
/// FALSE, and this is its witness.
///
/// `3·5 = 5·3` with `gcd 3 5 = 1` and `y = 5` unbounded: the intended statement
/// does not apply here, because `x = 3` is not below `pp = 3`. A version
/// bounding `y` instead WOULD apply, and would be refuted. No numeral check
/// over instances the intended theorem reaches can see this, which is why the
/// declared types are pinned below.
#[test]
fn the_transposed_reading_is_false_at_this_witness() {
    let mut f = Fixture::new();

    let three = f.num(3);
    let five = f.num(5);
    let left = f.mul(three, five);
    let right = f.mul(five, three);
    assert!(
        f.k.def_eq(left, right),
        "3*5 = 5*3, so bounding the wrong index gives a false statement"
    );

    // Positive control for the `def_eq` above: it is not accepting everything.
    let seven = f.num(7);
    let other = f.mul(five, seven);
    assert!(
        !f.k.def_eq(left, other),
        "positive control: 3*5 and 5*7 are different numerals"
    );
}

/// Both declarations rest on zero axioms.
#[test]
fn the_side_condition_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;

    for name in [
        p.mul_ne_mul_of_coprime_of_lt,
        p.mul_succ_ne_mul_succ_of_coprime,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The two declarations state the types they are supposed to state, pinned
/// character for character against `render_lean`.
///
/// This is the probe for *admitted, true, and not your theorem*. Transposing
/// the four binders consistently in both the type and the value yields a
/// DIFFERENT and false statement (see the witness test above), but nothing
/// mechanical other than the rendered type distinguishes the intended one:
/// every instance the intended theorem reaches is also an instance where the
/// transposed statement happens to hold.
#[test]
fn the_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    for (name, expected) in [
        (p.mul_ne_mul_of_coprime_of_lt, EXPECTED_GENERAL),
        (p.mul_succ_ne_mul_succ_of_coprime, EXPECTED_SUCC),
    ] {
        assert_eq!(
            rendered(&k, name),
            expected,
            "{} states a different type than intended",
            k.display_name(name)
        );
    }

    // The bound is on the index paired with `q` (`x2` below, the third
    // binder), not on the one paired with `pp`. A `contains` query with a
    // positive control, because an empty match and a mistyped pattern are the
    // same observation.
    assert!(
        rendered(&k, p.mul_ne_mul_of_coprime_of_lt).contains("AxNat.lt x2 x0"),
        "the bound must be `x < pp`"
    );
    assert!(
        !rendered(&k, p.mul_ne_mul_of_coprime_of_lt).contains("AxNat.lt x3 x0"),
        "the bound must NOT be on the index paired with pp"
    );
}

const EXPECTED_GENERAL: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : Eq.{1} AxNat (AxNat.gcd x0 x1) (AxNat.succ AxNat.zero)) -> ((x5 : AxNat.lt AxNat.zero x2) -> ((x6 : AxNat.lt x2 x0) -> Not (Eq.{1} AxNat (AxNat.mul x0 x3) (AxNat.mul x1 x2)))))))))";
const EXPECTED_SUCC: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : Eq.{1} AxNat (AxNat.gcd x0 x1) (AxNat.succ AxNat.zero)) -> ((x5 : AxNat.lt (AxNat.succ x2) x0) -> Not (Eq.{1} AxNat (AxNat.mul x0 (AxNat.succ x3)) (AxNat.mul x1 (AxNat.succ x2)))))))))";
