//! Tests for
//! [`nat_prelude::arith_functions_family`](super::arith_functions_family).
//!
//! Same discipline as `arith_functions_tests.rs`: every definition here has a
//! wrong-but-well-typed variant, so each gets an evaluation test at numerals
//! whose reference distinguishes it.
//!
//! - `Nat.dirichlet` would type-check with `g d` instead of `g (n/d)` (that
//!   would make it the pointwise product summed over divisors), and the
//!   control below pins that the two readings give different numbers.
//! - `Nat.moebiusPos`/`Nat.moebiusNeg` would type-check with the parity read
//!   the other way round, so the tests check `μ(2) = -1` and `μ(6) = +1` —
//!   the two cases that separate the readings — as well as `μ(4) = 0`.
//!
//! `Nat.dirichlet_comm` gets an instance at a pair whose SUMMANDS differ
//! term by term (`f 2 · g 3 = 8` against `g 2 · f 3 = 9`) so the theorem is
//! not confirmed by an accidental symmetry.

use crate::env::Declaration;
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

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }

    /// `fun k => k`.
    fn identity(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        self.lam_fv(k_fv, nat, k)
    }

    /// `fun k => succ k`.
    fn succ_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.succ(k);
        self.lam_fv(k_fv, nat, body)
    }

    /// `fun _ => 1`.
    fn one_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let one = self.num(1);
        self.lam_fv(k_fv, nat, one)
    }

    /// `Nat.dirichlet f g n` at a numeral `n`.
    fn dirichlet_at(&mut self, f: ExprId, g: ExprId, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.dirichlet, &[f, g, n])
    }

    /// `Lt zero n` at a literal successor.
    fn positivity(&mut self, n: u32) -> ExprId {
        assert!(n >= 1, "positivity is only available at a successor");
        let pred = self.num(n - 1);
        self.zero_lt_succ(pred)
    }

    fn moebius_pos_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.moebius_pos, &[n])
    }

    fn moebius_neg_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.moebius_neg, &[n])
    }

    fn moebius_abs_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.moebius_abs, &[n])
    }
}

// ---------------------------------------------------------------------------
// The Dirichlet convolution.
// ---------------------------------------------------------------------------

/// The Rust reference: the two readings of the convolution summand
/// (`f d · g (n/d)` and the pointwise `f d · g d`) really do give different
/// numbers at the instance used below.
#[test]
fn the_convolution_readings_are_distinct() {
    let divisors: Vec<u32> = (1..=6).filter(|d| 6_u32.is_multiple_of(*d)).collect();
    assert_eq!(divisors, vec![1, 2, 3, 6]);
    let convolved: u32 = divisors.iter().map(|&d| d * (6 / d + 1)).sum();
    assert_eq!(convolved, 36);
    let pointwise: u32 = divisors.iter().map(|&d| d * (d + 1)).sum();
    // 1*2 + 2*3 + 3*4 + 6*7
    assert_eq!(pointwise, 62);
    assert_ne!(convolved, pointwise);
    // The swapped convolution has the same TOTAL but different TERMS.
    let swapped: u32 = divisors.iter().map(|&d| (d + 1) * (6 / d)).sum();
    assert_eq!(swapped, 36);
    assert_ne!(2 * (6 / 2 + 1), (2 + 1) * (6 / 2)); // 8 against 9
}

/// `Nat.dirichlet` really is the convolution, not the pointwise product.
#[test]
fn dirichlet_computes_the_convolution() {
    let mut f = Fixture::new();
    // `Σ_{d∣6} d · 1 = 12`.
    let id = f.identity();
    let one = f.one_fn();
    let term = f.dirichlet_at(id, one, 6);
    assert!(f.reduces_to(term, 12), "dirichlet id 1 at 6 must be 12");
    // `Σ_{d∣6} 1 · 1 = 4`.
    let one_a = f.one_fn();
    let one_b = f.one_fn();
    let term = f.dirichlet_at(one_a, one_b, 6);
    assert!(f.reduces_to(term, 4), "dirichlet 1 1 at 6 must be 4");
    // `Σ_{d∣6} d · (6/d + 1) = 36`, and NOT the pointwise 62.
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let term = f.dirichlet_at(id, succ_fn, 6);
    assert!(f.reduces_to(term, 36), "dirichlet id succ at 6 must be 36");
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let term = f.dirichlet_at(id, succ_fn, 6);
    assert!(
        !f.reduces_to(term, 62),
        "dirichlet must not be the pointwise product"
    );
}

/// `Nat.dirichlet_comm` at a discharged instance, at a pair whose summands
/// differ term by term.
#[test]
fn dirichlet_comm_holds_at_a_discharged_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let six = f.num(6);
    let pos = f.positivity(6);
    let instance = f.lemma(p.dirichlet_comm, &[id, succ_fn, six, pos]);
    let ty = f.k.infer(instance).expect("the instance must type-check");

    let id = f.identity();
    let succ_fn = f.succ_fn();
    let lhs = f.dirichlet_at(id, succ_fn, 6);
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let rhs = f.dirichlet_at(succ_fn, id, 6);
    let expected = f.eq(lhs, rhs);
    assert!(f.k.def_eq(ty, expected), "the instance must state the swap");

    // Both sides reduce to 36 — so the equation is between two computed
    // numbers, not between two stuck terms.
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let lhs = f.dirichlet_at(id, succ_fn, 6);
    assert!(f.reduces_to(lhs, 36), "the left side must be 36");
    let id = f.identity();
    let succ_fn = f.succ_fn();
    let rhs = f.dirichlet_at(succ_fn, id, 6);
    assert!(f.reduces_to(rhs, 36), "the right side must be 36");
}

/// `d = 1 ∗ 1` and `σ = id ∗ 1`, at numerals on both sides.
#[test]
fn the_two_classical_functions_are_convolutions() {
    let mut f = Fixture::new();
    let p = f.p;
    let six = f.num(6);
    let num_divisors = f.const_app(p.num_divisors, &[six]);
    assert!(f.reduces_to(num_divisors, 4));
    let six = f.num(6);
    let sigma = f.const_app(p.sum_divisors, &[six]);
    assert!(f.reduces_to(sigma, 12));

    let six = f.num(6);
    let instance = f.lemma(p.num_divisors_eq_dirichlet, &[six]);
    f.k.infer(instance).expect("d = 1 * 1 must type-check");
    let six = f.num(6);
    let instance = f.lemma(p.sum_divisors_eq_dirichlet, &[six]);
    f.k.infer(instance).expect("sigma = id * 1 must type-check");
}

// ---------------------------------------------------------------------------
// Multiplicativity.
// ---------------------------------------------------------------------------

/// `Nat.isMultiplicative_totient` at a FULLY DISCHARGED coprime pair:
/// `φ(6) = φ(2)·φ(3)`, i.e. `2 = 1·2`, with `gcd 2 3 = 1` closed by `Eq.refl`
/// because `Nat.gcd` computes at numerals.
#[test]
fn totient_is_a_member_of_the_family() {
    let mut f = Fixture::new();
    let p = f.p;
    let two = f.num(2);
    let three = f.num(3);
    let g = f.gcd(two, three);
    let coprime = f.refl(g);
    let two = f.num(2);
    let three = f.num(3);
    let law = f.kernel().const_(p.is_multiplicative_totient, vec![]);
    let instance = f.apply(law, &[two, three, coprime]);
    let ty =
        f.k.infer(instance)
            .expect("the totient instance must type-check");

    let two = f.num(2);
    let three = f.num(3);
    let product = f.mul(two, three);
    let lhs = f.const_app(p.totient, &[product]);
    let two = f.num(2);
    let three = f.num(3);
    let ta = f.const_app(p.totient, &[two]);
    let tb = f.const_app(p.totient, &[three]);
    let rhs = f.mul(ta, tb);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(ty, expected),
        "the instance must state phi(2*3) = phi 2 * phi 3"
    );
    // and both sides compute to 2, so the equation is not vacuous.
    let two = f.num(2);
    let three = f.num(3);
    let product = f.mul(two, three);
    let lhs = f.const_app(p.totient, &[product]);
    assert!(f.reduces_to(lhs, 2), "phi 6 must be 2");
}

// ---------------------------------------------------------------------------
// Möbius.
// ---------------------------------------------------------------------------

/// `μ` at the four values the brief names, read off the graded pair:
/// `μ(1) = +1`, `μ(2) = -1`, `μ(4) = 0`, `μ(6) = +1`. The parity-flipped
/// definition would swap the `n = 2` and `n = 6` rows, so these four
/// instances distinguish it.
#[test]
fn moebius_takes_its_classical_values() {
    let mut f = Fixture::new();
    for (n, pos, neg) in [
        (1_u32, 1_u32, 0_u32),
        (2, 0, 1),
        (3, 0, 1),
        (4, 0, 0),
        (5, 0, 1),
        (6, 1, 0),
    ] {
        let term = f.moebius_pos_at(n);
        assert!(f.reduces_to(term, pos), "moebiusPos {n} must be {pos}");
        let term = f.moebius_neg_at(n);
        assert!(f.reduces_to(term, neg), "moebiusNeg {n} must be {neg}");
        let term = f.moebius_abs_at(n);
        let abs = pos + neg;
        assert!(f.reduces_to(term, abs), "moebiusAbs {n} must be {abs}");
    }
    // The parity-flipped reading would put `moebiusPos 2 = 1`.
    let term = f.moebius_pos_at(2);
    assert!(
        !f.reduces_to(term, 1),
        "moebiusPos 2 must be 0, not the parity-flipped 1"
    );
    // The squarefree-ignoring reading would put `moebiusAbs 4 = 1`.
    let term = f.moebius_abs_at(4);
    assert!(
        !f.reduces_to(term, 1),
        "moebiusAbs 4 must be 0: 4 is not squarefree"
    );
}

/// The two structural laws of the graded pair, instantiated at a squarefree
/// even-`Ω`, a squarefree odd-`Ω` and a non-squarefree argument — the three
/// branches of both proofs.
#[test]
fn the_graded_pair_laws_hold_at_every_branch() {
    let mut f = Fixture::new();
    let p = f.p;
    for n_value in [6_u32, 2, 4] {
        let n = f.num(n_value);
        let instance = f.lemma(p.moebius_pos_add_neg, &[n]);
        let ty = f.k.infer(instance).expect("the sum law must type-check");
        let pos = f.moebius_pos_at(n_value);
        let neg = f.moebius_neg_at(n_value);
        let lhs = f.add(pos, neg);
        let rhs = f.moebius_abs_at(n_value);
        let expected = f.eq(lhs, rhs);
        assert!(f.k.def_eq(ty, expected), "the sum law at {n_value}");

        let n = f.num(n_value);
        let instance = f.lemma(p.moebius_pos_mul_neg, &[n]);
        let ty =
            f.k.infer(instance)
                .expect("the product law must type-check");
        let pos = f.moebius_pos_at(n_value);
        let neg = f.moebius_neg_at(n_value);
        let lhs = f.mul(pos, neg);
        let zero = f.zero();
        let expected = f.eq(lhs, zero);
        assert!(f.k.def_eq(ty, expected), "the product law at {n_value}");
    }
}

// ---------------------------------------------------------------------------
// Footprints and types.
// ---------------------------------------------------------------------------

/// Every declaration in the family layer rests on zero axioms.
#[test]
fn the_family_declarations_rest_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    for name in [
        p.sum_divisors_by_congr,
        p.is_multiplicative,
        p.is_multiplicative_totient,
        p.is_multiplicative_one,
        p.dirichlet,
        p.dirichlet_comm,
        p.num_divisors_eq_dirichlet,
        p.sum_divisors_eq_dirichlet,
        p.omega_count,
        p.moebius_abs,
        p.moebius_pos,
        p.moebius_neg,
        p.moebius_pos_add_neg,
        p.moebius_pos_mul_neg,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character.
#[test]
fn the_family_declarations_state_the_intended_types() {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let render = |k: &mut Kernel, name| match k
        .environment()
        .get(name)
        .expect("the declaration must exist")
    {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is neither a theorem nor a definition"),
    };

    let rendered: Vec<(String, String)> = [
        p.is_multiplicative,
        p.is_multiplicative_totient,
        p.dirichlet,
        p.dirichlet_comm,
        p.omega_count,
        p.moebius_pos,
        p.moebius_pos_add_neg,
        p.moebius_pos_mul_neg,
    ]
    .into_iter()
    .map(|name| (k.display_name(name).to_string(), render(&mut k, name)))
    .collect();

    let mut report = String::new();
    for (name, ty) in &rendered {
        report.push_str(name);
        report.push_str(" : ");
        report.push_str(ty);
        report.push('\n');
    }
    assert_eq!(report, EXPECTED_TYPES, "declared types drifted");
}

/// Pinned. Regenerate by reading the assertion failure.
const EXPECTED_TYPES: &str = concat!(
    "Nat.IsMultiplicative : ((x0 : ((x0 : AxNat) -> AxNat)) -> Prop)\n",
    "Nat.isMultiplicative_totient : AxNat.IsMultiplicative AxNat.totient\n",
    "Nat.dirichlet : ((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> AxNat)))\n",
    "Nat.dirichlet_comm : ((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : ((x1 : AxNat) -> AxNat)) -> ((x2 : AxNat) -> ((x3 : AxNat.lt AxNat.zero x2) -> Eq.{1} AxNat (AxNat.dirichlet x0 x1 x2) (AxNat.dirichlet x1 x0 x2)))))\n",
    "Nat.omegaCount : ((x0 : AxNat) -> AxNat)\n",
    "Nat.moebiusPos : ((x0 : AxNat) -> AxNat)\n",
    "Nat.moebius_pos_add_neg : ((x0 : AxNat) -> Eq.{1} AxNat (AxNat.add (AxNat.moebiusPos x0) (AxNat.moebiusNeg x0)) (AxNat.moebiusAbs x0))\n",
    "Nat.moebius_pos_mul_neg : ((x0 : AxNat) -> Eq.{1} AxNat (AxNat.mul (AxNat.moebiusPos x0) (AxNat.moebiusNeg x0)) AxNat.zero)\n",
);
