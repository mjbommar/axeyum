//! Tests for [`nat_prelude::eisenstein_lemma`](super::eisenstein_lemma).
//!
//! Four kinds of check:
//!
//! 1. **The arithmetic, recomputed in Rust first** — the floor sum `F`, the
//!    Gauss count `N`, the triangular sum `T`, the residue sum and the
//!    conditional fold sum `S` — so no expectation below is inherited from an
//!    ADR or from the kernel itself.
//! 2. **Concrete instantiation** of all four declarations with the
//!    coprimality hypothesis discharged by `Eq.refl` (so `Nat.gcd` really
//!    reduces), each aggregate evaluated to a numeral, and each numeral shown
//!    to reject its neighbour.
//! 3. **Coprimality shown load-bearing**, at `pp = 9`, `q = 3` (`gcd 3 9 = 3`):
//!    there `F + N = 3`, and `3` is refuted as `k + k` inside the kernel by
//!    exhausting every `k` that could reach it. So the conclusion is FALSE at
//!    an instance every other hypothesis of the theorem reaches — there are
//!    none.
//! 4. **The four declared types, pinned character for character**, and the
//!    axiom footprints.
//!
//! Numerals are kept small deliberately: every `Nat` numeral in this kernel
//! is unary, and the cost of evaluating `Nat.div` inside a `sumRange` is
//! superlinear in the largest magnitude FORMED. The largest product any
//! instance below forms is `15`.

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

// --- the reference, recomputed here -----------------------------------------

fn residue(pp: u32, a: u32, k: u32) -> u32 {
    (a * k) % pp
}

fn sign_neg(pp: u32, a: u32, k: u32) -> bool {
    // `gaussSignNeg pp a k := ble (succ (div pp 2)) (leastResidue pp a k)`,
    // i.e. the residue STRICTLY exceeds `pp / 2`.
    pp / 2 < residue(pp, a, k)
}

fn fold(pp: u32, a: u32, k: u32) -> u32 {
    let r = residue(pp, a, k);
    if sign_neg(pp, a, k) { pp - r } else { r }
}

/// `F := Σ_{k=1..m} ⌊a·k / pp⌋`.
fn floor_sum(pp: u32, a: u32, m: u32) -> u32 {
    (1..=m).map(|k| (a * k) / pp).sum()
}

/// `N := gaussNegCount pp a m`.
fn neg_count(pp: u32, a: u32, m: u32) -> u32 {
    u32::try_from((1..=m).filter(|&k| sign_neg(pp, a, k)).count()).expect("the count fits")
}

/// `T := Σ_{k=1..m} k`.
fn triangular(m: u32) -> u32 {
    (1..=m).sum()
}

/// `Σ_{k=1..m} leastResidue pp a k`.
fn residue_sum(pp: u32, a: u32, m: u32) -> u32 {
    (1..=m).map(|k| residue(pp, a, k)).sum()
}

/// `S := Σ_{k=1..m, sign k} gaussFold pp a k`.
fn negative_fold_sum(pp: u32, a: u32, m: u32) -> u32 {
    (1..=m)
        .filter(|&k| sign_neg(pp, a, k))
        .map(|k| fold(pp, a, k))
        .sum()
}

/// `(m, n)` pairs with `pp = 2m+1`, `q = 2n+1`, all coprime.
const COPRIME: [(u32, u32); 3] = [
    // `pp = 7`, `q = 3`.
    (3, 1),
    // `pp = 5`, `q = 3`.
    (2, 1),
    // `pp = 7`, `q = 5`.
    (3, 2),
];

/// `pp = 9`, `q = 3`: `gcd 3 9 = 3`, and `F + N` is ODD there.
const NOT_COPRIME: (u32, u32) = (4, 1);

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `fun j => succ j`.
    fn succ_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let body = self.succ(j);
        self.lam_fv(j_fv, nat, body)
    }

    /// `fun j => div (mul a (succ j)) (succ ap)`.
    fn floor_fn(&mut self, ap: u32, a: u32) -> ExprId {
        let nat = self.nat_ty();
        let ap_e = self.num(ap);
        let pp = self.succ(ap_e);
        let a_e = self.num(a);
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let sj = self.succ(j);
        let prod = self.mul(a_e, sj);
        let body = self.div(prod, pp);
        self.lam_fv(j_fv, nat, body)
    }

    /// `fun j => leastResidue (succ ap) a (succ j)`.
    fn residue_fn(&mut self, ap: u32, a: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let ap_e = self.num(ap);
        let pp = self.succ(ap_e);
        let a_e = self.num(a);
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let sj = self.succ(j);
        let body = self.const_app(p.least_residue, &[pp, a_e, sj]);
        self.lam_fv(j_fv, nat, body)
    }

    /// `F` as a kernel term, at `pp = succ (2*m)`, `q = succ (2*n)`.
    fn f_sum(&mut self, m: u32, n: u32) -> ExprId {
        let f = self.floor_fn(2 * m, 2 * n + 1);
        let m_e = self.num(m);
        self.sum_range(f, m_e)
    }

    /// `N` as a kernel term.
    fn n_count(&mut self, m: u32, n: u32) -> ExprId {
        let p = self.p;
        let pp = self.num(2 * m + 1);
        let q = self.num(2 * n + 1);
        let m_e = self.num(m);
        self.const_app(p.gauss_neg_count, &[pp, q, m_e])
    }

    /// `gcd (succ (2*n)) (succ (2*m)) = 1`, by `Eq.refl` — which only
    /// type-checks if `Nat.gcd` genuinely reduces at the pair.
    fn coprimality(&mut self) -> ExprId {
        let one = self.num(1);
        self.refl(one)
    }

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }
}

/// The reference itself: `F + N` is even at every coprime instance and ODD at
/// the non-coprime one. Checked in Rust before anything is asked of the
/// kernel, so the controls below cannot be vacuous.
#[test]
fn the_parity_the_lemma_asserts_holds_and_fails_where_it_should() {
    for (m, n) in COPRIME {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        let total = floor_sum(pp, q, m) + neg_count(pp, q, m);
        assert_eq!(total % 2, 0, "F + N must be even at pp = {pp}, q = {q}");
        assert!(total > 0, "and non-trivially so");
    }

    let (m, n) = NOT_COPRIME;
    let (pp, q) = (2 * m + 1, 2 * n + 1);
    assert_eq!((pp, q), (9, 3));
    assert_ne!(gcd(q, pp), 1, "this instance must NOT be coprime");
    assert_eq!(floor_sum(pp, q, m), 2);
    assert_eq!(neg_count(pp, q, m), 1);
    assert_eq!(
        (floor_sum(pp, q, m) + neg_count(pp, q, m)) % 2,
        1,
        "F + N is ODD at pp = 9, q = 3, so the conclusion is FALSE there"
    );
}

fn gcd(a: u32, b: u32) -> u32 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// The pinned numbers this file asserts, all recomputed rather than quoted.
#[test]
fn the_reference_values_are_what_the_tests_use() {
    // `pp = 7`, `q = 3`, `m = 3`.
    assert_eq!(triangular(3), 6);
    assert_eq!(residue_sum(7, 3, 3), 11);
    assert_eq!(floor_sum(7, 3, 3), 1);
    assert_eq!(neg_count(7, 3, 3), 1);
    assert_eq!(negative_fold_sum(7, 3, 3), 1);
    // Step 1 at this instance: `a·T = pp·F + ΣL`, i.e. `18 = 7 + 11`.
    assert_eq!(
        3 * triangular(3),
        7 * floor_sum(7, 3, 3) + residue_sum(7, 3, 3)
    );
    // Step 2: `a·T + (S+S) = pp·(F+N) + T`, i.e. `20 = 14 + 6`.
    assert_eq!(
        3 * triangular(3) + 2 * negative_fold_sum(7, 3, 3),
        7 * (floor_sum(7, 3, 3) + neg_count(7, 3, 3)) + triangular(3)
    );
}

/// **Step 1**, the summed division algorithm, instantiated and evaluated.
#[test]
fn the_summed_division_algorithm_applies_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;
    let (ap, a, m) = (6u32, 3u32, 3u32);
    let pp = ap + 1;

    let ap_e = f.num(ap);
    let a_e = f.num(a);
    let m_e = f.num(m);
    let instance = f.lemma(p.mul_sum_range_div_add_least_residue, &[ap_e, a_e, m_e]);
    let inferred = f.k.infer(instance).expect("the instance must type-check");

    let succ_f = f.succ_fn();
    let m_e2 = f.num(m);
    let t = f.sum_range(succ_f, m_e2);
    let a_e2 = f.num(a);
    let lhs = f.mul(a_e2, t);

    let floor_f = f.floor_fn(ap, a);
    let m_e3 = f.num(m);
    let f_sum = f.sum_range(floor_f, m_e3);
    let pp_e = {
        let ap2 = f.num(ap);
        f.succ(ap2)
    };
    let scaled = f.mul(pp_e, f_sum);
    let resid_f = f.residue_fn(ap, a);
    let m_e4 = f.num(m);
    let l_sum = f.sum_range(resid_f, m_e4);
    let rhs = f.add(scaled, l_sum);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "step 1's conclusion is not the summed division algorithm"
    );

    assert!(f.reduces_to(t, triangular(m)), "T = 6");
    assert!(f.reduces_to(f_sum, floor_sum(pp, a, m)), "F = 1");
    assert!(f.reduces_to(l_sum, residue_sum(pp, a, m)), "ΣL = 11");
    assert!(f.reduces_to(lhs, 18), "a·T = 18");
    assert!(f.reduces_to(rhs, 18), "pp·F + ΣL = 18");
    assert!(!f.reduces_to(rhs, 19), "and not 19");
}

/// **Step 2**, the counting identity, instantiated and evaluated.
#[test]
fn the_counting_identity_applies_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;
    let (m, a) = (3u32, 3u32);
    let pp = 2 * m + 1;

    let m_e = f.num(m);
    let a_e = f.num(a);
    let cop = f.coprimality();
    let instance = f.lemma(p.eisenstein_count_identity, &[m_e, a_e, cop]);
    let inferred = f.k.infer(instance).expect("the instance must type-check");

    let succ_f = f.succ_fn();
    let m_e2 = f.num(m);
    let t = f.sum_range(succ_f, m_e2);
    let a_e2 = f.num(a);
    let left_product = f.mul(a_e2, t);
    // `S` is exactly the reconciliation's conditional fold sum.
    let s_sum = {
        let nat = f.nat_ty();
        let pp_e = f.num(pp);
        let a_e3 = f.num(a);
        let sign = {
            let j_fv = f.fresh_fvar();
            let j = f.k.fvar(j_fv);
            let sj = f.succ(j);
            let body = f.const_app(p.gauss_sign_neg, &[pp_e, a_e3, sj]);
            f.lam_fv(j_fv, nat, body)
        };
        let fold_fn = {
            let j_fv = f.fresh_fvar();
            let j = f.k.fvar(j_fv);
            let sj = f.succ(j);
            let body = f.const_app(p.gauss_fold, &[pp_e, a_e3, sj]);
            f.lam_fv(j_fv, nat, body)
        };
        let m_e3 = f.num(m);
        f.const_app(p.sum_range_if, &[sign, fold_fn, m_e3])
    };
    let doubled = f.add(s_sum, s_sum);
    let lhs = f.add(left_product, doubled);

    let floor_f = f.floor_fn(2 * m, a);
    let m_e4 = f.num(m);
    let f_sum = f.sum_range(floor_f, m_e4);
    let pp_e2 = f.num(pp);
    let a_e4 = f.num(a);
    let m_e5 = f.num(m);
    let n_count = f.const_app(p.gauss_neg_count, &[pp_e2, a_e4, m_e5]);
    let combined = f.add(f_sum, n_count);
    let scaled = f.mul(pp_e2, combined);
    let rhs = f.add(scaled, t);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(inferred, expected),
        "the counting identity's conclusion is not what this test builds"
    );

    assert!(f.reduces_to(s_sum, negative_fold_sum(pp, a, m)), "S = 1");
    assert!(f.reduces_to(n_count, neg_count(pp, a, m)), "N = 1");
    assert!(f.reduces_to(lhs, 20), "a·T + 2S = 20");
    assert!(f.reduces_to(rhs, 20), "pp·(F+N) + T = 20");
    assert!(!f.reduces_to(rhs, 21), "and not 21");
}

/// **Eisenstein's lemma**, instantiated at three coprime pairs of odd
/// moduli, with the coprimality proof by `Eq.refl` and `F + N` evaluated.
#[test]
fn eisensteins_lemma_applies_at_coprime_odd_pairs() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in COPRIME {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        let want = floor_sum(pp, q, m) + neg_count(pp, q, m);

        let m_e = f.num(m);
        let n_e = f.num(n);
        let cop = f.coprimality();
        let instance = f.lemma(p.eisenstein_lemma, &[m_e, n_e, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the coprime instance must type-check");

        let f_sum = f.f_sum(m, n);
        let n_count = f.n_count(m, n);
        let total = f.add(f_sum, n_count);
        let expected = f.const_app(p.even, &[total]);
        assert!(
            f.k.def_eq(inferred, expected),
            "at pp = {pp}, q = {q} the conclusion is not `Even (F + N)`"
        );

        // The aggregates are not stuck.
        assert!(f.reduces_to(f_sum, floor_sum(pp, q, m)));
        assert!(f.reduces_to(n_count, neg_count(pp, q, m)));
        assert!(f.reduces_to(total, want), "F + N must be {want}");
        assert!(!f.reduces_to(total, want + 1));
    }
}

/// **Coprimality is load-bearing.** At `pp = 9`, `q = 3` every other
/// hypothesis of the theorem holds (there are none), `F + N` reduces to `3`,
/// and `3` is refuted as `k + k` by exhausting every `k` that could reach it:
/// `k ≤ 3` is checked directly and `k ≥ 4` gives `k + k ≥ 8 > 3`.
#[test]
fn dropping_coprimality_gives_an_odd_sum() {
    let mut f = Fixture::new();
    let (m, n) = NOT_COPRIME;
    let (pp, q) = (2 * m + 1, 2 * n + 1);
    assert_eq!(floor_sum(pp, q, m) + neg_count(pp, q, m), 3);

    let f_sum = f.f_sum(m, n);
    let n_count = f.n_count(m, n);
    let total = f.add(f_sum, n_count);
    assert!(f.reduces_to(f_sum, 2), "F = 2 at pp = 9, q = 3");
    assert!(f.reduces_to(n_count, 1), "N = 1 there");
    assert!(f.reduces_to(total, 3), "so F + N = 3");

    for k in 0u32..=3 {
        let k_e = f.num(k);
        let doubled = f.add(k_e, k_e);
        assert!(
            !f.k.def_eq(total, doubled),
            "3 is not {k} + {k}, so `Even (F + N)` is FALSE here"
        );
    }
    // Positive control on that loop: the SAME query succeeds at `2 = 1 + 1`,
    // so the negatives above are not an artefact of a broken comparison.
    let two = f.num(2);
    let one_a = f.num(1);
    let one_b = f.num(1);
    let one_plus_one = f.add(one_a, one_b);
    assert!(f.k.def_eq(two, one_plus_one), "positive control: 2 = 1 + 1");
}

/// The congruence form, instantiated: `modEq 2 F N` at the same three pairs.
#[test]
fn the_congruence_form_applies_at_the_same_pairs() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in COPRIME {
        let m_e = f.num(m);
        let n_e = f.num(n);
        let cop = f.coprimality();
        let instance = f.lemma(p.eisenstein_lemma_mod_eq, &[m_e, n_e, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the congruence instance must type-check");

        let f_sum = f.f_sum(m, n);
        let n_count = f.n_count(m, n);
        let two = f.num(2);
        let expected = f.mod_eq(two, f_sum, n_count);
        assert!(
            f.k.def_eq(inferred, expected),
            "the congruence's conclusion is not `modEq 2 F N`"
        );
    }
}

/// All four declarations rest on zero axioms.
#[test]
fn the_eisenstein_family_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    for name in [
        p.mul_sum_range_div_add_least_residue,
        p.eisenstein_count_identity,
        p.eisenstein_lemma,
        p.eisenstein_lemma_mod_eq,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The four declared types, pinned character for character.
///
/// What the numeric instances cannot see, and these pins are the only guard
/// for: that the modulus is `succ (2*m)` and the multiplier `succ (2*n)` in
/// EVERY occurrence (an instance at one pair cannot distinguish `2*m` from
/// `m*2`, or `succ (2*m)` from a bare `pp` free variable), that step 1 is
/// stated at a general `succ ap` rather than at `succ (2*m)`, and that the
/// counting identity's `a` is unconstrained while the lemma's is forced odd.
#[test]
fn the_eisenstein_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let render = |k: &mut Kernel, name| match k
        .environment()
        .get(name)
        .expect("the theorem must be declared")
    {
        Declaration::Theorem { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is not a theorem"),
    };

    assert_eq!(
        render(&mut k, p.mul_sum_range_div_add_least_residue),
        EXPECTED_STEP_ONE
    );
    assert_eq!(
        render(&mut k, p.eisenstein_count_identity),
        EXPECTED_IDENTITY
    );
    assert_eq!(render(&mut k, p.eisenstein_lemma), EXPECTED_LEMMA);
    assert_eq!(
        render(&mut k, p.eisenstein_lemma_mod_eq),
        EXPECTED_LEMMA_MOD_EQ
    );

    // Step 1 is stated at a GENERAL `succ ap`, not at `succ (2*m)`: it is the
    // division algorithm, and nothing about it is Eisenstein-specific.
    assert!(
        !EXPECTED_STEP_ONE.contains("AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero))"),
        "step 1 must not mention `2 * _`"
    );
    // Negative control on that query: the lemma DOES mention `2 * _`.
    assert!(
        EXPECTED_LEMMA.contains("AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero))"),
        "positive control: the lemma's moduli are `succ (2*_)`"
    );
}

const EXPECTED_STEP_ONE: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.mul x1 (AxNat.sumRange (fun (x3 : AxNat) => AxNat.succ x3) x2)) (AxNat.add (AxNat.mul (AxNat.succ x0) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul x1 (AxNat.succ x3)) (AxNat.succ x0)) x2)) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.leastResidue (AxNat.succ x0) x1 (AxNat.succ x3)) x2)))))";
const EXPECTED_IDENTITY: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd x1 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> Eq.{1} AxNat (AxNat.add (AxNat.mul x1 (AxNat.sumRange (fun (x3 : AxNat) => AxNat.succ x3) x0)) (AxNat.add (AxNat.sumRangeIf (fun (x3 : AxNat) => AxNat.gaussSignNeg (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 (AxNat.succ x3)) (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 (AxNat.succ x3)) x0) (AxNat.sumRangeIf (fun (x3 : AxNat) => AxNat.gaussSignNeg (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 (AxNat.succ x3)) (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 (AxNat.succ x3)) x0))) (AxNat.add (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul x1 (AxNat.succ x3)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) x0) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 x0))) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.succ x3) x0)))))";
const EXPECTED_LEMMA: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> AxNat.Even (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ x3)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) x0) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) x0)))))";
const EXPECTED_LEMMA_MOD_EQ: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> AxNat.modEq (AxNat.succ (AxNat.succ AxNat.zero)) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ x3)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) x0) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) x0))))";
