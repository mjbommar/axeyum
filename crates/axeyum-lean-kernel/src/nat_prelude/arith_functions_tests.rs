//! Tests for [`nat_prelude::arith_functions`](super::arith_functions).
//!
//! The trusted gate cannot tell you a `Definition` is wrong, and every wrong
//! variant here type-checks: `Nat.sumDivisorsBy` would be just as well typed
//! with the bound `n` instead of `succ n` (dropping `n` itself from its own
//! divisors), and `Nat.divisorFlip` would be just as well typed as the naive
//! `fun n k => n / k` — which is precisely the map that is NOT injective and
//! whose use would make the reindexing false. So the order is:
//!
//! 1. **Evaluation at numerals**, each against a Rust reference, with the
//!    wrong-but-well-typed readings shown to give DIFFERENT numbers.
//! 2. The involution and the reindexing at FULLY DISCHARGED instances — no
//!    local context, no assumed hypothesis: the positivity comes from
//!    `zero_lt_succ` and the divisibility from `Nat.dvd_mul` at literals, so
//!    the kernel really does reduce both sides.
//! 3. Footprints and the declared types, pinned character for character.
//!
//! Magnitudes stay at or below `12`: every `Nat` numeral in this kernel is
//! unary, so `sumDivisorsBy` at `n` unrolls a `succ n`-step fold whose every
//! step runs a `Nat.mod`.

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

    fn is_true(&mut self, term: ExprId) -> bool {
        let t = self.bool_true();
        self.k.def_eq(term, t)
    }

    fn is_false(&mut self, term: ExprId) -> bool {
        let t = self.bool_false();
        self.k.def_eq(term, t)
    }

    /// `Nat.dvdB a n` at numerals.
    fn dvd_b_at(&mut self, a: u32, n: u32) -> ExprId {
        let p = self.p;
        let a = self.num(a);
        let n = self.num(n);
        self.const_app(p.dvd_b, &[a, n])
    }

    /// `Nat.divisorFlip n k` at numerals.
    fn flip_at(&mut self, n: u32, k: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        let k = self.num(k);
        self.const_app(p.divisor_flip, &[n, k])
    }

    /// The identity summand `fun k => k`.
    fn identity(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        self.lam_fv(k_fv, nat, k)
    }

    /// The summand `fun k => succ k`, which is NOT invariant under
    /// `k ↦ n / k` pointwise — the reindexing is a statement about the whole
    /// sum, not about the summand.
    fn succ_summand(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let k_fv = self.fresh_fvar();
        let k = self.k.fvar(k_fv);
        let body = self.succ(k);
        self.lam_fv(k_fv, nat, body)
    }

    /// `Nat.sumDivisorsBy f n` at a numeral `n`.
    fn sum_divisors_by_at(&mut self, f: ExprId, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.sum_divisors_by, &[f, n])
    }

    /// `Nat.numDivisors n` at a numeral.
    fn num_divisors_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let n = self.num(n);
        self.const_app(p.num_divisors, &[n])
    }

    /// `Lt zero n` for a literal `n = succ m`, discharged by `zero_lt_succ`.
    fn positivity(&mut self, n: u32) -> ExprId {
        assert!(n >= 1, "positivity is only available at a successor");
        let pred = self.num(n - 1);
        self.zero_lt_succ(pred)
    }

    /// `dvd a (a * q)` at literals, whose type is definitionally
    /// `dvd a (a*q)` — used where a numeral divisibility proof is needed.
    fn dvd_literal(&mut self, a: u32, q: u32) -> ExprId {
        let p = self.p;
        let a = self.num(a);
        let q = self.num(q);
        self.lemma(p.dvd_mul, &[a, q])
    }
}

// ---------------------------------------------------------------------------
// 1. Evaluation.
// ---------------------------------------------------------------------------

/// The Rust reference readings really are different numbers, so the `def_eq`
/// controls below are not vacuous.
#[test]
fn the_reference_readings_are_distinct() {
    // Divisors of 6 counted the intended way (`d ∈ [0,6]`, `d ∣ 6`, and
    // `0 ∤ 6`): {1,2,3,6} -> 4 of them, summing to 12.
    let divisors = |n: u32| -> Vec<u32> { (1..=n).filter(|d| n % d == 0).collect() };
    assert_eq!(divisors(6), vec![1, 2, 3, 6]);
    assert_eq!(divisors(6).len(), 4);
    assert_eq!(divisors(6).iter().sum::<u32>(), 12);
    // The PROPER-divisor reading (bound `n` instead of `succ n`) drops `6`:
    // 3 divisors summing to 6. Both differ from the intended reading.
    let proper: Vec<u32> = divisors(6).into_iter().filter(|&d| d != 6).collect();
    assert_eq!(proper.len(), 3);
    assert_eq!(proper.iter().sum::<u32>(), 6);
    // And the reading that treats `0` as a divisor of `6` would count 5.
    assert_eq!(divisors(6).len() + 1, 5);
}

/// `Nat.dvdB` decides divisibility, INCLUDING the two degenerate arguments:
/// `dvdB 0 n` is `beq n 0`, so `0` divides `0` and nothing else.
#[test]
fn dvd_b_decides_divisibility_including_the_zero_divisor() {
    let mut f = Fixture::new();
    for (a, n) in [(1_u32, 6_u32), (2, 6), (3, 6), (6, 6), (1, 1), (0, 0)] {
        let term = f.dvd_b_at(a, n);
        assert!(f.is_true(term), "dvdB {a} {n} must be true");
    }
    for (a, n) in [(4_u32, 6_u32), (5, 6), (0, 6), (0, 1), (5, 12)] {
        let term = f.dvd_b_at(a, n);
        assert!(f.is_false(term), "dvdB {a} {n} must be false");
    }
}

/// `Nat.numDivisors` counts the divisors of `n` INCLUDING `n` itself and
/// EXCLUDING `0` — the two conventions the type cannot see.
#[test]
fn num_divisors_computes_on_small_numerals() {
    let mut f = Fixture::new();
    for (n, expected) in [(1_u32, 1_u32), (2, 2), (3, 2), (4, 3), (6, 4), (12, 6)] {
        let term = f.num_divisors_at(n);
        assert!(
            f.reduces_to(term, expected),
            "numDivisors {n} must be {expected}"
        );
    }
    // The proper-divisor reading would give 3 at `n = 6`, and the reading
    // that counts `0` would give 5. Neither is what the definition computes.
    let term = f.num_divisors_at(6);
    assert!(
        !f.reduces_to(term, 3),
        "numDivisors 6 is not the proper count"
    );
    let term = f.num_divisors_at(6);
    assert!(!f.reduces_to(term, 5), "numDivisors 6 must not count 0");
}

/// `Nat.sumDivisorsBy` at the identity summand IS `σ`, and at `succ` it adds
/// one per divisor — the summand really is applied, not ignored.
#[test]
fn sum_divisors_by_applies_its_summand() {
    let mut f = Fixture::new();
    for (n, expected) in [(1_u32, 1_u32), (2, 3), (4, 7), (6, 12)] {
        let identity = f.identity();
        let term = f.sum_divisors_by_at(identity, n);
        assert!(
            f.reduces_to(term, expected),
            "sumDivisorsBy id {n} must be {expected}"
        );
    }
    // `Σ_{d∣6} (d+1) = 12 + 4 = 16`: the summand is applied per divisor.
    let succ_summand = f.succ_summand();
    let term = f.sum_divisors_by_at(succ_summand, 6);
    assert!(f.reduces_to(term, 16), "sumDivisorsBy succ 6 must be 16");
    // A summand-ignoring definition would give 12 here.
    let succ_summand = f.succ_summand();
    let term = f.sum_divisors_by_at(succ_summand, 6);
    assert!(
        !f.reduces_to(term, 12),
        "sumDivisorsBy must not ignore its summand"
    );
}

/// `Nat.divisorFlip` is the classical `d ↦ n/d` ON THE DIVISORS and the
/// IDENTITY elsewhere. The second half is the whole point: the naive
/// `fun n k => n / k` sends `4`, `5` and `6` all to `1` at `n = 6` and is
/// therefore not injective.
#[test]
fn divisor_flip_moves_divisors_and_fixes_everything_else() {
    let mut f = Fixture::new();
    for (n, k, expected) in [
        (6_u32, 1_u32, 6_u32),
        (6, 2, 3),
        (6, 3, 2),
        (6, 6, 1),
        // Non-divisors, fixed:
        (6, 0, 0),
        (6, 4, 4),
        (6, 5, 5),
        (12, 4, 3),
        (12, 5, 5),
    ] {
        let term = f.flip_at(n, k);
        assert!(
            f.reduces_to(term, expected),
            "divisorFlip {n} {k} must be {expected}"
        );
    }
    // The naive `n / k` reading would send 4, 5 and 6 all to 1 at `n = 6`.
    for k in [4_u32, 5] {
        let term = f.flip_at(6, k);
        assert!(
            !f.reduces_to(term, 1),
            "divisorFlip 6 {k} must not be the naive quotient"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. The theorems, at fully discharged instances.
// ---------------------------------------------------------------------------

/// `Nat.sumDivisorsBy_eq_sumDivisors` at a numeral, with the control that
/// the shared value is the nonzero `12` rather than two zeros agreeing.
#[test]
fn the_new_aggregate_agrees_with_the_existing_sigma() {
    let mut f = Fixture::new();
    let p = f.p;
    let six = f.num(6);
    let sigma = f.const_app(p.sum_divisors, &[six]);
    assert!(f.reduces_to(sigma, 12), "sumDivisors 6 must be 12");
    let identity = f.identity();
    let aggregate = f.sum_divisors_by_at(identity, 6);
    assert!(f.reduces_to(aggregate, 12), "sumDivisorsBy id 6 must be 12");
    // And the theorem itself, instantiated.
    let six = f.num(6);
    let instance = f.lemma(p.sum_divisors_by_eq_sum_divisors, &[six]);
    let ty = f.k.infer(instance).expect("the instance must type-check");
    let identity = f.identity();
    let lhs = f.sum_divisors_by_at(identity, 6);
    let six = f.num(6);
    let rhs = f.const_app(p.sum_divisors, &[six]);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(ty, expected),
        "the instance must state the equation"
    );
}

/// `Nat.div_div_self_of_dvd` at a FULLY DISCHARGED instance: `6 / (6 / 2) = 2`
/// with the positivity from `zero_lt_succ` and the divisibility from
/// `Nat.dvd_mul 2 3`, whose subject `2 * 3` is definitionally `6`.
#[test]
fn div_div_self_holds_at_a_discharged_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    let six = f.num(6);
    let two = f.num(2);
    let pos = f.positivity(6);
    let dvd = f.dvd_literal(2, 3);
    let instance = f.lemma(p.div_div_self_of_dvd, &[six, two, pos, dvd]);
    let ty = f.k.infer(instance).expect("the instance must type-check");
    let six = f.num(6);
    let two = f.num(2);
    let inner = f.div(six, two);
    let six = f.num(6);
    let outer = f.div(six, inner);
    let two = f.num(2);
    let expected = f.eq(outer, two);
    assert!(
        f.k.def_eq(ty, expected),
        "the instance must state 6/(6/2) = 2"
    );
    // The control that the statement is not vacuous: `6 / (6 / 2)` really
    // does reduce, and to `2` rather than to `6 / 2 = 3`.
    let six = f.num(6);
    let two = f.num(2);
    let inner = f.div(six, two);
    let six = f.num(6);
    let outer = f.div(six, inner);
    assert!(f.reduces_to(outer, 2), "6/(6/2) must reduce to 2");
    let six = f.num(6);
    let two = f.num(2);
    let inner = f.div(six, two);
    let six = f.num(6);
    let outer = f.div(six, inner);
    assert!(!f.reduces_to(outer, 3), "6/(6/2) must not be 3");
}

/// The involution, at every point of `[0,6]` — divisors and non-divisors
/// alike — with the positivity discharged.
#[test]
fn divisor_flip_is_an_involution_at_a_discharged_instance() {
    let mut f = Fixture::new();
    let p = f.p;
    for k_value in 0_u32..=6 {
        let six = f.num(6);
        let pos = f.positivity(6);
        let law = f.lemma(p.divisor_flip_involutive, &[six, pos]);
        let k = f.num(k_value);
        let instance = f.apply(law, &[k]);
        let ty = f.k.infer(instance).expect("the instance must type-check");
        let inner = f.flip_at(6, k_value);
        let six = f.num(6);
        let outer = f.const_app(p.divisor_flip, &[six, inner]);
        let k = f.num(k_value);
        let expected = f.eq(outer, k);
        assert!(
            f.k.def_eq(ty, expected),
            "the involution must state flip(flip {k_value}) = {k_value}"
        );
        // and it really reduces, so the equation is not vacuously about two
        // stuck terms.
        assert!(
            f.reduces_to(outer, k_value),
            "flip(flip {k_value}) must reduce to {k_value}"
        );
    }
}

/// **The deliverable**: `Nat.sumDivisorsBy_reindex` at a discharged instance,
/// with both sides reduced.
///
/// The reindexed summand is NOT the original summand — at `n = 6`, `k = 2`
/// the identity gives `2` where `fun k => 6 / k` gives `3` — so the equation
/// is a statement about the whole sum, and the control below pins that the
/// two summands really do differ pointwise.
#[test]
fn the_reindexing_holds_at_a_discharged_instance() {
    let mut f = Fixture::new();
    let p = f.p;

    let identity = f.identity();
    let six = f.num(6);
    let pos = f.positivity(6);
    let instance = f.lemma(p.sum_divisors_by_reindex, &[identity, six, pos]);
    let ty = f.k.infer(instance).expect("the instance must type-check");

    // Both sides reduce to 12.
    let identity = f.identity();
    let lhs = f.sum_divisors_by_at(identity, 6);
    assert!(f.reduces_to(lhs, 12), "the left side must be 12");

    let nat = f.nat_ty();
    let reindexed = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let six = f.num(6);
        let body = f.div(six, k);
        f.lam_fv(k_fv, nat, body)
    };
    let rhs = f.sum_divisors_by_at(reindexed, 6);
    assert!(f.reduces_to(rhs, 12), "the right side must be 12");

    // The instance states exactly that equation.
    let identity = f.identity();
    let lhs = f.sum_divisors_by_at(identity, 6);
    let reindexed = {
        let k_fv = f.fresh_fvar();
        let k = f.k.fvar(k_fv);
        let six = f.num(6);
        let body = f.div(six, k);
        f.lam_fv(k_fv, nat, body)
    };
    let rhs = f.sum_divisors_by_at(reindexed, 6);
    let expected = f.eq(lhs, rhs);
    assert!(
        f.k.def_eq(ty, expected),
        "the instance must state the reindexed equation"
    );

    // The control: the two summands differ pointwise at `k = 2`.
    let two = f.num(2);
    let six = f.num(6);
    let quotient = f.div(six, two);
    assert!(f.reduces_to(quotient, 3), "6/2 must be 3, not 2");

    // A second control at a summand that is not the identity: `Σ (d+1)` and
    // `Σ (6/d + 1)` are both 16, and the reindexing states their equality.
    let succ_summand = f.succ_summand();
    let six = f.num(6);
    let pos = f.positivity(6);
    let instance = f.lemma(p.sum_divisors_by_reindex, &[succ_summand, six, pos]);
    f.k.infer(instance)
        .expect("the second instance must type-check");
    let succ_summand = f.succ_summand();
    let lhs = f.sum_divisors_by_at(succ_summand, 6);
    assert!(f.reduces_to(lhs, 16), "Σ_{{d∣6}} (d+1) must be 16");
}

/// `mapsInto` at `succ n` is not vacuous: the flip really does land inside
/// `[0, n]` at every point of `[0, n]`, including the non-divisors the naive
/// quotient would collapse onto `1`.
#[test]
fn divisor_flip_stays_in_range() {
    let mut f = Fixture::new();
    // The image of `[0,6]` under `divisorFlip 6`, point by point.
    for (k, image) in [
        (0_u32, 0_u32),
        (1, 6),
        (2, 3),
        (3, 2),
        (4, 4),
        (5, 5),
        (6, 1),
    ] {
        assert!(image <= 6, "the reference image must be in range");
        let term = f.flip_at(6, k);
        assert!(
            f.reduces_to(term, image),
            "divisorFlip 6 {k} must be {image}, which is in [0,6]"
        );
    }
}

// ---------------------------------------------------------------------------
// 3. Footprints and types.
// ---------------------------------------------------------------------------

/// Every declaration here rests on zero axioms.
#[test]
fn the_arith_function_declarations_rest_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    for name in [
        p.dvd_b,
        p.dvd_of_dvd_b,
        p.dvd_b_of_dvd,
        p.sum_divisors_by,
        p.num_divisors,
        p.sum_divisors_by_eq_sum_divisors,
        p.div_div_self_of_dvd,
        p.divisor_flip,
        p.divisor_flip_at_divisor,
        p.divisor_flip_at_non_divisor,
        p.divisor_flip_dvd_b,
        p.divisor_flip_involutive,
        p.divisor_flip_injective_on,
        p.divisor_flip_maps_into,
        p.sum_divisors_by_reindex,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character. Three distinctions no
/// numeric instance can see:
///
/// - `divisorFlip_injectiveOn` quantifies over an ARBITRARY range `x1`, not
///   over `succ x0` — an involution needs no bound;
/// - `divisorFlip_mapsInto`'s range IS `succ x0`;
/// - `sumDivisorsBy_reindex`'s summand binder is `AxNat → AxNat`, so the
///   theorem is about an arbitrary arithmetic function rather than about
///   `σ`.
#[test]
fn the_arith_function_declarations_state_the_intended_types() {
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
        p.dvd_b,
        p.sum_divisors_by,
        p.num_divisors,
        p.div_div_self_of_dvd,
        p.divisor_flip,
        p.divisor_flip_involutive,
        p.divisor_flip_injective_on,
        p.divisor_flip_maps_into,
        p.sum_divisors_by_reindex,
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

/// The nine pinned types. Regenerate by reading the assertion failure.
const EXPECTED_TYPES: &str = concat!(
    "Nat.dvdB : ((x0 : AxNat) -> ((x1 : AxNat) -> Bool))\n",
    "Nat.sumDivisorsBy : ((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : AxNat) -> AxNat))\n",
    "Nat.numDivisors : ((x0 : AxNat) -> AxNat)\n",
    "Nat.div_div_self_of_dvd : ((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat.lt AxNat.zero x0) -> ((x3 : AxNat.dvd x1 x0) -> Eq.{1} AxNat (AxNat.div x0 (AxNat.div x0 x1)) x1))))\n",
    "Nat.divisorFlip : ((x0 : AxNat) -> ((x1 : AxNat) -> AxNat))\n",
    "Nat.divisorFlip_involutive : ((x0 : AxNat) -> ((x1 : AxNat.lt AxNat.zero x0) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.divisorFlip x0 (AxNat.divisorFlip x0 x2)) x2)))\n",
    "Nat.divisorFlip_injectiveOn : ((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat.lt AxNat.zero x0) -> AxNat.injectiveOn (fun (x3 : AxNat) => AxNat.divisorFlip x0 x3) x1)))\n",
    "Nat.divisorFlip_mapsInto : ((x0 : AxNat) -> ((x1 : AxNat.lt AxNat.zero x0) -> AxNat.mapsInto (fun (x2 : AxNat) => AxNat.divisorFlip x0 x2) (AxNat.succ x0)))\n",
    "Nat.sumDivisorsBy_reindex : ((x0 : ((x0 : AxNat) -> AxNat)) -> ((x1 : AxNat) -> ((x2 : AxNat.lt AxNat.zero x1) -> Eq.{1} AxNat (AxNat.sumDivisorsBy x0 x1) (AxNat.sumDivisorsBy (fun (x3 : AxNat) => x0 (AxNat.div x1 x3)) x1))))\n",
);
