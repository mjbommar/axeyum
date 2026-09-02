//! Seven theorems about `Nat.Abundant`/`Nat.Deficient`, closed after
//! revisiting `abundant_deficient.rs`'s "stays open" verdict.
//!
//! ## The divergence verdict, revised
//!
//! `abundant_deficient.rs`'s module doc argues our bodies are "provably
//! equivalent to, and not definitionally identical with, Mathlib's" and
//! concludes every `ml430` mirror against them "therefore stays open" --
//! citing an equivalence the author derived independently
//! (`sumDivisors n = (∑ properDivisors n) + n`).
//!
//! That derivation is exactly right, and Mathlib proves it too, by name:
//!
//! ```text
//! -- Mathlib/NumberTheory/Divisors.lean:391
//! theorem sum_divisors_eq_sum_properDivisors_add_self :
//!     ∑ i ∈ divisors n, i = (∑ i ∈ properDivisors n, i) + n
//!
//! -- Mathlib/NumberTheory/Divisors.lean:404 (0 < n)
//! theorem perfect_iff_sum_divisors_eq_two_mul :
//!     Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n
//!
//! -- Mathlib/NumberTheory/FactorisationProperties.lean:180
//! theorem abundant_iff_sum_divisors :
//!     Abundant n ↔ 2 * n < ∑ i ∈ n.divisors, i
//! ```
//!
//! So `Lt (mul 2 n) (sumDivisors n)` is not an externally-inferred
//! equivalent of Mathlib's `Abundant` that we would need our own hard
//! induction to certify (the `Nat.multichoose` shape, where ours DEFINES
//! what Mathlib PROVES as a theorem about an independent, hard-to-relate
//! double recursion, per the mirror-flip criterion in `CLAUDE.md`). It is
//! Mathlib's OWN endorsed alternate characterization, proved by a one-line
//! `grind` from a three-line divisor-partition lemma
//! (`divisors n = insert n (properDivisors n)`, `n ∉ properDivisors n`).
//! That is the `Max.max`/`Min.min` precedent (ADR-1415): "same function;
//! only the delivery differs, which is elaboration, not content" -- here the
//! "delivery" is *which* divisor sum you compare against *which* multiple of
//! `n`, both sides settled, checked, and named by Mathlib itself.
//!
//! `Nat.Perfect` (`perfect.rs`) already uses exactly this alternate form
//! (`sumDivisors n = 2 * n`, matching `perfect_iff_sum_divisors_eq_two_mul`
//! verbatim modulo the `0 < n` guard -- see the caveat below), so this
//! module treats all three predicates the same way.
//!
//! **This is a per-statement judgment, not a blanket reversal** -- every one
//! of the ten `ml430` facts drawn for this lane states a proposition
//! entirely in terms of `Abundant`/`Deficient`/`Perfect`/`Prime`/`dvd`/`mul`,
//! so all ten sit on the honest side of the line for the SAME reason. The
//! seven proved here are the ones this lane also found a proof for; the
//! other three (`abundant_of_dvd`, `abundant_mul_left`,
//! `prime_deficient_pow`) are recorded as open for a DIFFERENT reason
//! entirely -- missing supporting infrastructure (divisor-sum monotonicity
//! under `dvd`, and a prime-power divisor characterization), not a
//! divergence question. See the lane's report for the boundary.
//!
//! **One real divergence remains, at `n = 0`, and none of these ten facts
//! touch it.** Mathlib's `Perfect` carries an explicit `0 < n` conjunct, so
//! `Perfect 0` is `False` there; ours (`perfect.rs`) has no such conjunct,
//! and `sumDivisors 0 = 0 = mul 2 0`, so `Perfect 0` is *provable* here.
//! `Abundant 0`/`Deficient 0` agree with Mathlib (both `Lt 0 0`, i.e. false,
//! on both sides) precisely because the strict inequalities don't need the
//! positivity guard the equality does. Every trichotomy/prime fact below
//! either carries an explicit `n ≠ 0` hypothesis (matching Mathlib's own
//! guard) or never instantiates at `0` (`Prime 0` is impossible;
//! `deficient_one`/`abundant_twelve` are concrete positive numerals), so
//! this residual divergence never enters a proof here.
//!
//! ## What's proved
//!
//! - [`declare_deficient_one`], [`declare_abundant_twelve`]: concrete
//!   evaluations. `abundant_twelve` forms nothing larger than `28`
//!   (`sumDivisors 12`, already validated cheap in
//!   `abundant_deficient_tests.rs`) -- nowhere near the magnitude regime
//!   where this kernel's unary `Nat` literals get expensive.
//! - [`declare_prime_deficient`]: `Prime n → Deficient n`, from
//!   `sum_divisors_prime` (`perfect.rs`: `sumDivisors p = succ p`) and
//!   `prime_one_lt` (`1 < p`), via `add_lt_add_left` and a bridge lemma
//!   [`two_mul_eq_add_self`] (`mul 2 n` is STUCK for symbolic `n` -- `Nat.mul`
//!   recurses on its RIGHT argument and `n` sits there -- so relating it to
//!   `add n n` needs a real theorem, not a reduction).
//! - [`declare_prime_not_perfect`], [`declare_prime_not_abundant`]: both
//!   fall out of `prime_deficient` plus irreflexivity of `Lt`, reusing the
//!   already-declared theorem rather than re-deriving `sum_divisors_prime`.
//! - [`declare_abundant_iff_not_perfect_and_not_deficient`],
//!   [`declare_deficient_iff_not_abundant_and_not_perfect`]: both are
//!   trichotomy of `Nat`'s order applied to the pair `(mul 2 n, sumDivisors
//!   n)` -- `lt_or_ge`/`lt_or_eq_of_le` supply the case split, `lt_irrefl`
//!   discharges both contradiction branches. The `n ≠ 0` hypothesis is
//!   carried (matching Mathlib's guard, needed there for the `Perfect`
//!   positivity conjunct) but unused in the proof term: these hold
//!   unconditionally for our subtraction-free forms, including at `n = 0`.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_lt_or_ge};
use super::primes::prime_condition;
use super::steps::absurd;
use super::steps::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Shared arithmetic/order combinators.
// ============================================================================

/// `Le a b` from `h : Lt a b`. `Lt a b` is `Le (succ a) b`; `le_succ a : Le a
/// (succ a)` composed with `le_trans` gives `Le a b` directly.
fn le_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let succ_a = d.succ(a);
    let le_a_succ_a = d.lemma(p.le_succ, &[a]);
    d.lemma(p.le_trans, &[a, succ_a, b, le_a_succ_a, h])
}

/// From `h : Lt a b` and `heq : Eq b a`, derive `False`: transport `h` along
/// `heq` (rewriting the `b` position to `a`) gives `Lt a a`, absurd via
/// `lt_irrefl`.
fn false_of_lt_and_eq_rev(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    heq: ExprId,
) -> ExprId {
    let motive = d.eq_motive(b, &move |d, z| d.lt(a, z));
    let lt_a_a = d.transport(b, motive, h, a, heq);
    d.lemma(p.lt_irrefl, &[a, lt_a_a])
}

/// From `h : Lt a b` and `hlt : Lt b a`, derive `False`: `le_of_lt` turns
/// `hlt` into `Le b a`, `lt_of_lt_of_le` chains it with `h` into `Lt a a`,
/// absurd via `lt_irrefl`.
fn false_of_lt_and_lt_rev(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    hlt: ExprId,
) -> ExprId {
    let le_b_a = le_of_lt(d, p, b, a, hlt);
    let lt_a_a = d.lemma(p.lt_of_lt_of_le, &[a, b, a, h, le_b_a]);
    d.lemma(p.lt_irrefl, &[a, lt_a_a])
}

/// `Eq (mul 2 n) (add n n)`. `mul 2 n` is STUCK for symbolic `n` (`Nat.mul`
/// recurses on its RIGHT argument, and `n` sits on the right here), so this
/// is a real theorem: `mul_comm` moves the `2` to the reducing side (`mul n
/// 2` unfolds by pure iota to `add (add zero n) n`), and `zero_add` clears
/// the inner `zero`.
fn two_mul_eq_add_self(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let two = d.num(2);
    let mul_2_n = d.mul(two, n);
    let mul_n_2 = d.mul(n, two);
    let comm = d.lemma(p.mul_comm, &[two, n]); // Eq (mul 2 n) (mul n 2)
    let zero = d.zero();
    let add_0_n = d.add(zero, n);
    let za = d.lemma(p.zero_add, &[n]); // Eq (add zero n) n
    let add_n_n = d.add(n, n);
    // Eq (add (add zero n) n) (add n n); defeq `Eq mul_n_2 (add n n)` since
    // `mul n 2` reduces by pure iota to `add (add zero n) n`.
    let rewritten = d.congr(add_0_n, n, za, &move |d, x| d.add(x, n));
    d.trans(mul_2_n, mul_n_2, add_n_n, comm, rewritten)
}

// ============================================================================
// Concrete evaluations.
// ============================================================================

/// `Nat.deficient_one : Deficient (succ zero)`. `Deficient 1` unfolds to `Lt
/// (sumDivisors 1) (mul 2 1)`, defeq `Lt 1 2` (`sumDivisors 1 = 1`,
/// `sum_divisors_one`; `mul 2 1 = 2` by pure reduction), defeq `Le 2 2` --
/// `le_refl 2` directly.
pub(super) fn declare_deficient_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let proof = d.lemma(p.le_refl, &[two]);
    let ty = d.const_app(p.deficient, &[one]);
    d.declare_theorem(p.deficient_one, ty, proof)
}

/// `Nat.abundant_twelve : Abundant 12`. `Abundant 12` unfolds to `Lt (mul 2
/// 12) (sumDivisors 12)`, defeq `Lt 24 28` (`sumDivisors 12 = 28`, checked
/// cheap in `abundant_deficient_tests.rs`), defeq `Le 25 28`, which is `Le 25
/// (add 25 3)` -- `le_add_right 25 3` directly. Largest magnitude formed is
/// `28`, far below where this kernel's unary literals get expensive.
pub(super) fn declare_abundant_twelve(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let twelve = d.num(12);
    let twenty_five = d.num(25);
    let three = d.num(3);
    let proof = d.lemma(p.le_add_right, &[twenty_five, three]);
    let ty = d.const_app(p.abundant, &[twelve]);
    d.declare_theorem(p.abundant_twelve, ty, proof)
}

// ============================================================================
// Prime facts.
// ============================================================================

/// `Nat.prime_deficient : ∀ n, Prime n → Deficient n`.
///
/// `prime_one_lt` gives `Lt one n`; `add_lt_add_left` lifts it to `Lt (add n
/// one) (add n n)`, defeq `Lt (succ n) (add n n)`. [`two_mul_eq_add_self`]
/// bridges `add n n` to `mul 2 n`, and `sum_divisors_prime` bridges `succ n`
/// to `sumDivisors n`, both by `transport` along a `symm`'d equation.
pub(super) fn declare_prime_deficient(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_deficient, 1, &|d, v| {
        let n = v[0];
        let prime_ty = prime_condition(d, &p, n);
        let deficient_n = d.const_app(p.deficient, &[n]);
        let stmt = d.arrow(prime_ty, deficient_n);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let h1 = d.lemma(p.prime_one_lt, &[n, prime_hyp]); // Lt one n
        let one = d.num(1);
        let h2 = d.lemma(p.add_lt_add_left, &[n, one, n, h1]); // Lt (add n one) (add n n)

        let add_n_n = d.add(n, n);
        let two = d.num(2);
        let mul_2n = d.mul(two, n);
        let two_mul_eq = two_mul_eq_add_self(d, &p, n); // Eq (mul 2 n) (add n n)
        let symm_eq = d.symm(mul_2n, add_n_n, two_mul_eq); // Eq (add n n) (mul 2 n)
        let succ_n = d.succ(n);
        let motive1 = d.eq_motive(add_n_n, &move |d, z| d.lt(succ_n, z));
        let h3 = d.transport(add_n_n, motive1, h2, mul_2n, symm_eq); // Lt (succ n) (mul 2 n)

        let sdp_eq = d.lemma(p.sum_divisors_prime, &[n, prime_hyp]); // Eq (sumDivisors n) (succ n)
        let sum_n = d.const_app(p.sum_divisors, &[n]);
        let symm_sdp = d.symm(sum_n, succ_n, sdp_eq); // Eq (succ n) (sumDivisors n)
        let motive2 = d.eq_motive(succ_n, &move |d, z| d.lt(z, mul_2n));
        let deficient_proof = d.transport(succ_n, motive2, h3, sum_n, symm_sdp); // Lt (sumDivisors n) (mul 2 n)

        let proof = d.lam_fv(prime_fv, prime_ty, deficient_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_not_perfect : ∀ p, Prime p → Not (Perfect p)`. `Perfect p`
/// gives `Eq (sumDivisors p) (mul 2 p)`; transporting `prime_deficient`'s
/// `Lt (sumDivisors p) (mul 2 p)` along it yields `Lt (mul 2 p) (mul 2 p)`,
/// absurd via `lt_irrefl`.
pub(super) fn declare_prime_not_perfect(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_not_perfect, 1, &|d, v| {
        let n = v[0];
        let prime_ty = prime_condition(d, &p, n);
        let perfect_n = d.const_app(p.perfect, &[n]);
        let not_perfect_n = d.const_app(p.logic.not, &[perfect_n]);
        let stmt = d.arrow(prime_ty, not_perfect_n);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let deficient_proof = d.lemma(p.prime_deficient, &[n, prime_hyp]); // Lt (sumDivisors n) (mul 2 n)

        let sum_n = d.const_app(p.sum_divisors, &[n]);
        let two = d.num(2);
        let mul_2n = d.mul(two, n);

        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv); // Perfect n = Eq (sumDivisors n) (mul 2 n)
        let motive = d.eq_motive(sum_n, &move |d, z| d.lt(z, mul_2n));
        let lt_mul_mul = d.transport(sum_n, motive, deficient_proof, mul_2n, heq); // Lt (mul 2 n) (mul 2 n)
        let false_proof = d.lemma(p.lt_irrefl, &[mul_2n, lt_mul_mul]);
        let not_perfect_body = d.lam_fv(heq_fv, perfect_n, false_proof);

        let proof = d.lam_fv(prime_fv, prime_ty, not_perfect_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_not_abundant : ∀ n, Prime n → Not (Abundant n)`. `Abundant n`
/// gives `Lt (mul 2 n) (sumDivisors n)`; chained with `prime_deficient`'s
/// `Lt (sumDivisors n) (mul 2 n)` via `lt_of_lt_of_le` (after `le_of_lt` on
/// the deficient side) yields `Lt (mul 2 n) (mul 2 n)`, absurd via
/// `lt_irrefl`.
pub(super) fn declare_prime_not_abundant(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_not_abundant, 1, &|d, v| {
        let n = v[0];
        let prime_ty = prime_condition(d, &p, n);
        let abundant_n = d.const_app(p.abundant, &[n]);
        let not_abundant_n = d.const_app(p.logic.not, &[abundant_n]);
        let stmt = d.arrow(prime_ty, not_abundant_n);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let deficient_proof = d.lemma(p.prime_deficient, &[n, prime_hyp]); // Lt (sumDivisors n) (mul 2 n)

        let sum_n = d.const_app(p.sum_divisors, &[n]);
        let two = d.num(2);
        let mul_2n = d.mul(two, n);

        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv); // Abundant n = Lt (mul 2 n) (sumDivisors n)
        let le_sum_mul = le_of_lt(d, &p, sum_n, mul_2n, deficient_proof); // Le (sumDivisors n) (mul 2 n)
        let lt_mul_mul = d.lemma(p.lt_of_lt_of_le, &[mul_2n, sum_n, mul_2n, hp, le_sum_mul]); // Lt (mul 2 n) (mul 2 n)
        let false_proof = d.lemma(p.lt_irrefl, &[mul_2n, lt_mul_mul]);
        let not_abundant_body = d.lam_fv(hp_fv, abundant_n, false_proof);

        let proof = d.lam_fv(prime_fv, prime_ty, not_abundant_body);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// Trichotomy.
// ============================================================================

/// `Nat.abundant_iff_not_perfect_and_not_deficient : ∀ n, Not (Eq zero n) →
/// Iff (Abundant n) (And (Not (Perfect n)) (Not (Deficient n)))`.
///
/// With `x := mul 2 n`, `y := sumDivisors n`: `Lt x y ↔ Not (Eq y x) ∧ Not
/// (Lt y x)`. Forward: [`false_of_lt_and_eq_rev`]/[`false_of_lt_and_lt_rev`]
/// discharge both conjuncts from `h : Lt x y`. Backward: `cases_lt_or_ge`
/// splits `Lt x y ∨ Le y x`; the `Le y x` branch splits again via
/// `lt_or_eq_of_le` into `Lt y x ∨ Eq y x`, each contradicting one conjunct.
///
/// The `Not (Eq zero n)` hypothesis is carried (matching Mathlib's `0 ≠ n`
/// guard) but never used: this holds unconditionally for our
/// subtraction-free forms, including at `n = 0` (`abundant_deficient.rs`'s
/// own module doc: both sides are `Lt 0 0` there).
pub(super) fn declare_abundant_iff_not_perfect_and_not_deficient(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.abundant_iff_not_perfect_and_not_deficient, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let hyp_ty = {
            let eq_0n = d.eq(zero, n);
            d.const_app(p.logic.not, &[eq_0n])
        };

        let two = d.num(2);
        let x = d.mul(two, n);
        let y = d.const_app(p.sum_divisors, &[n]);

        let lt_xy = d.lt(x, y);
        let eq_yx = d.eq(y, x);
        let not_eq_yx = d.const_app(p.logic.not, &[eq_yx]);
        let lt_yx = d.lt(y, x);
        let not_lt_yx = d.const_app(p.logic.not, &[lt_yx]);
        let conj = d.const_app(p.logic.and, &[not_eq_yx, not_lt_yx]);

        // forward : Lt x y -> And (Not (Eq y x)) (Not (Lt y x))
        let forward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let part1 = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let false_proof = false_of_lt_and_eq_rev(d, &p, x, y, h, heq);
                d.lam_fv(heq_fv, eq_yx, false_proof)
            };
            let part2 = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let false_proof = false_of_lt_and_lt_rev(d, &p, x, y, h, hlt);
                d.lam_fv(hlt_fv, lt_yx, false_proof)
            };
            let and_proof = d.const_app(p.logic.and_intro, &[not_eq_yx, not_lt_yx, part1, part2]);
            d.lam_fv(h_fv, lt_xy, and_proof)
        };

        // backward : And (Not (Eq y x)) (Not (Lt y x)) -> Lt x y
        let backward = {
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let h1 = and_left(d, not_eq_yx, not_lt_yx, hand); // Not (Eq y x)
            let h2 = and_right(d, not_eq_yx, not_lt_yx, hand); // Not (Lt y x)

            let goal = lt_xy;
            let small = &|_d: &mut NatDev<'_>, _n: ExprId, h: ExprId| h;
            let big = &move |d: &mut NatDev<'_>, _n: ExprId, h_le: ExprId| -> ExprId {
                let split = d.lemma(p.lt_or_eq_of_le, &[y, x, h_le]); // Or (Lt y x) (Eq y x)
                let on_lt = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let false_proof = d.apply(h2, &[hh]);
                    let result = absurd(d, goal, false_proof);
                    d.lam_fv(hh_fv, lt_yx, result)
                };
                let on_eq = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let false_proof = d.apply(h1, &[hh]);
                    let result = absurd(d, goal, false_proof);
                    d.lam_fv(hh_fv, eq_yx, result)
                };
                or_cases(d, lt_yx, eq_yx, goal, on_lt, on_eq, split)
            };
            let case_result = cases_lt_or_ge(d, &p, x, y, &move |_d, _n| goal, small, big);
            d.lam_fv(hand_fv, conj, case_result)
        };

        let iff_ty = d.const_app(p.logic.iff, &[lt_xy, conj]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[lt_xy, conj, forward, backward]);

        let stmt = d.arrow(hyp_ty, iff_ty);
        let hyp_fv = d.fresh_fvar();
        let proof = d.lam_fv(hyp_fv, hyp_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.deficient_iff_not_abundant_and_not_perfect : ∀ n, Not (Eq n zero) →
/// Iff (Deficient n) (And (Not (Abundant n)) (Not (Perfect n)))`.
///
/// The mirror image of
/// [`declare_abundant_iff_not_perfect_and_not_deficient`]: with `x := mul 2
/// n`, `y := sumDivisors n`, `Lt y x ↔ Not (Lt x y) ∧ Not (Eq y x)`. Same
/// technique, conjunct order and `Eq` direction swapped to match this fact's
/// statement (Mathlib's own two lemmas differ the same way).
pub(super) fn declare_deficient_iff_not_abundant_and_not_perfect(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.deficient_iff_not_abundant_and_not_perfect, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let hyp_ty = {
            let eq_n0 = d.eq(n, zero);
            d.const_app(p.logic.not, &[eq_n0])
        };

        let two = d.num(2);
        let x = d.mul(two, n);
        let y = d.const_app(p.sum_divisors, &[n]);

        let lt_yx = d.lt(y, x);
        let lt_xy = d.lt(x, y);
        let not_lt_xy = d.const_app(p.logic.not, &[lt_xy]);
        let eq_yx = d.eq(y, x);
        let not_eq_yx = d.const_app(p.logic.not, &[eq_yx]);
        let conj = d.const_app(p.logic.and, &[not_lt_xy, not_eq_yx]);

        // forward : Lt y x -> And (Not (Lt x y)) (Not (Eq y x))
        let forward = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let part1 = {
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let false_proof = false_of_lt_and_lt_rev(d, &p, y, x, h, hlt);
                d.lam_fv(hlt_fv, lt_xy, false_proof)
            };
            let part2 = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv); // Eq y x
                let heq_rev = d.symm(y, x, heq); // Eq x y
                let false_proof = false_of_lt_and_eq_rev(d, &p, y, x, h, heq_rev);
                d.lam_fv(heq_fv, eq_yx, false_proof)
            };
            let and_proof = d.const_app(p.logic.and_intro, &[not_lt_xy, not_eq_yx, part1, part2]);
            d.lam_fv(h_fv, lt_yx, and_proof)
        };

        // backward : And (Not (Lt x y)) (Not (Eq y x)) -> Lt y x
        let backward = {
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let h1 = and_left(d, not_lt_xy, not_eq_yx, hand); // Not (Lt x y)
            let h2 = and_right(d, not_lt_xy, not_eq_yx, hand); // Not (Eq y x)

            let goal = lt_yx;
            let small = &|_d: &mut NatDev<'_>, _n: ExprId, h: ExprId| h;
            let big = &move |d: &mut NatDev<'_>, _n: ExprId, h_le: ExprId| -> ExprId {
                let split = d.lemma(p.lt_or_eq_of_le, &[x, y, h_le]); // Or (Lt x y) (Eq x y)
                let on_lt = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv);
                    let false_proof = d.apply(h1, &[hh]);
                    let result = absurd(d, goal, false_proof);
                    d.lam_fv(hh_fv, lt_xy, result)
                };
                let on_eq = {
                    let hh_fv = d.fresh_fvar();
                    let hh = d.kernel().fvar(hh_fv); // Eq x y
                    let hh_rev = d.symm(x, y, hh); // Eq y x
                    let false_proof = d.apply(h2, &[hh_rev]);
                    let result = absurd(d, goal, false_proof);
                    let eq_xy = d.eq(x, y);
                    d.lam_fv(hh_fv, eq_xy, result)
                };
                let eq_xy = d.eq(x, y);
                or_cases(d, lt_xy, eq_xy, goal, on_lt, on_eq, split)
            };
            let case_result = cases_lt_or_ge(d, &p, y, x, &move |_d, _n| goal, small, big);
            d.lam_fv(hand_fv, conj, case_result)
        };

        let iff_ty = d.const_app(p.logic.iff, &[lt_yx, conj]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[lt_yx, conj, forward, backward]);

        let stmt = d.arrow(hyp_ty, iff_ty);
        let hyp_fv = d.fresh_fvar();
        let proof = d.lam_fv(hyp_fv, hyp_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all seven theorems. Must run after
/// [`super::abundant_deficient::declare_abundant_deficient_all`] (needs
/// `Nat.Abundant`/`Nat.Deficient`) and
/// [`super::perfect::declare_perfect_all`] (needs `Nat.Perfect`,
/// `Nat.sumDivisors`, `sum_divisors_prime`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_abundant_deficient_lemmas_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_deficient_one(d, p)?;
    declare_abundant_twelve(d, p)?;
    declare_prime_deficient(d, p)?;
    declare_prime_not_perfect(d, p)?;
    declare_prime_not_abundant(d, p)?;
    declare_abundant_iff_not_perfect_and_not_deficient(d, p)?;
    declare_deficient_iff_not_abundant_and_not_perfect(d, p)?;
    Ok(())
}
