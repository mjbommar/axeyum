//! Order and growth theorems about `Nat.primeCounting'`, the prime-counting
//! function — the shelf ADR-1637 deliberately left empty.
//!
//! ## Why this file exists now and did not exist on 2026-09-05
//!
//! `Nat.primeCounting` / `Nat.primeCounting'` (`prime_counting.rs`) were
//! declared as CONSTRUCTIONS ONLY under ADR-0653, because five of the ten
//! rows of the preregistered held-out family
//! `discrete-step-and-counting-bounds` are statements about that pair, and the
//! family had never been scored. ADR-1637's lane declined the whole shelf on
//! that ground.
//!
//! That family moved `held-out -> development` on 2026-09-05
//! (`artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`,
//! `partition_moves`, authority ADR-0542): a producer contract cited
//! `F:ml430-int-le-sub-one-of-not-le-fc32b89d` by name as a `non_example`, and
//! per ADR-0542 the partition unit is the whole family, so all ten rows moved
//! together. The blind-evaluation value was spent by the citation, not by this
//! file; the move is recorded as irreversible. So the shelf is now writable
//! from `development`, and this file is that shelf.
//!
//! **`natural-max-power-dividing` is still held-out** and it carries
//! `Nat.divMaxPow`'s base cases and Bertrand's postulate. Nothing here
//! mentions `Nat.divMaxPow`, by construction.
//!
//! ## `primeCounting'` is `countRange` under two aliases
//!
//! ```text
//! primeCounting' n := Nat.count Nat.isPrime n        (prime_counting.rs)
//! count dec n      := Nat.countRange dec n           (count_and_div_max_pow.rs)
//! ```
//!
//! Both are `Regular` definitions with strictly decreasing delta heights
//! (14 -> 13 -> 12), so `primeCounting' n` and `countRange isPrime n` are
//! definitionally equal by delta alone — no rewriting, no transport. That is
//! the whole content of the first theorem below: `countRange_le_of_le`
//! (`totient_lemmas.rs`) already IS monotonicity of `primeCounting'`, and the
//! kernel's defeq check unfolds the two aliases while checking the stated
//! type. It is stated here anyway because a name the fact ledger can cite is
//! the deliverable; an unstated defeq is not a theorem.
//!
//! ## What is declared
//!
//! | name | statement |
//! | --- | --- |
//! | `Nat.primeCounting'_mono` | `∀ m n, m ≤ n → primeCounting' m ≤ primeCounting' n` |
//! | `Nat.primeCounting_mono` | `∀ m n, m ≤ n → primeCounting m ≤ primeCounting n` |

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps};
use super::primes::prime_condition;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.primeCounting' n`.
fn prime_counting_prime(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.prime_counting_prime, &[n])
}

/// `Nat.primeCounting n`.
fn prime_counting(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.prime_counting, &[n])
}

/// The two monotonicity rows of the prime-counting shelf.
///
/// Both are `countRange_le_of_le` at the predicate `Nat.isPrime`, accepted
/// through the delta chain documented in this module's header. The second
/// additionally uses `succ_le_succ` to move `m ≤ n` to `succ m ≤ succ n`,
/// because `primeCounting n` is `primeCounting' (succ n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_counting_order(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // primeCounting'_mono : ∀ m n, Le m n → Le (primeCounting' m) (primeCounting' n)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let pred = d.const_app(p.is_prime, &[]);
        let proof = d.lemma(p.count_range_le_of_le, &[pred, m, n, h]);

        let left = prime_counting_prime(d, &p, m);
        let right = prime_counting_prime(d, &p, n);
        let concl = d.le(left, right);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(m_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(m_fv, nat, mid)
        };
        d.declare_theorem(p.prime_counting_prime_mono, ty, value)?;
    }

    // primeCounting_mono : ∀ m n, Le m n → Le (primeCounting m) (primeCounting n)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h_ty = d.le(m, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sm = d.succ(m);
        let sn = d.succ(n);
        let hs = d.lemma(p.succ_le_succ, &[m, n, h]);
        let pred = d.const_app(p.is_prime, &[]);
        let proof = d.lemma(p.count_range_le_of_le, &[pred, sm, sn, hs]);

        let left = prime_counting(d, &p, m);
        let right = prime_counting(d, &p, n);
        let concl = d.le(left, right);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(n_fv, nat, inner);
            d.pi_fv(m_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(n_fv, nat, inner);
            d.lam_fv(m_fv, nat, mid)
        };
        d.declare_theorem(p.prime_counting_mono, ty, value)?;
    }

    Ok(())
}

// ============================================================================
// The bridge: `Nat.isPrime` is the primality predicate it is named for.
// ============================================================================

/// `fun j => Nat.beq (Nat.mod n (succ j)) zero` — `Nat.isPrime`'s divisor
/// predicate at `n`.
///
/// Spelled exactly as `prime_counting.rs` spells it inside `Nat.isPrime`'s
/// body, so that `isPrime n` delta-reduces to
/// `beq (countRange (divisor_pred n) n) 2` up to alpha only. Every proof below
/// is stated against `countRange (divisor_pred n) n` and accepted at
/// `isPrime n` through that one step.
fn divisor_pred(d: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let candidate = d.succ(j);
    let remainder = d.modulo(n, candidate);
    let zero = d.zero();
    let body = d.beq(remainder, zero);
    d.lam_fv(j_fv, nat, body)
}

/// `Eq (add 1 k) (succ k)`.
///
/// `Nat.add` recurses on its RIGHT argument, so `add 1 k` is STUCK at a
/// symbolic `k` — it is not `succ k` by reduction, and every step below that
/// meets `countRange_split`'s shifted predicate `fun k => f (add 1 k)` needs
/// this equation to get back to a `succ`. `succ_add zero k` then `zero_add k`
/// under a `congr succ`.
fn one_add_eq_succ(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId) -> ExprId {
    let zero = d.zero();
    let one = d.num(1);
    let sum = d.add(one, k);
    let step = d.lemma(p.succ_add, &[zero, k]);
    let inner = d.add(zero, k);
    let inner_succ = d.succ(inner);
    let base = d.lemma(p.zero_add, &[k]);
    let lifted = d.congr(inner, k, base, &|d, x| d.succ(x));
    let target = d.succ(k);
    d.trans(sum, inner_succ, target, step, lifted)
}

/// `Dvd 1 n` — the witness is `n` itself, since `dvd a n := ∃ q, n = a * q`.
fn one_dvd(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.num(1);
    let level_one = d.level_one();
    let predicate = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let product = d.mul(one, q);
        let body = d.eq(n, product);
        d.lam_fv(q_fv, nat, body)
    };
    let product = d.mul(one, n);
    let forward = d.lemma(p.one_mul, &[n]);
    let equation = d.symm(product, n, forward);
    let intro_name = p.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![level_one]);
    d.apply(intro, &[nat, predicate, n, equation])
}

/// `Eq (mod n c) zero` from `Dvd c n`, through `Nat.dvd_iff_mod_eq_zero`.
fn mod_eq_zero_of_dvd_bridge(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    c: ExprId,
    n: ExprId,
    proof: ExprId,
) -> ExprId {
    let bridge = d.lemma(p.dvd_iff_mod_eq_zero, &[c, n]);
    let left = d.dvd(c, n);
    let remainder = d.modulo(n, c);
    let zero = d.zero();
    let right = d.eq(remainder, zero);
    let forward = iff_forward(d, left, right, bridge);
    d.apply(forward, &[proof])
}

/// `hprime : prime_condition (succ (succ m)) ⊢ Eq Bool (isPrime (succ (succ m))) true`.
///
/// The whole content of the bridge, at the only shape where it can hold:
/// `Nat.isPrime n` counts the divisors of `n` among `1 … n`, and a prime has
/// exactly two of them, so `n` must be at least `2` for the count to be `2` at
/// all. Three pieces — the two witnesses, and the emptiness of the middle:
///
/// * `divisor_pred n 0` is `beq (n % 1) 0` — true, because `1 ∣ n`.
/// * `divisor_pred n (n-1)` is `beq (n % n) 0` — true, by `mod_self`.
/// * every index strictly between is false, because a divisor `c` with
///   `2 ≤ c ≤ n-1` contradicts primality's own divisor clause: `c = 1` is
///   refuted by `succ_ne_zero` and `c = n` by `lt_irrefl`.
///
/// The count is assembled by peeling the LAST index with
/// `countRange_succ_of_true` and the FIRST with `countRange_split` at `1`,
/// leaving `countRange_eq_zero_of_all_false` for the middle: `2 = 1 + 0 + 1`.
fn is_prime_true_at_double_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    hprime: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();
    let one = d.num(1);
    let sm = d.succ(m);
    let n = d.succ(sm);
    let f = divisor_pred(d, n);

    // The divisor clause of `prime_condition n`, as a function.
    let hdivisors = {
        let two = d.num(2);
        let lower = d.le(two, n);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hypothesis = d.dvd(c, n);
        let trivial = d.eq(c, one);
        let whole = d.eq(c, n);
        let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
        let body = d.arrow(hypothesis, disjunction);
        let divisors = d.pi_fv(c_fv, nat, body);
        and_right(d, lower, divisors, hprime)
    };

    // hlast : divisor_pred n (succ m) = true, because `n % n = 0`.
    let hlast = {
        let remainder = d.modulo(n, n);
        let self_zero = d.lemma(p.mod_self, &[n]);
        d.lemma(p.beq_eq_true_of_eq, &[remainder, zero, self_zero])
    };

    // hfirst : divisor_pred n 0 = true, because `1 ∣ n`.
    let hfirst = {
        let witness = one_dvd(d, &p, n);
        let mod_one = mod_eq_zero_of_dvd_bridge(d, &p, one, n, witness);
        let remainder = d.modulo(n, one);
        d.lemma(p.beq_eq_true_of_eq, &[remainder, zero, mod_one])
    };

    // c1 : countRange f 1 = 1.
    let count_at_one = {
        let peel = d.lemma(p.count_range_succ_of_true, &[f, zero, hfirst]);
        let empty = d.lemma(p.count_range_zero, &[f]);
        let inner = d.const_app(p.count_range, &[f, zero]);
        let lifted = d.congr(inner, zero, empty, &|d, x| d.succ(x));
        let at_one = d.const_app(p.count_range, &[f, one]);
        let inner_succ = d.succ(inner);
        d.trans(at_one, inner_succ, one, peel, lifted)
    };

    // The shifted predicate `countRange_split` produces at `m := 1`.
    let shifted = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let index = d.add(one, k);
        let body = d.apply(f, &[index]);
        d.lam_fv(k_fv, nat, body)
    };

    // hall : ∀ k, Lt k m → shifted k = false.
    let hall = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hlt_ty = d.lt(k, m);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);

        // The divisor this index names, once `add 1 k` is unstuck: `k + 2`.
        let sk = d.succ(k);
        let c = d.succ(sk);

        // hnd : Not (Dvd c n) — primality's divisor clause refuted twice.
        let hnd = {
            let hd_ty = d.dvd(c, n);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let dichotomy = d.apply(hdivisors, &[c, hd]);
            let left_ty = d.eq(c, one);
            let right_ty = d.eq(c, n);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);

            // c = 1 is `succ (succ k) = succ zero`: strip one `succ`, then
            // `succ_ne_zero`.
            let left_branch = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let stripped = d.lemma(p.succ_injective, &[sk, zero, he]);
                let ne = d.lemma(p.succ_ne_zero, &[k]);
                let body = d.apply(ne, &[stripped]);
                d.lam_fv(he_fv, left_ty, body)
            };

            // c = n is `succ (succ k) = succ (succ m)`: strip twice to `k = m`,
            // then `lt_irrefl m` against the range hypothesis.
            let right_branch = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let once = d.lemma(p.succ_injective, &[sk, sm, he]);
                let twice = d.lemma(p.succ_injective, &[k, m, once]);
                let motive = d.eq_motive(k, &|d, x| d.lt(x, m));
                let shifted_lt = d.transport(k, motive, hlt, m, twice);
                let irrefl = d.lemma(p.lt_irrefl, &[m]);
                let body = d.apply(irrefl, &[shifted_lt]);
                d.lam_fv(he_fv, right_ty, body)
            };

            let anon = d.anon_name();
            let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
            let motive = d.kernel().lam(anon, or_ty, false_ty, BinderInfo::Default);
            let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                or_rec,
                &[
                    left_ty,
                    right_ty,
                    motive,
                    left_branch,
                    right_branch,
                    dichotomy,
                ],
            );
            d.lam_fv(hd_fv, hd_ty, body)
        };

        // hne : Not (n % c = 0), by composing `hnd` with the reverse bridge.
        let hne = {
            let remainder = d.modulo(n, c);
            let heq_ty = d.eq(remainder, zero);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let bridge = d.lemma(p.dvd_iff_mod_eq_zero, &[c, n]);
            let left = d.dvd(c, n);
            let reverse = iff_reverse(d, left, heq_ty, bridge);
            let dvd_proof = d.apply(reverse, &[heq]);
            let body = d.apply(hnd, &[dvd_proof]);
            d.lam_fv(heq_fv, heq_ty, body)
        };

        // The goal is stated at the STUCK index `add 1 k`; transport the proof
        // built at `succ k` along `one_add_eq_succ`.
        let at_succ = {
            let remainder = d.modulo(n, c);
            d.lemma(p.beq_eq_false_of_ne, &[remainder, zero, hne])
        };
        let unstick = one_add_eq_succ(d, &p, k);
        let sum = d.add(one, k);
        let back = d.symm(sum, sk, unstick);
        let motive = d.eq_motive(sk, &|d, x| {
            let candidate = d.succ(x);
            let remainder = d.modulo(n, candidate);
            let zero = d.zero();
            let lhs = d.beq(remainder, zero);
            let false_value = d.bool_false();
            d.bool_eq(lhs, false_value)
        });
        let body = d.transport(sk, motive, at_succ, sum, back);
        let with_lt = d.lam_fv(hlt_fv, hlt_ty, body);
        d.lam_fv(k_fv, nat, with_lt)
    };

    // c2 : countRange shifted m = 0.
    let count_middle = d.lemma(p.count_range_eq_zero_of_all_false, &[shifted, m, hall]);

    // countRange f (succ m) = 1 + 0, via the split at 1.
    let count_at_sm = {
        let split = d.lemma(p.count_range_split, &[f, one, m]);
        let left = d.const_app(p.count_range, &[f, one]);
        let right = d.const_app(p.count_range, &[shifted, m]);
        let sum_expr = d.add(left, right);
        let stuck = d.add(one, m);
        let at_stuck = d.const_app(p.count_range, &[f, stuck]);

        let after_left = d.congr(left, one, count_at_one, &|d, x| {
            let right = d.const_app(p.count_range, &[shifted, m]);
            d.add(x, right)
        });
        let mid = {
            let right = d.const_app(p.count_range, &[shifted, m]);
            d.add(one, right)
        };
        let after_right = d.congr(right, zero, count_middle, &|d, x| d.add(one, x));
        let target = d.add(one, zero);
        let chained = d.trans(sum_expr, mid, target, after_left, after_right);
        let full = d.trans(at_stuck, sum_expr, target, split, chained);

        // Move the bound from the stuck `add 1 m` to `succ m`.
        let unstick = one_add_eq_succ(d, &p, m);
        let motive = d.eq_motive(stuck, &|d, x| {
            let lhs = d.const_app(p.count_range, &[f, x]);
            let one = d.num(1);
            let zero = d.zero();
            let rhs = d.add(one, zero);
            d.eq(lhs, rhs)
        });
        d.transport(stuck, motive, full, sm, unstick)
    };

    // countRange f n = succ (countRange f (succ m)) = succ (1 + 0) ≡ 2.
    let count_total = {
        let peel = d.lemma(p.count_range_succ_of_true, &[f, sm, hlast]);
        let inner = d.const_app(p.count_range, &[f, sm]);
        let target = d.add(one, zero);
        let lifted = d.congr(inner, target, count_at_sm, &|d, x| d.succ(x));
        let at_n = d.const_app(p.count_range, &[f, n]);
        let inner_succ = d.succ(inner);
        let target_succ = d.succ(target);
        d.trans(at_n, inner_succ, target_succ, peel, lifted)
    };

    let at_n = d.const_app(p.count_range, &[f, n]);
    let two = d.num(2);
    d.lemma(p.beq_eq_true_of_eq, &[at_n, two, count_total])
}

/// `Nat.isPrime_eq_true_of_prime : ∀ n, prime_condition n →
/// Eq Bool (isPrime n) true` — the keystone of the whole shelf.
///
/// `prime_counting.rs` declares `Nat.isPrime` with NO theorem about it
/// (ADR-0653), so before this nothing in the kernel connected the `Bool`
/// predicate `primeCounting'` actually counts to this prelude's propositional
/// `prime_condition`. Every statement about `primeCounting'` beyond
/// monotonicity needs it, because monotonicity is the only kind of fact that
/// holds of `countRange` at an ARBITRARY predicate.
///
/// The general form is reached from `is_prime_true_at_double_succ` by writing
/// `n` as `succ (succ (pred (pred n)))`: `Nat.Prime.pred_pos` gives
/// `0 < pred n`, `succ_pred_of_pos` turns that into `pred n = succ (pred (pred
/// n))`, and `Nat.succ_pred_prime` gives `succ (pred n) = n`. Both the
/// hypothesis and the conclusion are then transported along that one equation.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_prime_bridge(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let h_ty = prime_condition(d, &p, n);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // n = succ (succ m), with m := pred (pred n).
    let q = d.const_app(p.pred, &[n]);
    let m = d.const_app(p.pred, &[q]);
    let sm = d.succ(m);
    let sq = d.succ(q);
    let double = d.succ(sm);

    let hq_pos = d.lemma(p.prime_pred_pos, &[n, h]);
    let eq_q = d.lemma(p.succ_pred_of_pos, &[q, hq_pos]);
    let lifted = d.congr(q, sm, eq_q, &|d, x| d.succ(x));
    let back = d.symm(sq, double, lifted);
    let eq_p = d.lemma(p.succ_pred_prime, &[n, h]);
    let hn = d.trans(double, sq, n, back, eq_p);

    // Transport the hypothesis to the double-successor shape.
    let hprime = {
        let reverse = d.symm(double, n, hn);
        let motive = d.eq_motive(n, &|d, x| prime_condition(d, &p, x));
        d.transport(n, motive, h, double, reverse)
    };

    let base = is_prime_true_at_double_succ(d, &p, m, hprime);
    let motive = d.eq_motive(double, &|d, x| {
        let lhs = d.const_app(p.is_prime, &[x]);
        let true_value = d.bool_true();
        d.bool_eq(lhs, true_value)
    });
    let proof = d.transport(double, motive, base, n, hn);

    let concl = {
        let lhs = d.const_app(p.is_prime, &[n]);
        let true_value = d.bool_true();
        d.bool_eq(lhs, true_value)
    };
    let ty = {
        let inner = d.arrow(h_ty, concl);
        d.pi_fv(n_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(h_fv, h_ty, proof);
        d.lam_fv(n_fv, nat, inner)
    };
    d.declare_theorem(p.is_prime_eq_true_of_prime, ty, value)
}

/// `Nat.primeCounting'_unbounded : ∀ k, ∃ n, Le k (primeCounting' n)` —
/// Euclid's theorem in COUNTING form.
///
/// `Nat.exists_prime_gt` already says the primes are unbounded as a set. This
/// says the prime-COUNTING function is unbounded as a function, which is the
/// form every Chebyshev-style estimate is compared against, and it is the
/// first statement about `Nat.primeCounting'` that is not true of
/// `Nat.countRange` at an arbitrary predicate.
///
/// Induction on `k`. The base takes the witness `0` and `zero_le`. The step
/// eliminates the hypothesis' witness `n`, takes a prime `p > n` from
/// `exists_prime_gt`, and uses the witness `succ p`:
///
/// ```text
/// primeCounting' (succ p) = succ (primeCounting' p)   -- isPrime p = true
///                         ≥ succ (primeCounting' n)   -- monotone, n ≤ p
///                         ≥ succ k
/// ```
///
/// The first line is where the bridge is spent: `countRange_succ_of_true`
/// needs `Eq Bool (isPrime p) true`, and `exists_prime_gt` hands back
/// `prime_condition p`. Without `isPrime_eq_true_of_prime` the two do not
/// meet, and this theorem is not provable from anything else in the prelude.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_counting_unbounded(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let level_one = d.level_one();

    // `fun n => Le bound (primeCounting' n)`, the existential's predicate.
    let goal_pred = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let count = d.const_app(p.prime_counting_prime, &[n]);
        let body = d.le(bound, count);
        d.lam_fv(n_fv, nat, body)
    };
    let goal_at = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
        let predicate = goal_pred(d, bound);
        let level_one = d.level_one();
        let exists_ = d.kernel().const_(p.logic.exists_, vec![level_one]);
        d.apply(exists_, &[nat, predicate])
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let proof = d.induct(
        &|d, x| goal_at(d, x),
        &|d| {
            let zero = d.zero();
            let predicate = goal_pred(d, zero);
            let count = d.const_app(p.prime_counting_prime, &[zero]);
            let witness = d.lemma(p.zero_le, &[count]);
            let nat = d.nat_ty();
            let level_one = d.level_one();
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            d.apply(intro, &[nat, predicate, zero, witness])
        },
        &|d, j, ih| {
            let nat = d.nat_ty();
            let level_one = d.level_one();
            let sj = d.succ(j);
            let goal = goal_at(d, sj);
            let inner_pred = goal_pred(d, j);

            // fun n (hn : Le j (primeCounting' n)) => ...
            let minor = {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let count_n = d.const_app(p.prime_counting_prime, &[n]);
                let hn_ty = d.le(j, count_n);
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);

                // The prime above `n`, and its two projections.
                let prime_pred = {
                    let q_fv = d.fresh_fvar();
                    let q = d.kernel().fvar(q_fv);
                    let lt = d.lt(n, q);
                    let prime = prime_condition(d, &p, q);
                    let body = d.const_app(p.logic.and, &[lt, prime]);
                    d.lam_fv(q_fv, nat, body)
                };
                let euclid = d.lemma(p.exists_prime_gt, &[n]);

                let prime_minor = {
                    let q_fv = d.fresh_fvar();
                    let q = d.kernel().fvar(q_fv);
                    let lt_ty = d.lt(n, q);
                    let prime_ty = prime_condition(d, &p, q);
                    let hq_ty = d.const_app(p.logic.and, &[lt_ty, prime_ty]);
                    let hq_fv = d.fresh_fvar();
                    let hq = d.kernel().fvar(hq_fv);

                    let hlt = and_left(d, lt_ty, prime_ty, hq);
                    let hprime = and_right(d, lt_ty, prime_ty, hq);

                    // isPrime q = true, and the resulting count step.
                    let bridge = d.lemma(p.is_prime_eq_true_of_prime, &[q, hprime]);
                    let is_prime = d.const_app(p.is_prime, &[]);
                    let sq = d.succ(q);
                    let peel = d.lemma(p.count_range_succ_of_true, &[is_prime, q, bridge]);

                    // n ≤ q, so the count at n is at most the count at q.
                    let sn = d.succ(n);
                    let step = d.lemma(p.le_succ, &[n]);
                    let hnq = d.lemma(p.le_trans, &[n, sn, q, step, hlt]);
                    let mono = d.lemma(p.count_range_le_of_le, &[is_prime, n, q, hnq]);

                    let count_n = d.const_app(p.count_range, &[is_prime, n]);
                    let count_q = d.const_app(p.count_range, &[is_prime, q]);
                    let chained = d.lemma(p.le_trans, &[j, count_n, count_q, hn, mono]);
                    let lifted = d.lemma(p.succ_le_succ, &[j, count_q, chained]);

                    // Move `succ (count q)` to `count (succ q)`.
                    let count_sq = d.const_app(p.count_range, &[is_prime, sq]);
                    let succ_count_q = d.succ(count_q);
                    let back = d.symm(count_sq, succ_count_q, peel);
                    let motive = d.eq_motive(succ_count_q, &|d, x| d.le(sj, x));
                    let shifted = d.transport(succ_count_q, motive, lifted, count_sq, back);

                    let predicate = goal_pred(d, sj);
                    let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
                    let body = d.apply(intro, &[nat, predicate, sq, shifted]);
                    let with_hq = d.lam_fv(hq_fv, hq_ty, body);
                    d.lam_fv(q_fv, nat, with_hq)
                };

                let anon = d.anon_name();
                let exists_ = d.kernel().const_(p.logic.exists_, vec![level_one]);
                let prime_exists = d.apply(exists_, &[nat, prime_pred]);
                let prime_motive = d
                    .kernel()
                    .lam(anon, prime_exists, goal, BinderInfo::Default);
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, prime_pred, prime_motive, prime_minor, euclid],
                );
                let with_hn = d.lam_fv(hn_fv, hn_ty, body);
                d.lam_fv(n_fv, nat, with_hn)
            };

            let anon = d.anon_name();
            let exists_ = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let inner_exists = d.apply(exists_, &[nat, inner_pred]);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, goal, BinderInfo::Default);
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
            d.apply(exists_rec, &[nat, inner_pred, inner_motive, minor, ih])
        },
        k,
    );

    let concl = goal_at(d, k);
    let ty = d.pi_fv(k_fv, nat, concl);
    let value = d.lam_fv(k_fv, nat, proof);
    let _ = level_one;
    d.declare_theorem(p.prime_counting_prime_unbounded, ty, value)
}
