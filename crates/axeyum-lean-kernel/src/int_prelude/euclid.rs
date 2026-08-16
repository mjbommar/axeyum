//! Euclidean decomposition over `ℤ`, built from the proved `ℕ` division
//! development.
//!
//! `Int.euclidean_decomposition` — `0 < k → ∃ q r, t = k·q + r ∧ 0 ≤ r ∧ r < k`
//! — is the last member of [`super`] that is still an axiom, and the only one
//! that is not a ring or order law: it asserts an *existence*, so no rewriting
//! lemma discharges it.
//!
//! This module builds it branch by branch. The non-negative branch is here; the
//! `negSucc` branch is where the real work is, because Euclidean rounding is not
//! truncation.
//!
//! ## Why no `Int.div` is needed
//!
//! The axiom is purely existential, so it is discharged by *supplying
//! witnesses*. Defining `Int.div`/`Int.mod` is a sufficient route, not a
//! necessary one, and the witnesses come straight from `Nat.divMod`.
//!
//! ## What is definitional here, and what is not
//!
//! `Int.add` and `Int.mul` are structural definitions that **compute on two
//! `ofNat` constructors** (which is why `Int.add_zero` is proved by `irefl` and
//! nothing else), and `Int.le`/`Int.lt` are four-case definitions over
//! `Nat.le`/`Nat.lt` with `Int.le (ofNat m) (ofNat n) ≡ Nat.le m n`. So on the
//! non-negative branch every transfer step below is a definitional equality the
//! kernel discharges itself, and the only propositional content is the `ℕ`
//! equation. `Nat.divMod d n q r` is likewise a *definition*, unfolding to
//! `(n = d·q + r) ∧ (r < d)`, so `And.left`/`And.right` apply to it directly.

use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::{IntDev, Shape, case_split, exists_elim};
use super::statements;

/// `Exists.{1} Int predicate`.
fn int_exists(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let exists = d.kernel().const_(name, vec![one]);
    d.apply(exists, &[int_ty, predicate])
}

/// `Exists.intro.{1} Int predicate witness proof`.
fn int_exists_intro(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(name, vec![one]);
    d.apply(intro, &[int_ty, predicate, witness, proof])
}

/// The inner predicate `fun (r : Int) => t = k·q + r ∧ (0 ≤ r ∧ r < k)`.
fn remainder_predicate(d: &mut IntDev<'_>, t: ExprId, k: ExprId, q: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let product = d.imul(k, q);
    let sum = d.iadd(product, r);
    let equation = d.ieq(t, sum);
    let zero = d.izero();
    let lower = d.ile(zero, r);
    let upper = d.ilt(r, k);
    let bounds = d.and(lower, upper);
    let facts = d.and(equation, bounds);
    d.lam_fv(r_fv, int_ty, facts)
}

/// The outer predicate `fun (q : Int) => ∃ r, …`.
fn quotient_predicate(d: &mut IntDev<'_>, t: ExprId, k: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let inner = remainder_predicate(d, t, k, q);
    let body = int_exists(d, inner);
    d.lam_fv(q_fv, int_ty, body)
}

/// `∃ q r : Int, t = k·q + r ∧ 0 ≤ r ∧ r < k`, the conclusion shared by every
/// branch.
pub(super) fn decomposition_goal(d: &mut IntDev<'_>, t: ExprId, k: ExprId) -> ExprId {
    let predicate = quotient_predicate(d, t, k);
    int_exists(d, predicate)
}

/// Supply `(q, r)` as the witnesses for [`decomposition_goal`], given a proof of
/// the conjunction they satisfy.
fn intro_pair(
    d: &mut IntDev<'_>,
    t: ExprId,
    k: ExprId,
    q: ExprId,
    r: ExprId,
    facts: ExprId,
) -> ExprId {
    let inner = remainder_predicate(d, t, k, q);
    let inner_proof = int_exists_intro(d, inner, r, facts);
    let outer = quotient_predicate(d, t, k);
    int_exists_intro(d, outer, q, inner_proof)
}

/// `Int.euclid_of_nat : ∀ (n m : Nat), ∃ q r, ofNat n = ofNat (succ m)·q + r ∧
/// 0 ≤ r ∧ r < ofNat (succ m)`.
///
/// The non-negative branch of the decomposition, stated over `ℕ` parameters so
/// that the divisor is positive *by construction* (`succ m`) rather than by a
/// hypothesis the caller must discharge again.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_of_nat_branch(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let divisor = d.succ(m);
    let t = d.of_nat(n);
    let k = d.of_nat(divisor);
    let goal = decomposition_goal(d, t, k);

    // 1 ≤ succ m, from `zero_le m` through `le_succ_succ`.
    let one_le_divisor = {
        let zero = d.zero();
        let base = d.const_app(p.nat.zero_le, &[m]);
        d.const_app(p.nat.le_succ_succ, &[zero, m, base])
    };

    // Nat.div_mod_exists : ∀ d n, 1 ≤ d → ∃ q r, divMod d n q r.
    let witness = d.const_app(p.nat.div_mod_exists, &[divisor, n, one_le_divisor]);

    // The two nested `Exists Nat` predicates the witness inhabits.
    let inner_predicate = |d: &mut IntDev<'_>, a: ExprId| {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = d.div_mod(divisor, n, a, b);
        d.lam_fv(b_fv, nat, body)
    };
    let outer_predicate = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let body = inner_predicate(d, a);
        let inner = {
            let one = d.level_one();
            let name = d.int().logic.exists_;
            let exists = d.kernel().const_(name, vec![one]);
            d.apply(exists, &[nat, body])
        };
        d.lam_fv(a_fv, nat, inner)
    };

    // fun a (ha : ∃ b, divMod (succ m) n a b) => …
    let minor = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let predicate = inner_predicate(d, a);

        // fun b (hb : divMod (succ m) n a b) => …
        let inner_minor = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let relation = d.div_mod(divisor, n, a, b);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);

            // `hb` is definitionally `(n = divisor·a + b) ∧ (b < divisor)`.
            let product = NatOps::mul(d, divisor, a);
            let reconstructed = NatOps::add(d, product, b);
            let equation = d.eq(n, reconstructed);
            let bound = NatOps::lt(d, b, divisor);
            let heq = d.and_left(equation, bound, hb);
            let hlt = d.and_right(equation, bound, hb);

            // ofNat n = ofNat (divisor·a + b), and the goal's right-hand side
            // `ofNat divisor · ofNat a + ofNat b` reduces to exactly that.
            let lifted = d.nat_eq_to_int(n, reconstructed, heq, &|d, x| d.of_nat(x));

            // 0 ≤ ofNat b reduces to Nat.le zero b.
            let nonneg = d.const_app(p.nat.zero_le, &[b]);

            let q = d.of_nat(a);
            let r = d.of_nat(b);
            let zero = d.izero();
            let lower_ty = d.ile(zero, r);
            let upper_ty = d.ilt(r, k);
            let bounds = d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, nonneg, hlt]);

            let product_int = d.imul(k, q);
            let sum_int = d.iadd(product_int, r);
            let equation_ty = d.ieq(t, sum_int);
            let bounds_ty = d.and(lower_ty, upper_ty);
            let facts = d.const_app(p.logic.and_intro, &[equation_ty, bounds_ty, lifted, bounds]);

            let body = intro_pair(d, t, k, q, r, facts);
            let with_h = d.lam_fv(hb_fv, relation, body);
            d.lam_fv(b_fv, nat, with_h)
        };

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let ha_ty = {
            let one = d.level_one();
            let name = d.int().logic.exists_;
            let exists = d.kernel().const_(name, vec![one]);
            d.apply(exists, &[nat, predicate])
        };
        let eliminated = exists_elim(d, predicate, goal, ha, inner_minor);
        let with_h = d.lam_fv(ha_fv, ha_ty, eliminated);
        d.lam_fv(a_fv, nat, with_h)
    };

    let value = exists_elim(d, outer_predicate, goal, witness, minor);

    let ty = {
        let with_m = d.pi_fv(m_fv, nat, goal);
        d.pi_fv(n_fv, nat, with_m)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, value);
        d.lam_fv(n_fv, nat, with_m)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euclid_of_nat,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `Int.euclid_neg_succ : ∀ (n m : Nat), ∃ q r, negSucc n = ofNat (succ m)·q + r
/// ∧ 0 ≤ r ∧ r < ofNat (succ m)`.
///
/// The negative branch, and the one with real content: Euclidean rounding is not
/// truncation, so the quotient is *not* the negation of the `ℕ` quotient.
///
/// With `K = succ m` and `Nat.divMod K n a b`, the witnesses are uniformly
///
/// ```text
/// q = negSucc a          r = ofNat (K - succ b)
/// ```
///
/// and the `succ b = K` case needs no separate treatment: truncated subtraction
/// makes `r` collapse to `0` on its own. Checked numerically before it was
/// built — `K=3, n=4` gives `-5 = 3·(-2) + 1`, and `K=3, n=2` gives
/// `-3 = 3·(-1) + 0`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_neg_succ_branch(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let divisor = d.succ(m);
    let t = d.neg_succ(n);
    let k = d.of_nat(divisor);
    let goal = decomposition_goal(d, t, k);

    let one_le_divisor = {
        let zero = d.zero();
        let base = d.const_app(p.nat.zero_le, &[m]);
        d.const_app(p.nat.le_succ_succ, &[zero, m, base])
    };
    let witness = d.const_app(p.nat.div_mod_exists, &[divisor, n, one_le_divisor]);

    let inner_predicate = |d: &mut IntDev<'_>, a: ExprId| {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = d.div_mod(divisor, n, a, b);
        d.lam_fv(b_fv, nat, body)
    };
    let exists_nat = |d: &mut IntDev<'_>, predicate: ExprId| {
        let one = d.level_one();
        let name = d.int().logic.exists_;
        let exists = d.kernel().const_(name, vec![one]);
        d.apply(exists, &[nat, predicate])
    };
    let outer_predicate = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let body = inner_predicate(d, a);
        let inner = exists_nat(d, body);
        d.lam_fv(a_fv, nat, inner)
    };

    let minor = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let predicate = inner_predicate(d, a);

        let inner_minor = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let relation = d.div_mod(divisor, n, a, b);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);

            let product = NatOps::mul(d, divisor, a);
            let reconstructed = NatOps::add(d, product, b);
            let equation = d.eq(n, reconstructed);
            let bound = NatOps::lt(d, b, divisor);
            let heq = d.and_left(equation, bound, hb);
            // `Nat.lt b K` is *defined* as `Nat.le (succ b) K`, which is exactly
            // what `sub_add_cancel` consumes — no conversion lemma needed.
            let hlt = d.and_right(equation, bound, hb);

            let succ_b = d.succ(b);
            let rem = NatOps::sub(d, divisor, succ_b);
            let q = d.neg_succ(a);
            let r = d.of_nat(rem);

            // ---- `divisor · succ a = rem + succ n`, in ℕ ---------------------
            let succ_n = d.succ(n);
            let start = NatOps::add(d, rem, succ_n);
            let succ_reconstructed = d.succ(reconstructed);
            let s1_to = NatOps::add(d, rem, succ_reconstructed);
            let s1 = d.congr(n, reconstructed, heq, &|d, x| {
                let sx = d.succ(x);
                NatOps::add(d, rem, sx)
            });

            let product_succ_b = NatOps::add(d, product, succ_b);
            let s2_to = NatOps::add(d, rem, product_succ_b);
            let s2 = {
                let add_succ = d.const_app(p.nat.add_succ, &[product, b]);
                let flipped = d.symm(product_succ_b, succ_reconstructed, add_succ);
                d.congr(succ_reconstructed, product_succ_b, flipped, &|d, x| {
                    NatOps::add(d, rem, x)
                })
            };

            let succ_b_product = NatOps::add(d, succ_b, product);
            let s3_to = NatOps::add(d, rem, succ_b_product);
            let s3 = {
                let commute = d.const_app(p.nat.add_comm, &[product, succ_b]);
                d.congr(product_succ_b, succ_b_product, commute, &|d, x| {
                    NatOps::add(d, rem, x)
                })
            };

            let rem_succ_b = NatOps::add(d, rem, succ_b);
            let s4_to = NatOps::add(d, rem_succ_b, product);
            let s4 = {
                let assoc = d.const_app(p.nat.add_assoc, &[rem, succ_b, product]);
                d.symm(s4_to, s3_to, assoc)
            };

            let divisor_product = NatOps::add(d, divisor, product);
            let s5 = {
                let cancel = d.const_app(p.nat.sub_add_cancel, &[succ_b, divisor, hlt]);
                d.congr(rem_succ_b, divisor, cancel, &|d, x| {
                    NatOps::add(d, x, product)
                })
            };

            let product_divisor = NatOps::add(d, product, divisor);
            let s6 = d.const_app(p.nat.add_comm, &[divisor, product]);

            let succ_a = d.succ(a);
            let divisor_succ_a = NatOps::mul(d, divisor, succ_a);
            let s7 = {
                let mul_succ = d.const_app(p.nat.mul_succ, &[divisor, a]);
                d.symm(product_divisor, divisor_succ_a, mul_succ)
            };

            let (_end, forward) = d.chain(
                start,
                &[
                    (s1_to, s1),
                    (s2_to, s2),
                    (s3_to, s3),
                    (s4_to, s4),
                    (divisor_product, s5),
                    (product_divisor, s6),
                    (divisor_succ_a, s7),
                ],
            );
            // `divisor · succ a = rem + succ n`, the direction the rewrite wants.
            let scaled_eq = d.symm(start, divisor_succ_a, forward);

            // ---- the ℤ equation ---------------------------------------------
            // `ofNat K · negSucc a` reduces to `negOfNat (K · succ a)`, so the
            // goal's right-hand side is already `negOfNat (…) + ofNat rem`.
            let negated = d.neg_of_nat(divisor_succ_a);
            let rhs = d.iadd(negated, r);
            let sub_form = d.sub_nat_nat(rem, divisor_succ_a);
            let e1 = d.const_app(p.neg_of_nat_add_of_nat, &[divisor_succ_a, rem]);

            let shifted = NatOps::add(d, rem, succ_n);
            let sub_shifted = d.sub_nat_nat(rem, shifted);
            let e2 = d.nat_eq_to_int(divisor_succ_a, shifted, scaled_eq, &|d, x| {
                d.sub_nat_nat(rem, x)
            });

            let neg_succ_n = d.neg_of_nat(succ_n);
            let e3 = d.const_app(p.sub_nat_nat_add_right, &[rem, succ_n]);

            let (_stop, chain_proof) =
                d.ichain(rhs, &[(sub_form, e1), (sub_shifted, e2), (neg_succ_n, e3)]);
            // `negOfNat (succ n)` *is* `negSucc n`, definitionally.
            let lifted = d.isymm(rhs, t, chain_proof);

            // ---- the two bounds ---------------------------------------------
            let nonneg = d.const_app(p.nat.zero_le, &[rem]);
            let upper = {
                let zero = d.zero();
                let zero_lt_succ_b = {
                    let base = d.const_app(p.nat.zero_le, &[b]);
                    d.const_app(p.nat.le_succ_succ, &[zero, b, base])
                };
                let raw = d.const_app(p.nat.add_lt_add_left, &[rem, zero, succ_b, zero_lt_succ_b]);
                let rem_zero = NatOps::add(d, rem, zero);
                let add_zero = d.const_app(p.nat.add_zero, &[rem]);
                let left_fixed = d.nat_rewrite(rem_zero, rem, add_zero, raw, &|d, x| {
                    let target = NatOps::add(d, rem, succ_b);
                    NatOps::lt(d, x, target)
                });
                let cancel = d.const_app(p.nat.sub_add_cancel, &[succ_b, divisor, hlt]);
                d.nat_rewrite(rem_succ_b, divisor, cancel, left_fixed, &|d, x| {
                    NatOps::lt(d, rem, x)
                })
            };

            let zero_int = d.izero();
            let lower_ty = d.ile(zero_int, r);
            let upper_ty = d.ilt(r, k);
            let bounds = d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, nonneg, upper]);

            let product_int = d.imul(k, q);
            let sum_int = d.iadd(product_int, r);
            let equation_ty = d.ieq(t, sum_int);
            let bounds_ty = d.and(lower_ty, upper_ty);
            let facts = d.const_app(p.logic.and_intro, &[equation_ty, bounds_ty, lifted, bounds]);

            let body = intro_pair(d, t, k, q, r, facts);
            let with_h = d.lam_fv(hb_fv, relation, body);
            d.lam_fv(b_fv, nat, with_h)
        };

        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let ha_ty = exists_nat(d, predicate);
        let eliminated = exists_elim(d, predicate, goal, ha, inner_minor);
        let with_h = d.lam_fv(ha_fv, ha_ty, eliminated);
        d.lam_fv(a_fv, nat, with_h)
    };

    let value = exists_elim(d, outer_predicate, goal, witness, minor);

    let ty = {
        let with_m = d.pi_fv(m_fv, nat, goal);
        d.pi_fv(n_fv, nat, with_m)
    };
    let value = {
        let with_m = d.lam_fv(m_fv, nat, value);
        d.lam_fv(n_fv, nat, with_m)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euclid_neg_succ,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `Int.euclidean_decomposition : ∀ t k, 0 < k → ∃ q r, t = k·q + r ∧ 0 ≤ r ∧
/// r < k` — **a theorem**, composed from the two branches above.
///
/// This is the last member of the integer prelude that was an assumption. The
/// composition is short because both halves of the case analysis are already
/// proved:
///
/// - `Int.lt_dest` turns `0 < k` into `∃ i, k = 0 + ofNat (succ i)`, and
///   `Nat.zero_add` normalises that to `k = ofNat (succ i)` — so the divisor is
///   a *positive* `ofNat`, which is the shape both branch lemmas take.
/// - `Int.rec` on `t` selects [`declare_of_nat_branch`] or
///   [`declare_neg_succ_branch`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_decomposition(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    d.int_theorem(p.euclidean_decomposition, 2, &|d, v| {
        let (t, k) = (v[0], v[1]);
        let stmt = statements::euclidean_decomposition(d, v);
        let zero = d.izero();
        let pos_ty = d.ilt(zero, k);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let goal = decomposition_goal(d, t, k);

        // `Int.lt_dest 0 k h : ∃ i, k = 0 + ofNat (succ i)`.
        let dest = d.const_app(p.lt_dest, &[zero, k, h]);
        let shift_body = |d: &mut IntDev<'_>, i: ExprId| {
            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);
            d.ieq(k, shifted)
        };
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = shift_body(d, i);
            d.lam_fv(i_fv, nat, body)
        };

        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_ty = shift_body(d, i);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);

            let si = d.succ(i);
            let value = d.of_nat(si);
            let shifted = d.iadd(zero, value);

            // `0 + ofNat (succ i)` is `ofNat (0 + succ i)`; `Nat.zero_add`
            // finishes the normalisation the reduction cannot do on its own,
            // because `Nat.add` recurses on its SECOND argument.
            let nat_zero = d.zero();
            let sum_nat = NatOps::add(d, nat_zero, si);
            let zero_add = d.const_app(p.nat.zero_add, &[si]);
            let normalise = d.nat_eq_to_int(sum_nat, si, zero_add, &|d, x| d.of_nat(x));
            let k_eq = d.itrans(k, shifted, value, hi, normalise);

            // With the divisor in `ofNat (succ i)` form, `Int.rec` on `t`
            // selects one of the two proved branches.
            let branch = case_split(
                d,
                &[t],
                &|d, args| decomposition_goal(d, args[0], value),
                &|d, b| {
                    let magnitude = b[0].1;
                    match b[0].0 {
                        Shape::OfNat => d.const_app(p.euclid_of_nat, &[magnitude, i]),
                        Shape::NegSucc => d.const_app(p.euclid_neg_succ, &[magnitude, i]),
                    }
                },
            );

            let back = d.isymm(k, value, k_eq);
            let transported =
                d.int_eq_rewrite(value, k, back, branch, &|d, x| decomposition_goal(d, t, x));
            let with_h = d.lam_fv(hi_fv, hi_ty, transported);
            d.lam_fv(i_fv, nat, with_h)
        };

        let body = exists_elim(d, predicate, goal, dest, minor);
        let proof = d.lam_fv(h_fv, pos_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}
