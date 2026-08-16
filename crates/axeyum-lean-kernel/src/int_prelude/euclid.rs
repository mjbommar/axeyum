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

use super::ops::{IntDev, exists_elim};

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
