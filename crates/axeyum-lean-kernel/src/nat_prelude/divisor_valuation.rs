//! A divisor's valuation is bounded by the multiset's — ADR-1658's missing
//! piece A, the surjectivity half of the divisors ↔ selections bijection
//! (roadmap W2-18, ADR-1671).
//!
//! # What was missing, exactly
//!
//! `Nat.Multiset.prodSel_dvd_prod` (ADR-1658) is the easy direction: every
//! selection of a multiset names a divisor of its product. The converse — every
//! divisor of `prod m` IS a selection — needs, before anything else, that a
//! divisor cannot carry more copies of a prime than the multiset does:
//!
//! ```text
//! Nat.Multiset.count_le_of_dvd_prod :
//!   (∀ x, 0 < count m x → prime x) → 0 < d → dvd d (prod m) →
//!   Le (count (factorization d) q) (count m q)
//! ```
//!
//! ADR-1658 sized this as "a real but bounded induction, mostly in
//! `multiset.rs`'s idiom". It is neither an induction nor in `multiset.rs`'s
//! idiom: both valuation halves already exist
//! (`Nat.Multiset.pow_count_dvd_prod` and
//! `Nat.Multiset.not_pow_succ_count_dvd_prod`), so the whole argument is one
//! trichotomy and a chain of three `dvd_trans`es.
//!
//! Suppose `count m q < count (factorization d) q`. Then
//! `q ^ (count m q + 1)` divides `q ^ count (factorization d) q`, which divides
//! `prod (factorization d) = d` (`Nat.prod_factorization`), which divides
//! `prod m`. And `not_pow_succ_count_dvd_prod` says it does not. The one thing
//! that has to be arranged is `q`'s primality, and it comes for free in exactly
//! the branch that needs it: `count m q < count (factorization d) q` forces
//! `0 < count (factorization d) q`, which is `Nat.factorization_prime`'s
//! hypothesis. In the other branch there is nothing to prove.
//!
//! **`Nat.lt n m` IS `Nat.le (succ n) m` definitionally here**, so the step
//! from "strictly greater" to "at least one more copy" costs nothing — no
//! `succ_le_of_lt` is needed and none exists.
//!
//! # `Nat.pow_dvd_pow_of_le` already existed, under a name I would not have
//! chosen
//!
//! The step "one more copy of `q` still divides `q ^ cd`" was budgeted as new
//! work and written in full — an induction on the upper exponent with the lower
//! one quantified inside the motive — before a field-name grep for
//! `pow_dvd_pow` turned up **`Nat.pow_dvd_pow_of_le`**
//! (`multiset.rs`, `∀ a i j, Le i j → dvd (pow a i) (pow a j)`, proved through
//! `le_dest` + `pow_add`). It is used twice in `multiset.rs` itself, two files
//! away from this one. The duplicate was deleted unlanded; this is hiding
//! place 4 of `finding-existing-lemmas.md` — there is no single spelling, and a
//! grep for the name you would have given it is not a search.
//!
//! # What this does NOT close
//!
//! Surjectivity itself is one theorem further on, and it is blocked on a
//! different missing primitive rather than on this one. With
//! `s q := ble 1 (count (factorization d) q)` and a squarefree `m` (every
//! `count m q ≤ 1`), this theorem gives
//! `count (restrict m s) q = count (factorization d) q` at every `q` — the two
//! multisets agree pointwise. Concluding `prodSel m s = d` from that needs
//! `count`-agreement to imply `prod`-agreement, and the multiset carrier
//! deliberately has no extensionality (ADR-1520): the two multisets have
//! DIFFERENT BOUNDS, so their `prodRange` folds run over different ranges and
//! `Nat.Multiset.count_eq_of_prod_eq` runs the other way. The missing lemma is
//! a range-stability law — `(∀ i, Le a i → f i = 1) → Le a b →
//! prodRange f b = prodRange f a` — and then
//! `Nat.Multiset.prod_eq_of_count_eq` on top of it. Neither exists;
//! `Nat.prodRange_eq_one_of_below` (`factorization_multiset.rs`) is the
//! collapse law, not the stability law.
//!
//! # House rules observed here
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call).

use super::NatPrelude;
use super::multiset::{ms_count, ms_prod};
use super::ops::NatDev;
use super::ops::NatOps;
use super::primes::prime_condition;
use super::steps::absurd;
use crate::KernelError;
use crate::expr::{BinderInfo, ExprId};
use crate::name::NameId;

/// `Or.rec` at a `Prop` goal — a private copy of the wrapper
/// `arith_functions.rs` and `subset_search.rs` each keep.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `∀ binders, stmt`, proved by `proof`.
fn declare_forall(
    d: &mut NatDev<'_>,
    name: NameId,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, binder_ty) in binders.iter().rev() {
        ty = d.pi_fv(fv, binder_ty, ty);
        value = d.lam_fv(fv, binder_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

/// `Nat.factorization d`.
fn factorization(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    d.const_app(p.factorization, &[n])
}

// ---------------------------------------------------------------------------
// `Nat.Multiset.count_le_of_dvd_prod`.
// ---------------------------------------------------------------------------

/// `Nat.Multiset.count_le_of_dvd_prod : ∀ m d q,
/// (∀ x, Lt 0 (count m x) → prime x) → Lt 0 d → dvd d (prod m) →
/// Le (count (factorization d) q) (count m q)`.
///
/// ADR-1658's missing piece A. The trichotomy is `Nat.lt_or_ge` at the two
/// counts: its right half IS the goal, and its left half contradicts
/// `Nat.Multiset.not_pow_succ_count_dvd_prod`.
fn declare_count_le_of_dvd_prod(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    // `∀ x, Lt 0 (count m x) → prime x`.
    let prime_support_ty = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let c = ms_count(d, &p, m, x);
        let zero = d.zero();
        let pos = d.lt(zero, c);
        let concl = prime_condition(d, &p, x);
        let body = d.arrow(pos, concl);
        d.pi_fv(x_fv, nat, body)
    };
    let hprime_fv = d.fresh_fvar();
    let hprime = d.kernel().fvar(hprime_fv);

    let zero = d.zero();
    let pos_ty = d.lt(zero, n);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let prod_m = ms_prod(d, &p, m);
    let dvd_ty = d.dvd(n, prod_m);
    let hdvd_fv = d.fresh_fvar();
    let hdvd = d.kernel().fvar(hdvd_fv);

    let fact = factorization(d, &p, n);
    let cd = ms_count(d, &p, fact, q);
    let cm = ms_count(d, &p, m, q);
    let goal = d.le(cd, cm);

    let strict_ty = d.lt(cm, cd);
    let big_ty = d.le(cd, cm);
    let split = d.lemma(p.lt_or_ge, &[cm, cd]);

    // `cm < cd` is impossible: `q ^ (cm + 1)` would divide `prod m`.
    let on_strict = {
        let hs_fv = d.fresh_fvar();
        let hs = d.kernel().fvar(hs_fv);

        // `0 < cd`, hence `q` is prime.
        let low = d.lemma(p.zero_le, &[cm]);
        let z2 = d.zero();
        let cd_pos = d.lemma(p.lt_of_le_of_lt, &[z2, cm, cd, low, hs]);
        let q_prime = d.lemma(p.factorization_prime, &[n, q, cd_pos]);

        // `Nat.lt cm cd` IS `Le (succ cm) cd`, so `pow_dvd_pow` applies here.
        let scm = d.succ(cm);
        let small = d.pow(q, scm);
        let step_up = d.lemma(p.pow_dvd_pow_of_le, &[q, scm, cd, hs]);

        // `q ^ cd ∣ prod (factorization n) = n ∣ prod m`.
        let at_cd = d.pow(q, cd);
        let into_fact = d.lemma(p.multiset_pow_count_dvd_prod, &[fact, q]);
        let prod_fact = ms_prod(d, &p, fact);
        let unfolds = d.lemma(p.prod_factorization, &[n, hpos]);
        let into_n = {
            let motive = d.eq_motive(prod_fact, &|d, x| d.dvd(at_cd, x));
            d.transport(prod_fact, motive, into_fact, n, unfolds)
        };
        let into_prod = d.lemma(p.dvd_trans, &[at_cd, n, prod_m, into_n, hdvd]);
        let chained = d.lemma(p.dvd_trans, &[small, at_cd, prod_m, step_up, into_prod]);

        let refused = d.lemma(
            p.multiset_not_pow_succ_count_dvd_prod,
            &[m, q, q_prime, hprime],
        );
        let contradiction = d.apply(refused, &[chained]);
        let body = absurd(d, goal, contradiction);
        d.lam_fv(hs_fv, strict_ty, body)
    };
    let on_big = {
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        d.lam_fv(hb_fv, big_ty, hb)
    };

    let proof = or_elim(d, &p, strict_ty, big_ty, goal, on_strict, on_big, split);

    let ms_ty = d.kernel().const_(p.multiset, vec![]);
    declare_forall(
        d,
        p.multiset_count_le_of_dvd_prod,
        &[
            (m_fv, ms_ty),
            (n_fv, nat),
            (q_fv, nat),
            (hprime_fv, prime_support_ty),
            (hpos_fv, pos_ty),
            (hdvd_fv, dvd_ty),
        ],
        goal,
        proof,
    )
}

/// Declare the divisor-valuation bound.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection, naming the step that
/// failed — one rejected declaration fails the whole shared `build_nat_prelude`
/// and the raw `TypeMismatch` names neither.
pub(super) fn declare_divisor_valuation_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    type Step = fn(&mut NatDev<'_>, &NatPrelude) -> Result<(), KernelError>;
    let steps: [(&str, Step); 1] = [("count_le_of_dvd_prod", declare_count_le_of_dvd_prod)];
    for (label, step) in steps {
        if let Err(e) = step(d, p) {
            let rendered = d.explain(&e);
            eprintln!("divisor_valuation: step `{label}` was rejected:\n  {rendered}");
            return Err(e);
        }
    }
    Ok(())
}
