//! **Density of ℚ in ℝ** (ADR-0512 phase R6): `seq x n` is itself a rational
//! within `1/(n+1)` of `x`, in both directions, for every `n`.
//!
//! ## Why this needs no `CReal.add`
//!
//! The obvious statement — `CReal.le (CReal.abs (x − ofRat q)) (ofRat ε)` —
//! routes the difference through [`CReal.add`](super::CRealPrelude::add),
//! which samples at Bishop's shifted index `2n+1`, not `n`. That shift buys
//! nothing here and only complicates the estimate, so this module states
//! density directly as a **two-sided [`CReal.le`](super::CRealPrelude::le)
//! sandwich against two embedded rationals** —
//! `CReal.le x (ofRat (q + 1/(n+1)))` and `CReal.le (ofRat (q − 1/(n+1))) x`
//! — which never mentions `CReal.add`, `CReal.neg` or `CReal.abs` at all.
//! Both bounds are pointwise in `k` from the start.
//!
//! ## The estimate, in one line
//!
//! Fix `n` and let `q := seq x n`. Regularity at `(k, n)` gives
//! `Within (seq x k − q) (1/(k+1) + 1/(n+1))`, whose **upper** half is
//! `seq x k − q ≤ 1/(k+1) + 1/(n+1)`, i.e. `seq x k − (q + 1/(n+1)) ≤
//! 1/(k+1) ≤ 2/(k+1)` — exactly the body `CReal.le x (ofRat (q+1/(n+1)))`
//! asks for at index `k`, with room to spare (`1/(k+1)`, not `2/(k+1)`, is
//! the exact quantity produced). Regularity at `(n, k)` — the same fact with
//! the two indices swapped — gives the other direction by the mirror
//! argument. Nothing beyond `ℚ` associativity/commutativity and
//! `Rat.sub_le_of_le`/`Rat.le_of_sub_le` is needed; the Archimedean property
//! of `ℚ` is not consumed here (unlike `Equiv.trans`, `le_trans` and
//! `bound_within`), because both sides of every inequality are compared at
//! the *same* index `k` throughout.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::{CRealPrelude, and_intro, cle, creal_ty, div_succ, embed, halves, modulus, sample};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rsymm, rzero};

/// Admit `CReal.rat_approx_upper`, `CReal.rat_approx_lower` and
/// `CReal.density`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_density(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_rat_approx_upper(d, p)?;
    declare_rat_approx_lower(d, p)?;
    declare_density_theorem(d, p)
}

/// `bound2 : Rat.natDivSucc 1 k ≤ Rat.natDivSucc 2 k`, read as `bound2 ≤
/// bound2 + bound2` folded through `Rat.natDivSucc_add` — the same
/// pad-with-zero-then-fuse idiom [`super::archimedean`] uses to reach
/// `2/(k+1)` from a one-sided estimate.
fn widen_to_double(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let bound2 = div_succ(d, p, 1, k);
    let full_bound = div_succ(d, p, 2, k);
    let zero = rzero(d, rat);

    let nonneg_b = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, k]);
    let refl_b = d.lemma(rat.le_refl, &[bound2]);
    let widened = d.lemma(
        rat.add_le_add,
        &[bound2, bound2, zero, bound2, refl_b, nonneg_b],
    );
    let padded = radd(d, bound2, zero);
    let summed = radd(d, bound2, bound2);
    let trim = d.lemma(rat.add_zero, &[bound2]);
    let bound2_le_sum = rat_eq_rewrite(d, padded, bound2, trim, widened, &|d, t| {
        rle(d, rat, t, summed)
    });
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, k]);
    let bound2_le_full = rat_eq_rewrite(d, summed, full_bound, fuse, bound2_le_sum, &|d, t| {
        rle(d, rat, bound2, t)
    });
    (bound2, full_bound, bound2_le_full)
}

/// `CReal.rat_approx_upper : ∀ x n, CReal.le x (CReal.ofRat (Rat.add (CReal.seq
/// x n) (Rat.natDivSucc 1 n)))`.
///
/// Witness-free: the body is proved directly for the rational `seq x n +
/// 1/(n+1)`, with no existential to discharge.
fn declare_rat_approx_upper(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let q = sample(d, p, x, n);
    let one_n = div_succ(d, p, 1, n);
    let target = radd(d, q, one_n);
    let embedded_target = embed(d, p, target);

    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let point = sample(d, p, x, k);
        let diff = rsub(d, rat, point, q);
        let bound2 = div_succ(d, p, 1, k);
        let bound_kn = modulus(d, p, k, n);

        let regularity = d.lemma(p.regular, &[x, k, n]);
        let (_, upper) = halves(d, p, diff, bound_kn, regularity);

        // `point ≤ q + (bound2 + one_n)`.
        let h0 = d.lemma(rat.le_of_sub_le, &[point, q, bound_kn, upper]);
        let start = radd(d, q, bound_kn);

        // Rearrange the sum: `q + (bound2 + one_n) = (q + one_n) + bound2`.
        let mid_inner = radd(d, one_n, bound2);
        let swap_inner = d.lemma(rat.add_comm, &[bound2, one_n]);
        let mid = radd(d, q, mid_inner);
        let step1 = rcongr(d, bound_kn, mid_inner, swap_inner, &|d, t| radd(d, q, t));
        let target_plus_bound2 = radd(d, target, bound2);
        let assoc = d.lemma(rat.add_assoc, &[q, one_n, bound2]);
        let step2 = rsymm(d, target_plus_bound2, mid, assoc);
        let (_, chain_proof) = rchain(d, start, &[(mid, step1), (target_plus_bound2, step2)]);

        let h1 = rat_eq_rewrite(d, start, target_plus_bound2, chain_proof, h0, &|d, t| {
            rle(d, rat, point, t)
        });

        // `point − target ≤ bound2 ≤ 2/(k+1)`.
        let at_bound = d.lemma(rat.sub_le_of_le, &[point, target, bound2, h1]);
        let (bound2_again, full_bound, bound2_le_full) = widen_to_double(d, p, k);
        debug_assert_eq!(bound2, bound2_again);
        let diff_target = rsub(d, rat, point, target);
        let chained = d.lemma(
            rat.le_trans,
            &[diff_target, bound2, full_bound, at_bound, bound2_le_full],
        );
        d.lam_fv(k_fv, nat, chained)
    };

    let stmt = cle(d, p, x, embedded_target);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(x_fv, carrier, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_approx_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.rat_approx_lower : ∀ x n, CReal.le (CReal.ofRat (Rat.sub (CReal.seq
/// x n) (Rat.natDivSucc 1 n))) x` — the mirror of
/// [`declare_rat_approx_upper`], read off `CReal.regular x n k` instead of
/// `CReal.regular x k n`.
fn declare_rat_approx_lower(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let q = sample(d, p, x, n);
    let one_n = div_succ(d, p, 1, n);
    let lower_target = rsub(d, rat, q, one_n);
    let embedded_target = embed(d, p, lower_target);

    let body = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let point = sample(d, p, x, k);
        let diff = rsub(d, rat, q, point);
        let bound2 = div_succ(d, p, 1, k);
        let bound_nk = modulus(d, p, n, k);

        let regularity = d.lemma(p.regular, &[x, n, k]);
        let (_, upper) = halves(d, p, diff, bound_nk, regularity);

        // `q ≤ point + (one_n + bound2)`.
        let h0 = d.lemma(rat.le_of_sub_le, &[q, point, bound_nk, upper]);
        let start = radd(d, point, bound_nk);

        // Rearrange: `point + (one_n + bound2) = one_n + (point + bound2)`.
        let point_plus_one_n = radd(d, point, one_n);
        let mid_a = radd(d, point_plus_one_n, bound2);
        let assoc1 = d.lemma(rat.add_assoc, &[point, one_n, bound2]);
        let step1 = rsymm(d, mid_a, start, assoc1);

        let one_n_plus_point = radd(d, one_n, point);
        let mid_b = radd(d, one_n_plus_point, bound2);
        let swap = d.lemma(rat.add_comm, &[point, one_n]);
        let step2 = rcongr(d, point_plus_one_n, one_n_plus_point, swap, &|d, t| {
            radd(d, t, bound2)
        });

        let point_plus_bound2 = radd(d, point, bound2);
        let target_shape = radd(d, one_n, point_plus_bound2);
        let assoc2 = d.lemma(rat.add_assoc, &[one_n, point, bound2]);

        let (_, chain_proof) = rchain(
            d,
            start,
            &[(mid_a, step1), (mid_b, step2), (target_shape, assoc2)],
        );

        let h1 = rat_eq_rewrite(d, start, target_shape, chain_proof, h0, &|d, t| {
            rle(d, rat, q, t)
        });

        // `q − one_n ≤ point + bound2`, i.e. `lower_target ≤ point + bound2`.
        let h2 = d.lemma(rat.sub_le_of_le, &[q, one_n, point_plus_bound2, h1]);

        // `lower_target − point ≤ bound2 ≤ 2/(k+1)`.
        let at_bound = d.lemma(rat.sub_le_of_le, &[lower_target, point, bound2, h2]);
        let (bound2_again, full_bound, bound2_le_full) = widen_to_double(d, p, k);
        debug_assert_eq!(bound2, bound2_again);
        let diff_target = rsub(d, rat, lower_target, point);
        let chained = d.lemma(
            rat.le_trans,
            &[diff_target, bound2, full_bound, at_bound, bound2_le_full],
        );
        d.lam_fv(k_fv, nat, chained)
    };

    let stmt = cle(d, p, embedded_target, x);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(x_fv, carrier, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_approx_lower,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.density : ∀ x n, ∃ q : Rat, CReal.le x (CReal.ofRat (Rat.add q
/// (Rat.natDivSucc 1 n))) ∧ CReal.le (CReal.ofRat (Rat.sub q (Rat.natDivSucc 1
/// n))) x`.
///
/// The packaged statement: `seq x n` is a witness by
/// [`declare_rat_approx_upper`] and [`declare_rat_approx_lower`] together —
/// **ℚ is dense in ℝ**, with an explicit modulus and no search.
fn declare_density_theorem(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let nat = d.nat_ty();
    let one = d.level_one();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let witness = sample(d, p, x, n);
    let one_n = div_succ(d, p, 1, n);

    let upper_stmt = {
        let target = radd(d, witness, one_n);
        let embedded = embed(d, p, target);
        cle(d, p, x, embedded)
    };
    let lower_stmt = {
        let target = rsub(d, p.rat, witness, one_n);
        let embedded = embed(d, p, target);
        cle(d, p, embedded, x)
    };
    let upper_proof = d.lemma(p.rat_approx_upper, &[x, n]);
    let lower_proof = d.lemma(p.rat_approx_lower, &[x, n]);
    let conjunction = and_intro(d, p, upper_stmt, lower_stmt, upper_proof, lower_proof);

    // `∃ q, CReal.le x (ofRat (q+1/(n+1))) ∧ CReal.le (ofRat (q-1/(n+1))) x`.
    let predicate = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let upper = {
            let target = radd(d, q, one_n);
            let embedded = embed(d, p, target);
            cle(d, p, x, embedded)
        };
        let lower = {
            let target = rsub(d, p.rat, q, one_n);
            let embedded = embed(d, p, target);
            cle(d, p, embedded, x)
        };
        let body = d.and(upper, lower);
        d.lam_fv(q_fv, rat_carrier, body)
    };
    let exists_name = p.rat.int.logic.exists_;
    let exists_intro_name = p.rat.int.logic.exists_intro;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let stmt = d.apply(exists_const, &[rat_carrier, predicate]);
    let intro = d.kernel().const_(exists_intro_name, vec![one]);
    let witnessed = d.apply(intro, &[rat_carrier, predicate, witness, conjunction]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, witnessed);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(x_fv, carrier, over_n)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.density,
        uparams: vec![],
        ty,
        value,
    })
}
