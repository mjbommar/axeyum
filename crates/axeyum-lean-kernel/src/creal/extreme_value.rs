//! **The Extreme Value Theorem's boundary certificate** (ADR-0603 row 2,
//! Spivak *Calculus* ch. 7 "Three Hard Theorems") — a machine-checked
//! reduction showing that an *attained* maximum, even for the simplest
//! non-trivial uniformly continuous family on `[0, 1]`, decides an order
//! question this development states outright that it cannot decide.
//!
//! ## What this file replaces
//!
//! `crates/axeyum-cas/src/extremum.rs` carried the row-2 claim as prose
//! ("Row 2 (kernel side, **in progress**)"), and
//! `docs/curriculum/graded-statement-families.md` recorded EVT's row 2 as
//! *asserted, not proved*. An asserted unavailability cannot fail, so it is
//! not evidence. This file makes the assertion a theorem.
//!
//! ## The statement, and why this one
//!
//! Classical EVT says: `F` continuous on `[a, b]` with `a ≤ b` implies there
//! is a `c ∈ [a, b]` with `F z ≤ F c` for every `z ∈ [a, b]`. The
//! constructive general form this development *does* have is
//! [`CReal.bounded_of_uniformly_continuous`](super::CRealPrelude::bounded_of_uniformly_continuous)
//! — a **computed** bound `K`, never an `∃ K`, and never an attaining point.
//! Row 2 asks what goes wrong if the attaining point is demanded.
//!
//! Take the one-parameter family
//!
//! ```text
//! CReal.evtLinear v := fun t => CReal.mul t v
//! ```
//!
//! — `t ↦ t·v`, on the interval `[0, 1]`. It is Lipschitz with constant
//! `|v|`, hence uniformly continuous, and its classical supremum over
//! `[0, 1]` is `max(0, v)`, attained at `t = 1` when `v ≥ 0` and at `t = 0`
//! when `v ≤ 0`. **Which endpoint attains it is precisely the sign of `v`**,
//! and that is the whole content of the counterexample: a maximizer `c` is
//! not merely a real number, it is a real number whose *position* answers a
//! question about `v`.
//!
//! [`CReal.evt_attained_max_decides_sign`](super::CRealPrelude::evt_attained_max_decides_sign)
//! turns that observation into a kernel-checked implication:
//!
//! ```text
//! ∀ v c, le zero c → le c one →
//!   (∀ t, le zero t → le t one → le (mul t v) (mul c v)) →
//!   Or (le v zero) (le zero v)
//! ```
//!
//! The conclusion `∀ v, v ≤ 0 ∨ 0 ≤ v` is *analytic LLPO* — equivalently,
//! after a translation, the total order `le_total` on `CReal`. And
//! [`creal/cotransitivity.rs`](super::cotransitivity)'s own module
//! documentation states the position this development takes on it verbatim:
//! "[`CReal.lt`](super::CRealPrelude::lt) is not decidable and **no
//! `lt_total` is assumed or provable over `CReal`** (`Rat.le_or_lt` holds for
//! `ℚ` and does not lift)." Cotransitivity exists precisely because that
//! total comparison does not.
//!
//! So an *operator* `argmax : CReal → CReal` returning an attaining point for
//! every `evtLinear v` would discharge the hypothesis at every `v` at once
//! and hand back `∀ v, Or (le v zero) (le zero v)` — the comparison the
//! order deliberately lacks. That is the boundary, proved rather than
//! asserted, and it is what makes
//! [`CReal.bounded_of_uniformly_continuous`](super::CRealPrelude::bounded_of_uniformly_continuous)
//! optimal rather than merely unimproved.
//!
//! ## The proof, on paper
//!
//! Both branches come from ONE application of
//! [`CReal.lt_cotrans`](super::CRealPrelude::lt_cotrans) to the **fixed,
//! always-strict** pair `zero < one`
//! ([`CReal.zero_lt_one`](super::CRealPrelude::zero_lt_one)) at `z := c` —
//! the same device [`CReal.ivt_step`](super::CRealPrelude::ivt_step) uses,
//! and for the same reason: nothing anywhere decides an exact sign.
//! `lt_cotrans` returns `Or (lt zero c) (lt c one)`, unconditionally.
//!
//! - **`0 < c`.** Instantiate the maximality hypothesis at `t := 0`:
//!   `0·v ≤ c·v`, i.e. (`mul_comm`, `mul_zero`) `c·0 ≤ c·v`. Cancel the
//!   positive left factor with
//!   [`CReal.le_of_mul_le_mul_left`](super::CRealPrelude::le_of_mul_le_mul_left),
//!   whose separating modulus comes from
//!   [`CReal.pos_bound_of_lt`](super::CRealPrelude::pos_bound_of_lt). Result:
//!   `0 ≤ v`, the right disjunct.
//! - **`c < 1`.** Instantiate at `t := 1`: `1·v ≤ c·v`, i.e. `v ≤ c·v`. Put
//!   `K := 1 + (−c)`, which is positive because `c < 1`
//!   (`add_lt_add_of_le_of_lt` at `le_refl (neg c)`, transported by
//!   `lt_congr` across `(−c) + c ≈ 0` and `(−c) + 1 ≈ 1 + (−c)`). Adding
//!   `K·v` to both sides of `v ≤ c·v` gives `v + K·v ≤ c·v + K·v`, and
//!   `c·v + K·v ≈ (c + K)·v ≈ 1·v ≈ v ≈ v + 0` by `right_distrib` and
//!   `c + (1 + (−c)) ≈ 1`. Cancelling the common `v` on the left (add
//!   `−v` to both sides, then `(v + u) + (−v) ≈ u`) leaves `K·v ≤ 0 ≈ K·0`,
//!   and the same cancellation lemma at `K` gives `v ≤ 0`, the left
//!   disjunct.
//!
//! Note what the proof does **not** use: neither `le zero c` nor `le c one`
//! is consumed anywhere. They are kept in the statement because EVT's own
//! conclusion supplies them — a faithful hypothesis, not a needed one — and
//! their being unnecessary strengthens the refutation: the maximizer need not
//! even be known to lie in the interval for the decision to fall out.
//!
//! ## Honest scope — what this is NOT
//!
//! This is **not** a proof that `∀ v, Or (le v zero) (le zero v)` is FALSE,
//! and no such proof is available: analytic LLPO is consistent with Bishop's
//! constructive mathematics (it is what a classical reading of this
//! development would simply assert), so it is *unprovable here*, not
//! refutable. The same is true of `creal/ivt.rs`'s row 2, which likewise
//! refutes specific constructions and argues the general case by reduction
//! to an undecidable sign rather than by deriving `False`.
//!
//! What "refuted" therefore means, precisely, for both files: **the classical
//! conclusion is proved at least as strong as a decision principle this
//! kernel demonstrably does not have.** That is a machine-checked statement
//! about the boundary, and it is falsifiable: if someone lands `lt_total`
//! over `CReal`, this theorem stops being a refutation and becomes a route to
//! EVT.

#![allow(clippy::too_many_lines, clippy::many_single_char_names)]

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, cadd, cle, clt, creal_ty};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};

/// Admit `CReal.evtLinear` and `CReal.evt_attained_max_decides_sign`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_extreme_value(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_evt_linear(d, p)?;
    declare_evt_attained_max_decides_sign(d, p)
}

// --- local term helpers -----------------------------------------------------

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `Equiv.symm` at an already-known `Equiv a b`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Compose `a ~ b` and `b ~ c` into `a ~ c`.
fn etrans(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.lemma(p.equiv_trans, &[a, b, c, h1, h2])
}

/// Fold `start ~ s₁ ~ s₂ ~ …` into a single `Equiv start last`, returning
/// `(last, proof)`. A local copy of the shape `ring_helpers::echain` uses;
/// that one is private to its own module.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = etrans(d, p, start, current, next, proof, step);
        current = next;
    }
    (current, proof)
}

/// `Equiv (mul zero v) zero` — `mul_comm` then `mul_zero`.
fn zero_mul_equiv(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let zv = cmul(d, p, zero, v);
    let vz = cmul(d, p, v, zero);
    let comm = d.lemma(p.mul_comm, &[zero, v]);
    let collapse = d.lemma(p.mul_zero, &[v]);
    let (_, proof) = echain(d, p, zv, &[(vz, comm), (zero, collapse)]);
    proof
}

/// `Equiv (mul one v) v` — `mul_comm` then `mul_one`.
fn one_mul_equiv(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId) -> ExprId {
    let one = d.kernel().const_(p.one, vec![]);
    let ov = cmul(d, p, one, v);
    let vo = cmul(d, p, v, one);
    let comm = d.lemma(p.mul_comm, &[one, v]);
    let collapse = d.lemma(p.mul_one, &[v]);
    let (_, proof) = echain(d, p, ov, &[(vo, comm), (v, collapse)]);
    proof
}

/// `Equiv (add (add v u) (neg v)) u` — cancel a repeated left summand.
fn add_cancel_left(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, u: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let nv = cneg(d, p, v);
    let vu = cadd(d, p, v, u);
    let start = cadd(d, p, vu, nv);
    // (v + u) + (−v) ~ (u + v) + (−v)
    let uv = cadd(d, p, u, v);
    let inner = d.lemma(p.add_comm, &[v, u]);
    let s1 = cadd(d, p, uv, nv);
    let refl_nv = d.lemma(p.equiv_refl, &[nv]);
    let step1 = d.lemma(p.add_congr, &[vu, uv, nv, nv, inner, refl_nv]);
    // (u + v) + (−v) ~ u + (v + (−v))
    let vnv = cadd(d, p, v, nv);
    let s2 = cadd(d, p, u, vnv);
    let step2 = d.lemma(p.add_assoc, &[u, v, nv]);
    // u + (v + (−v)) ~ u + 0
    let cancel = d.lemma(p.add_neg, &[v]);
    let refl_u = d.lemma(p.equiv_refl, &[u]);
    let s3 = cadd(d, p, u, zero);
    let step3 = d.lemma(p.add_congr, &[u, u, vnv, zero, refl_u, cancel]);
    // u + 0 ~ u
    let step4 = d.lemma(p.add_zero, &[u]);
    let (_, proof) = echain(
        d,
        p,
        start,
        &[(s1, step1), (s2, step2), (s3, step3), (u, step4)],
    );
    proof
}

/// `Equiv (add c (add one (neg c))) one`.
fn c_add_one_sub_c(d: &mut IntDev<'_>, p: CRealPrelude, c: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let nc = cneg(d, p, c);
    let k = cadd(d, p, one, nc);
    let start = cadd(d, p, c, k);
    // c + (1 + (−c)) ~ c + ((−c) + 1)
    let nc1 = cadd(d, p, nc, one);
    let inner = d.lemma(p.add_comm, &[one, nc]);
    let refl_c = d.lemma(p.equiv_refl, &[c]);
    let s1 = cadd(d, p, c, nc1);
    let step1 = d.lemma(p.add_congr, &[c, c, k, nc1, refl_c, inner]);
    // c + ((−c) + 1) ~ (c + (−c)) + 1  -- `add_assoc` runs the other way.
    let cnc = cadd(d, p, c, nc);
    let s2 = cadd(d, p, cnc, one);
    let assoc = d.lemma(p.add_assoc, &[c, nc, one]);
    let step2 = esymm(d, p, s2, s1, assoc);
    // (c + (−c)) + 1 ~ 0 + 1
    let cancel = d.lemma(p.add_neg, &[c]);
    let refl_one = d.lemma(p.equiv_refl, &[one]);
    let s3 = cadd(d, p, zero, one);
    let step3 = d.lemma(p.add_congr, &[cnc, zero, one, one, cancel, refl_one]);
    // 0 + 1 ~ 1 + 0 ~ 1
    let s4 = cadd(d, p, one, zero);
    let step4 = d.lemma(p.add_comm, &[zero, one]);
    let step5 = d.lemma(p.add_zero, &[one]);
    let (_, proof) = echain(
        d,
        p,
        start,
        &[
            (s1, step1),
            (s2, step2),
            (s3, step3),
            (s4, step4),
            (one, step5),
        ],
    );
    proof
}

// --- `CReal.evtLinear` ------------------------------------------------------

/// `CReal.evtLinear : CReal → CReal → CReal := fun v t => mul t v`.
///
/// The EVT counterexample family, as a named object so the row-2 statement
/// and its concrete instantiations can both refer to it. Lipschitz with
/// constant `|v|`, so uniformly continuous on every interval; classical
/// supremum `max(0, v)` on `[0, 1]`, attained at `1` when `v ≥ 0` and at `0`
/// when `v ≤ 0`.
fn declare_evt_linear(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let body = cmul(d, p, t, v);
    let value = {
        let inner = d.lam_fv(t_fv, carrier, body);
        d.lam_fv(v_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.evt_linear,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 1),
    })
}

// --- `CReal.evt_attained_max_decides_sign` ----------------------------------

/// `CReal.evt_attained_max_decides_sign : ∀ v c, le zero c → le c one →
/// (∀ t, le zero t → le t one → le (mul t v) (mul c v)) →
/// Or (le v zero) (le zero v)` — this file's module documentation has the
/// statement, the reason for this particular family, and the two-branch
/// paper proof.
fn declare_evt_attained_max_decides_sign(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    // The two faithful-but-unused interval hypotheses.
    let hc0_ty = cle(d, p, zero, c);
    let hc1_ty = cle(d, p, c, one);

    // hmax : ∀ t, le zero t → le t one → le (mul t v) (mul c v)
    let cv = cmul(d, p, c, v);
    let hmax_ty = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let lo = cle(d, p, zero, t);
        let hi = cle(d, p, t, one);
        let tv = cmul(d, p, t, v);
        let concl = cle(d, p, tv, cv);
        let with_hi = d.arrow(hi, concl);
        let with_lo = d.arrow(lo, with_hi);
        d.pi_fv(t_fv, carrier, with_lo)
    };

    let left_disj = cle(d, p, v, zero);
    let right_disj = cle(d, p, zero, v);
    let target = d.or(left_disj, right_disj);

    let hmax_fv = d.fresh_fvar();
    let hmax = d.kernel().fvar(hmax_fv);

    // `le zero one`, needed to instantiate `hmax` at both endpoints.
    let zero_lt_one = d.kernel().const_(p.zero_lt_one, vec![]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zero_lt_one]);

    // hmax0 : le (mul zero v) (mul c v)
    let refl_zero = d.lemma(p.le_refl, &[zero]);
    let hmax0 = d.apply(hmax, &[zero, refl_zero, zero_le_one]);
    // hmax1 : le (mul one v) (mul c v)
    let refl_one = d.lemma(p.le_refl, &[one]);
    let hmax1 = d.apply(hmax, &[one, zero_le_one, refl_one]);

    let lt_zero_c = clt(d, p, zero, c);
    let lt_c_one = clt(d, p, c, one);
    let cotrans = d.lemma(p.lt_cotrans, &[zero, one, zero_lt_one, c]);

    let body = d.or_elim(
        lt_zero_c,
        lt_c_one,
        target,
        cotrans,
        // --- branch A: 0 < c  =>  0 ≤ v -------------------------------------
        &|d, hpos| {
            let nat = d.nat_ty();
            let pos_bound_pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.const_app(p.pos_bound, &[c, k]);
                d.lam_fv(k_fv, nat, body)
            };
            let witness = d.lemma(p.pos_bound_of_lt, &[c, hpos]);
            let minor = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = d.const_app(p.pos_bound, &[c, k]);
                // le (mul c zero) (mul c v), from hmax0 across
                // Equiv (mul zero v) (mul c zero).
                let zv = cmul(d, p, zero, v);
                let cz = cmul(d, p, c, zero);
                let zv_zero = zero_mul_equiv(d, p, v);
                let cz_zero = d.lemma(p.mul_zero, &[c]);
                let zero_cz = esymm(d, p, cz, zero, cz_zero);
                let zv_cz = etrans(d, p, zv, zero, cz, zv_zero, zero_cz);
                let refl_cv = d.lemma(p.equiv_refl, &[cv]);
                let shifted = d.lemma(p.le_congr, &[zv, cz, cv, cv, zv_cz, refl_cv, hmax0]);
                let cancelled = d.lemma(p.le_of_mul_le_mul_left, &[c, zero, v, k, hk, shifted]);
                let proof = d.or_inr(left_disj, right_disj, cancelled);
                let with_hk = d.lam_fv(hk_fv, hk_ty, proof);
                d.lam_fv(k_fv, nat, with_hk)
            };
            exists_elim(d, pos_bound_pred, target, witness, minor)
        },
        // --- branch B: c < 1  =>  v ≤ 0 -------------------------------------
        &|d, hlt1| {
            let nat = d.nat_ty();
            let nc = cneg(d, p, c);
            let kk = cadd(d, p, one, nc);
            // 0 < K := 1 + (−c)
            let refl_nc = d.lemma(p.le_refl, &[nc]);
            let raw = d.lemma(p.add_lt_add_of_le_of_lt, &[nc, nc, c, one, refl_nc, hlt1]);
            // raw : lt (add (neg c) c) (add (neg c) one)
            let nc_c = cadd(d, p, nc, c);
            let c_nc = cadd(d, p, c, nc);
            let lhs_comm = d.lemma(p.add_comm, &[nc, c]);
            let lhs_cancel = d.lemma(p.add_neg, &[c]);
            let (_, lhs_eq) = echain(d, p, nc_c, &[(c_nc, lhs_comm), (zero, lhs_cancel)]);
            let nc_one = cadd(d, p, nc, one);
            let rhs_eq = d.lemma(p.add_comm, &[nc, one]);
            let kpos = d.lemma(p.lt_congr, &[nc_c, zero, nc_one, kk, lhs_eq, rhs_eq, raw]);

            let pos_bound_pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = d.const_app(p.pos_bound, &[kk, k]);
                d.lam_fv(k_fv, nat, body)
            };
            let witness = d.lemma(p.pos_bound_of_lt, &[kk, kpos]);
            let minor = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let hk_ty = d.const_app(p.pos_bound, &[kk, k]);

                // hd : le v (mul c v), from hmax1 across Equiv (mul one v) v.
                let ov = cmul(d, p, one, v);
                let ov_v = one_mul_equiv(d, p, v);
                let refl_cv = d.lemma(p.equiv_refl, &[cv]);
                let hd = d.lemma(p.le_congr, &[ov, v, cv, cv, ov_v, refl_cv, hmax1]);

                // v + K·v ≤ c·v + K·v
                let kv = cmul(d, p, kk, v);
                let refl_kv = d.lemma(p.le_refl, &[kv]);
                let widened = d.lemma(p.add_le_add, &[v, cv, kv, kv, hd, refl_kv]);
                let lhs = cadd(d, p, v, kv);
                let rhs = cadd(d, p, cv, kv);

                // c·v + K·v ~ (c + K)·v ~ 1·v ~ v ~ v + 0
                let ck = cadd(d, p, c, kk);
                let ckv = cmul(d, p, ck, v);
                let dist = right_distrib(d, p, c, kk, v);
                let dist_back = esymm(d, p, ckv, rhs, dist);
                let ck_one = c_add_one_sub_c(d, p, c);
                let refl_v = d.lemma(p.equiv_refl, &[v]);
                let to_one_v = d.lemma(p.mul_congr, &[ck, one, v, v, ck_one, refl_v]);
                let one_v = one_mul_equiv(d, p, v);
                let v_zero = cadd(d, p, v, zero);
                let add_zero = d.lemma(p.add_zero, &[v]);
                let v_to_v_zero = esymm(d, p, v_zero, v, add_zero);
                let (_, rhs_eq2) = echain(
                    d,
                    p,
                    rhs,
                    &[
                        (ckv, dist_back),
                        (ov, to_one_v),
                        (v, one_v),
                        (v_zero, v_to_v_zero),
                    ],
                );
                let refl_lhs = d.lemma(p.equiv_refl, &[lhs]);
                let shifted =
                    d.lemma(p.le_congr, &[lhs, lhs, rhs, v_zero, refl_lhs, rhs_eq2, widened]);
                // shifted : le (add v kv) (add v zero)

                // Cancel the common `v`: add (−v) to both sides.
                let nv = cneg(d, p, v);
                let refl_nv = d.lemma(p.le_refl, &[nv]);
                let both = d.lemma(p.add_le_add, &[lhs, v_zero, nv, nv, shifted, refl_nv]);
                let l2 = cadd(d, p, lhs, nv);
                let r2 = cadd(d, p, v_zero, nv);
                let l2_eq = add_cancel_left(d, p, v, kv);
                let r2_eq = add_cancel_left(d, p, v, zero);
                let cancelled_add = d.lemma(p.le_congr, &[l2, kv, r2, zero, l2_eq, r2_eq, both]);
                // cancelled_add : le kv zero

                // le (mul K v) (mul K zero), then cancel K.
                let kz = cmul(d, p, kk, zero);
                let kz_zero = d.lemma(p.mul_zero, &[kk]);
                let zero_kz = esymm(d, p, kz, zero, kz_zero);
                let refl_kv2 = d.lemma(p.equiv_refl, &[kv]);
                let ready = d.lemma(
                    p.le_congr,
                    &[kv, kv, zero, kz, refl_kv2, zero_kz, cancelled_add],
                );
                let cancelled = d.lemma(p.le_of_mul_le_mul_left, &[kk, v, zero, k, hk, ready]);
                let proof = d.or_inl(left_disj, right_disj, cancelled);
                let with_hk = d.lam_fv(hk_fv, hk_ty, proof);
                d.lam_fv(k_fv, nat, with_hk)
            };
            exists_elim(d, pos_bound_pred, target, witness, minor)
        },
    );

    let value = {
        let with_hmax = d.lam_fv(hmax_fv, hmax_ty, body);
        let hc1_fv = d.fresh_fvar();
        let with_hc1 = d.lam_fv(hc1_fv, hc1_ty, with_hmax);
        let hc0_fv = d.fresh_fvar();
        let with_hc0 = d.lam_fv(hc0_fv, hc0_ty, with_hc1);
        let with_c = d.lam_fv(c_fv, carrier, with_hc0);
        d.lam_fv(v_fv, carrier, with_c)
    };
    let ty = {
        let with_hmax = d.arrow(hmax_ty, target);
        let with_hc1 = d.arrow(hc1_ty, with_hmax);
        let with_hc0 = d.arrow(hc0_ty, with_hc1);
        let with_c = d.pi_fv(c_fv, carrier, with_hc0);
        d.pi_fv(v_fv, carrier, with_c)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.evt_attained_max_decides_sign,
        uparams: vec![],
        ty,
        value,
    })
}
