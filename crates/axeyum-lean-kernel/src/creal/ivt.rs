//! The **constructive approximate Intermediate Value Theorem** (Spivak,
//! *Calculus*, Ch. 7 "Three Hard Theorems") — the one-step bisection lemma
//! `CReal.ivt_step`, its `n`-fold iteration `CReal.ivt_iter`, and the closing
//! statement `CReal.ivt_approx`.
//!
//! ## Why the classical statement is unavailable
//!
//! Classical IVT (`f` continuous on `[a,b]`, `f a ≤ 0 ≤ f b` ⟹ `∃ x, f x =
//! 0`) asserts a *computable* root, and no algorithm produces one in general:
//! deciding which side of the root a candidate point falls on is exactly as
//! hard as deciding the sign of an arbitrary real, which
//! [`cotransitivity`](super::cotransitivity)'s own module documentation
//! already explains is not constructively available (`CReal.lt` has no
//! `lt_total`). The constructive replacement is the *approximate* IVT: `∀ ε >
//! 0, ∃ x ∈ [a,b], |f x| ≤ ε`.
//!
//! ## The one-step lemma, worked on paper
//!
//! Fix a target slack `eps > 0` (this will end up being half the caller's
//! accuracy target — see [`CReal.ivt_approx`](super::CRealPrelude::ivt_approx)
//! below) and a bracket `[P, Q]`
//! satisfying the **weak sign invariant** `F P ≤ eps` and `−eps ≤ F Q` — note
//! this is *not* `F P ≤ 0 ≤ F Q`; the slack is what makes the step avoid ever
//! deciding an exact sign.
//!
//! Let `m := P + (Q − P)·(1/2)`, the exact midpoint (ordinary bisection — the
//! usual "trisection" write-up in the literature is needed only when the
//! invariant being maintained is the *exact* `F P ≤ 0 ≤ F Q`, which forces
//! comparing two interior points to avoid ever landing exactly on a decision
//! boundary; testing against a **fixed slack `eps`** removes that need; see
//! "Why not trisection" below).
//!
//! [`CReal.lt_cotrans`](super::CRealPrelude::lt_cotrans) applied to the
//! **fixed, always-strict** pair `−eps < eps` (strict because `eps > 0`,
//! independent of `P`, `Q`, `F` or `m`) at `z := F m` gives, unconditionally:
//!
//! ```text
//! Or (−eps < F m) (F m < eps)
//! ```
//!
//! Both disjuncts are usable, and which one the algorithm returns is
//! irrelevant to correctness — each justifies a smaller bracket that keeps
//! the invariant:
//!
//! - **`F m < eps`**: take the new bracket `[m, Q]`. `F m ≤ eps` is exactly
//!   the hypothesis this branch supplies (weakening `<` to `≤`), and `−eps ≤
//!   F Q` is untouched — `Q` did not move.
//! - **`−eps < F m`**: take the new bracket `[P, m]`. `F P ≤ eps` is
//!   untouched, and `−eps ≤ F m` is exactly this branch's hypothesis.
//!
//! In **both** cases the new width is exactly `(Q − P)·(1/2)` — plain
//! midpoint bisection, not a worst-case bound — because both bracket halves
//! have equal width by construction. Iterating `N` times
//! ([`CReal.ivt_iter`](super::CRealPrelude::ivt_iter), below) shrinks the
//! width geometrically as `(1/2)^N`, and once it drops under the modulus
//! [`CReal.UniformlyContinuousOn`](super::CRealPrelude::uniformly_continuous_on)
//! supplies for the target accuracy, continuity turns "the endpoints are
//! close" into "their `F`-values are close", which combined with the sign
//! invariant on the two endpoints pins down `|F x| ≤` the target for `x` one
//! of the two final endpoints. That combination step
//! ([`CReal.ivt_approx`](super::CRealPrelude::ivt_approx), `∀ e : Nat, ∃ x,
//! …`) needs a quantitative bound relating `pow x n` to a `natDivSucc`-shaped
//! rational threshold — [`CReal.pow_half_le_natDivSucc`](super::CRealPrelude::pow_half_le_nat_div_succ)
//! (`geometric.rs`) — and an Archimedean bound on the initial width, both
//! consumed by `ivt_approx`'s own construction below.
//!
//! ## Why not trisection
//!
//! The textbook argument compares `F` at *two* interior points `u < v`
//! because it maintains the *exact* invariant `F P ≤ 0 ≤ F Q` throughout, and
//! an exact `0` threshold cannot use cotransitivity directly (there is no
//! fixed strict pair straddling `0` alone — `lt_cotrans` needs a *known*
//! strict inequality to pivot on, and `0 < 0` is false). Splitting into
//! thirds and testing two points against each other manufactures that strict
//! pair from the domain side instead of the range side.
//!
//! Maintaining a **weak, ε-slack** invariant sidesteps the need for that
//! manufactured pair entirely: `−eps < eps` is already strict (from `eps >
//! 0`, fixed once, independent of the bracket), so a single interior point
//! and a single `lt_cotrans` call at that fixed pair suffices, and the
//! bracket bisects at the true midpoint rather than at a 1/3 point. This is
//! a smaller, and arguably more transparent, one-step lemma than the
//! two-point trisection, and it composes with the same downstream
//! Archimedean/uniform-continuity argument sketched above. Concretely: for
//! `eps := 1/(2(e+1))` (half the final accuracy target `1/(e+1)`) and
//! continuity's own accuracy also split as `1/(2(e+1))`, the two endpoints'
//! `F`-values after enough steps satisfy `F P ≤ eps`, `F Q ≥ −eps`, and `|F P
//! − F Q| ≤ eps`, from which `−eps ≤ F Q ≤ F P + eps ≤ 2·eps = 1/(e+1)`
//! (concretely, e.g. `e = 9`: `eps = 1/20`, and after enough bisection steps
//! `F Q` is pinned to `[−1/20, 1/10]`, giving `|F Q| ≤ 1/10`) — `x := Q`
//! is the desired witness, with no case split on any exact sign anywhere.
//!
//! ## What this file lands
//!
//! [`CReal.ivt_step`](super::CRealPrelude::ivt_step) — the bisection step
//! above, fully general in `F`, `P`, `Q`, `eps`; [`CReal.ivt_iter`](super::CRealPrelude::ivt_iter)
//! — `ivt_step` iterated `n` times by structural `Nat` induction, carrying
//! the same six-part invariant with the width tracked as `(Q0 − P0)·(1/2)ⁿ`
//! via `CReal.pow`; and [`CReal.ivt_approx`](super::CRealPrelude::ivt_approx)
//! — the outer `∀ e : Nat, ∃ x, …` statement, closing `ivt_iter` against
//! [`CReal.UniformlyContinuousOn`](super::CRealPrelude::uniformly_continuous_on)
//! and [`CReal.pow_half_le_natDivSucc`](super::CRealPrelude::pow_half_le_nat_div_succ);
//! and [`CReal.ivt_bisect`](super::CRealPrelude::ivt_bisect) (with its two
//! projections `ivt_bisect_lo`/`ivt_bisect_hi`) — a DATA-VALUED bisection
//! replacing `ivt_iter`'s `Exists`-wrapped bracket with one computed by
//! `Nat.rec`, per `docs/mathematics-2026-08/diary-exact-root-obstruction.md`.
//! This slice lands the computation and a concrete reduction check only; the
//! invariant spec theorem (that this bracket satisfies `ivt_step`'s own
//! six-part invariant) is a separate, not-yet-landed slice — see the
//! "Data-valued bisection" section near the bottom of this file.
//!
//! **The bound `pow_half_le_natDivSucc` supplies is linear (`1/(N+1)`), not
//! the tight geometric `1/2^N`** — it is a valid but looser upper bound, so
//! `ivt_approx` needs a bisection depth *proportional to* the target
//! accuracy rather than to its logarithm: `bisect_n := M·delta + c` for `c :=
//! CReal.bound (b − a)`, `M := c + 1`, `delta :=` the continuity modulus at
//! the chosen index (see [`CRealPrelude::ivt_approx`]'s own doc comment for
//! the full derivation). For `f := id` on `[0, 1]` at `e := 9`: `sgn_eps =
//! 1/20`, the identity's modulus is itself, so the continuity index is `n =
//! 19` and `delta = 19` — **not `N = 5`**, which was the right count only
//! under the never-built `2^N ≥ 20` route this file's earlier documentation
//! (wrongly) anticipated. `ivt_approx`'s own construction
//! (`declare_ivt_approx`, [`width_le_via_bound`]) computes `bisect_n`
//! directly from `CReal.bound`, with no search and no `Exists.rec`.
//!
//! **Chapter 12's exact inverse function theorem is now unblocked.** A
//! previous lane established that exact order-reflection is precisely as
//! hard as an exact IVT preimage — both need a computable root, which is
//! exactly what the *approximate* statement here declines to produce. With
//! `ivt_approx` landed, the *approximate* preimage direction that chapter
//! needs is available; the exact direction remains genuinely unavailable for
//! the same reason classical IVT is (see "Why the classical statement is
//! unavailable", above).

#![allow(
    clippy::too_many_arguments,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]

use super::ring_helpers::right_distrib;
use super::{
    CRealPrelude, and_intro, cadd, cle, clt, creal_ty, div_succ, embed, equiv, halves, sample,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_eq_to_rat, radd, rat_eq_rewrite, rle, rmul, rone, rzero};

/// Admit `CReal.ivt_step`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_ivt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_ivt_step(d, p)?;
    declare_ivt_iter(d, p)?;
    declare_ivt_approx(d, p)?;
    // The data-valued bisection (see this file's module documentation,
    // "Data-valued bisection" and `docs/mathematics-2026-08/diary-exact-root-
    // obstruction.md`) -- needs nothing beyond `ivt_step`/`ivt_iter`'s own
    // dependencies (`lt_cotrans` is NOT needed here: the branch is read off
    // `Rat.ble`, not `lt_cotrans`).
    declare_ivt_bisect(d, p)?;
    declare_ivt_bisect_lo(d, p)?;
    declare_ivt_bisect_hi(d, p)
}

// --- small shared idiom (private to this module, per the codebase's own
// "duplicated per file" convention — see `derivative.rs`'s identical copies
// of `cneg`/`cmul`/`czero`/`erefl`/`echain`) ---------------------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

/// `Equiv a a`.
fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

/// From `h : Equiv a b`, `Equiv b a`.
fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `(term, proof)` = `(ofRat (natDivSucc k idx), le zero term)`, copied from
/// `derivative.rs`'s private helper of the same name (that module is out of
/// this slice's file boundary).
fn nonneg_rat_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, idx: ExprId) -> (ExprId, ExprId) {
    let q = div_succ(d, p, k, idx);
    let ofr_q = d.const_app(p.of_rat, &[q]);
    let rzero_expr = rzero(d, p.rat);
    let numerator = d.num(k);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[numerator, idx]);
    let proof = d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg]);
    (ofr_q, proof)
}

/// `Equiv (ofNat (Nat.succ Nat.zero)) one`, copied from
/// `monotone.rs`'s private helper of the same name (itself duplicated from
/// `integral.rs`; both files are out of this slice's file boundary).
fn of_nat_one_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)`, copied from
/// `monotone.rs`'s private helper of the same name.
fn of_nat_succ_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = d.kernel().const_(p.one, vec![]);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        equiv(d, p, add_of_nat_m_1, embedded)
    });
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    let one_eq = of_nat_one_equiv_local(d, p);
    let refl_m = d.lemma(p.equiv_refl, &[of_nat_m]);
    let congr_step = d.lemma(
        p.add_congr,
        &[of_nat_m, of_nat_m, of_nat_1, one_c, refl_m, one_eq],
    );
    let add_of_nat_m_one = cadd(d, p, of_nat_m, one_c);
    d.lemma(
        p.equiv_trans,
        &[
            of_nat_succ_m,
            add_of_nat_m_1,
            add_of_nat_m_one,
            flipped,
            congr_step,
        ],
    )
}

// --- ring-algebra helpers, private to this module ---------------------------

/// `Equiv (add (add a x) (neg a)) x` — cancel a left-added `a`.
fn cancel_right(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, x: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let ax = cadd(d, p, a, x);
    let start = cadd(d, p, ax, na);
    let xa = cadd(d, p, x, a);
    let comm1 = d.lemma(p.add_comm, &[a, x]);
    let mid1 = cadd(d, p, xa, na);
    let refl_na = erefl(d, p, na);
    let step1 = d.lemma(p.add_congr, &[ax, xa, na, na, comm1, refl_na]);
    let assoc1 = d.lemma(p.add_assoc, &[x, a, na]);
    let a_na = cadd(d, p, a, na);
    let mid2 = cadd(d, p, x, a_na);
    let vanish = d.lemma(p.add_neg, &[a]);
    let zero_c = czero(d, p);
    let refl_x = erefl(d, p, x);
    let step3 = d.lemma(p.add_congr, &[x, x, a_na, zero_c, refl_x, vanish]);
    let x_zero = cadd(d, p, x, zero_c);
    let trim = d.lemma(p.add_zero, &[x]);
    echain(
        d,
        p,
        start,
        &[(mid1, step1), (mid2, assoc1), (x_zero, step3), (x, trim)],
    )
}

/// `Equiv (add a (add b (neg a))) b` — `a + (b − a) = b`.
fn restore_from_width(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let b_na = cadd(d, p, b, na);
    let start = cadd(d, p, a, b_na);
    let ab = cadd(d, p, a, b);
    let ab_na = cadd(d, p, ab, na);
    let assoc_ab = d.lemma(p.add_assoc, &[a, b, na]); // Equiv ab_na start
    let step_ab = esymm(d, p, ab_na, start, assoc_ab); // Equiv start ab_na

    let ba = cadd(d, p, b, a);
    let ba_na = cadd(d, p, ba, na);
    let comm_ab = d.lemma(p.add_comm, &[a, b]); // Equiv ab ba
    let refl_na = erefl(d, p, na);
    let step2 = d.lemma(p.add_congr, &[ab, ba, na, na, comm_ab, refl_na]); // Equiv ab_na ba_na

    let a_na = cadd(d, p, a, na);
    let b_ana = cadd(d, p, b, a_na);
    let assoc_bna = d.lemma(p.add_assoc, &[b, a, na]); // Equiv ba_na b_ana

    let vanish = d.lemma(p.add_neg, &[a]); // Equiv a_na zero
    let zero_c = czero(d, p);
    let b_zero = cadd(d, p, b, zero_c);
    let refl_b = erefl(d, p, b);
    let step4 = d.lemma(p.add_congr, &[b, b, a_na, zero_c, refl_b, vanish]); // Equiv b_ana b_zero

    let trim_b = d.lemma(p.add_zero, &[b]); // Equiv b_zero b

    echain(
        d,
        p,
        start,
        &[
            (ab_na, step_ab),
            (ba_na, step2),
            (b_ana, assoc_bna),
            (b_zero, step4),
            (b, trim_b),
        ],
    )
}

/// `Equiv (add (neg x) x) zero`.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h_ab_zero : Equiv (add a b) zero`, derive `Equiv b (neg a)` -- `b`
/// is the unique additive inverse of `a`. Verbatim reproduction of
/// `deriv_unique.rs`'s private helper of the same name (itself copied from
/// `derivative.rs`; both files are out of this slice's edit boundary).
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (neg (neg x)) x` -- double negation, from [`neg_unique`] applied
/// to [`neg_add_self`]. Verbatim reproduction of `deriv_unique.rs`'s private
/// helper of the same name.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// From `h : le y z`, `le zero (add z (neg y))` — copied from
/// `derivative.rs`'s private helper of the same name.
fn sub_nonneg_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    y: ExprId,
    z: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let gap = cadd(d, p, z, ny);
    let cancelled = cadd(d, p, y, ny);

    let reflexive = d.lemma(p.le_refl, &[ny]);
    let shifted = d.lemma(p.add_le_add, &[y, z, ny, ny, h, reflexive]);
    let cancel = d.lemma(p.add_neg, &[y]);
    let gap_refl = erefl(d, p, gap);
    d.lemma(
        p.le_congr,
        &[cancelled, zero_c, gap, gap, cancel, gap_refl, shifted],
    )
}

/// From `h : le zero (add b (neg a))`, `le a b` — copied from
/// `derivative.rs`'s private helper of the same name.
fn le_of_nonneg_sub(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let gap = cadd(d, p, b, na);
    let zero_a = cadd(d, p, zero_c, a);
    let gap_a = cadd(d, p, gap, a);
    let na_a = cadd(d, p, na, a);
    let b_naa = cadd(d, p, b, na_a);
    let a_zero = cadd(d, p, a, zero_c);
    let b_zero = cadd(d, p, b, zero_c);

    let reflexive = d.lemma(p.le_refl, &[a]);
    let step1 = d.lemma(p.add_le_add, &[zero_c, gap, a, a, h, reflexive]);

    let lhs_comm = d.lemma(p.add_comm, &[zero_c, a]);
    let lhs_trim = d.lemma(p.add_zero, &[a]);
    let lhs_eq = echain(d, p, zero_a, &[(a_zero, lhs_comm), (a, lhs_trim)]);

    let rhs_assoc = d.lemma(p.add_assoc, &[b, na, a]);
    let na_a_zero = neg_add_self(d, p, a);
    let refl_b = erefl(d, p, b);
    let rhs_congr = d.lemma(p.add_congr, &[b, b, na_a, zero_c, refl_b, na_a_zero]);
    let rhs_trim = d.lemma(p.add_zero, &[b]);
    let rhs_eq = echain(
        d,
        p,
        gap_a,
        &[(b_naa, rhs_assoc), (b_zero, rhs_congr), (b, rhs_trim)],
    );

    d.lemma(p.le_congr, &[zero_a, a, gap_a, b, lhs_eq, rhs_eq, step1])
}

/// From `hx : lt zero x`, `lt (neg x) x`.
fn neg_lt_of_pos(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, hx: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let refl_nx = d.lemma(p.le_refl, &[nx]);
    let step1 = d.lemma(p.add_lt_add_of_le_of_lt, &[nx, nx, zero_c, x, refl_nx, hx]);
    // step1 : lt (add nx zero) (add nx x)

    let nx_zero = cadd(d, p, nx, zero_c);
    let nx_x = cadd(d, p, nx, x);
    let add_zero_nx = d.lemma(p.add_zero, &[nx]); // Equiv nx_zero nx
    let refl_nxx = erefl(d, p, nx_x);
    let step2 = d.lemma(
        p.lt_congr,
        &[nx_zero, nx, nx_x, nx_x, add_zero_nx, refl_nxx, step1],
    );
    // step2 : lt nx nx_x

    let comm = d.lemma(p.add_comm, &[nx, x]); // Equiv nx_x (add x nx)
    let x_nx = cadd(d, p, x, nx);
    let vanish = d.lemma(p.add_neg, &[x]); // Equiv x_nx zero
    let compose = d.lemma(p.equiv_trans, &[nx_x, x_nx, zero_c, comm, vanish]);
    let refl_nx2 = erefl(d, p, nx);
    let step3 = d.lemma(
        p.lt_congr,
        &[nx, nx, nx_x, zero_c, refl_nx2, compose, step2],
    );
    // step3 : lt nx zero

    d.lemma(p.lt_trans, &[nx, zero_c, x, step3, hx])
}

/// `Equiv (add step step) width`, where `step := mul width (ofRat
/// (natDivSucc 1 1))` — the exact "half the width, twice, is the width"
/// identity `CReal.mesh_count_width` (at its two-pieces instance) already
/// supplies, unfolded through `ofNat 2 ~ one + one`.
fn width_eq_two_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    width: ExprId,
    step: ExprId,
    one_nat: ExprId,
) -> ExprId {
    // mcw : Equiv (mul (ofNat 2) step) width
    let mcw = d.lemma(p.mesh_count_width, &[width, one_nat]);

    let two_nat = d.succ(one_nat);
    let of_nat2 = d.const_app(p.of_nat, &[two_nat]);
    let of_nat1 = d.const_app(p.of_nat, &[one_nat]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let of_nat1_eq = of_nat_one_equiv_local(d, p); // Equiv of_nat1 one_c
    let succ_eq = of_nat_succ_equiv_local(d, p, one_nat); // Equiv of_nat2 (add of_nat1 one_c)

    let step_b = {
        let refl_one = erefl(d, p, one_c);
        d.lemma(
            p.add_congr,
            &[of_nat1, one_c, one_c, one_c, of_nat1_eq, refl_one],
        )
    }; // Equiv (add of_nat1 one_c) (add one_c one_c)
    let add_of_nat1_one = cadd(d, p, of_nat1, one_c);
    let one_one = cadd(d, p, one_c, one_c);
    let of_nat2_eq_oneone = d.lemma(
        p.equiv_trans,
        &[of_nat2, add_of_nat1_one, one_one, succ_eq, step_b],
    ); // Equiv of_nat2 one_one

    let mul_ofnat2_step = cmul(d, p, of_nat2, step);
    let mul_oneone_step = cmul(d, p, one_one, step);
    let step_c = {
        let refl_step = erefl(d, p, step);
        d.lemma(
            p.mul_congr,
            &[of_nat2, one_one, step, step, of_nat2_eq_oneone, refl_step],
        )
    }; // Equiv mul_ofnat2_step mul_oneone_step

    let step_d = right_distrib(d, p, one_c, one_c, step);
    // Equiv mul_oneone_step (add (mul one_c step) (mul one_c step))

    let mul_one_step = cmul(d, p, one_c, step);
    let onestep_eq_step = {
        let comm = d.lemma(p.mul_comm, &[one_c, step]);
        let mul_step_one = cmul(d, p, step, one_c);
        let mo = d.lemma(p.mul_one, &[step]);
        d.lemma(p.equiv_trans, &[mul_one_step, mul_step_one, step, comm, mo])
    }; // Equiv mul_one_step step

    let step_e = d.lemma(
        p.add_congr,
        &[
            mul_one_step,
            step,
            mul_one_step,
            step,
            onestep_eq_step,
            onestep_eq_step,
        ],
    ); // Equiv (add mul_one_step mul_one_step) (add step step)

    let add_mos_mos = cadd(d, p, mul_one_step, mul_one_step);
    let step_step = cadd(d, p, step, step);

    let mid1 = d.lemma(
        p.equiv_trans,
        &[
            mul_ofnat2_step,
            mul_oneone_step,
            add_mos_mos,
            step_c,
            step_d,
        ],
    );
    let two_step_eq = d.lemma(
        p.equiv_trans,
        &[mul_ofnat2_step, add_mos_mos, step_step, mid1, step_e],
    ); // Equiv mul_ofnat2_step step_step

    let flipped = esymm(d, p, mul_ofnat2_step, step_step, two_step_eq);
    d.lemma(
        p.equiv_trans,
        &[step_step, mul_ofnat2_step, width, flipped, mcw],
    )
}

// --- the `Exists P' Q', …` target, built generically over the witnesses ----

/// The 6-way right-nested `And` type for witnesses `pp`, `qq`.
fn conj_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    pp: ExprId,
    qq: ExprId,
) -> ExprId {
    let le1 = cle(d, p, cp, pp);
    let le2 = cle(d, p, pp, qq);
    let le3 = cle(d, p, qq, cq);
    let fpp = d.apply(f, &[pp]);
    let le4 = cle(d, p, fpp, eps);
    let neg_eps = cneg(d, p, eps);
    let fqq = d.apply(f, &[qq]);
    let le5 = cle(d, p, neg_eps, fqq);
    let neg_pp = cneg(d, p, pp);
    let diff = cadd(d, p, qq, neg_pp);
    let le6 = equiv(d, p, diff, width_half);
    let and5 = d.and(le5, le6);
    let and4 = d.and(le4, and5);
    let and3 = d.and(le3, and4);
    let and2 = d.and(le2, and3);
    d.and(le1, and2)
}

/// The proof matching [`conj_ty`], given the six proofs in the same order.
fn conj_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    pp: ExprId,
    qq: ExprId,
    h1: ExprId,
    h2: ExprId,
    h3: ExprId,
    h4: ExprId,
    h5: ExprId,
    h6: ExprId,
) -> ExprId {
    let le1 = cle(d, p, cp, pp);
    let le2 = cle(d, p, pp, qq);
    let le3 = cle(d, p, qq, cq);
    let fpp = d.apply(f, &[pp]);
    let le4 = cle(d, p, fpp, eps);
    let neg_eps = cneg(d, p, eps);
    let fqq = d.apply(f, &[qq]);
    let le5 = cle(d, p, neg_eps, fqq);
    let neg_pp = cneg(d, p, pp);
    let diff = cadd(d, p, qq, neg_pp);
    let le6 = equiv(d, p, diff, width_half);

    let p5 = and_intro(d, p, le5, le6, h5, h6);
    let and5ty = d.and(le5, le6);
    let p4 = and_intro(d, p, le4, and5ty, h4, p5);
    let and4ty = d.and(le4, and5ty);
    let p3 = and_intro(d, p, le3, and4ty, h3, p4);
    let and3ty = d.and(le3, and4ty);
    let p2 = and_intro(d, p, le2, and3ty, h2, p3);
    let and2ty = d.and(le2, and3ty);
    and_intro(d, p, le1, and2ty, h1, p2)
}

/// `Exists CReal predicate`, at the `CReal` universe (matching `Nat`'s: both
/// are ordinary `Sort 1` inhabitants, so the same `level_one()` instantiates
/// `Exists`/`Exists.intro` here as at `Nat` — see `archimedean.rs`'s
/// `∃ n : Nat, …` for the identical pattern one type down).
fn cexists_ty(d: &mut IntDev<'_>, p: CRealPrelude, elem_ty: ExprId, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_const, &[elem_ty, pred])
}

fn cexists_intro(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    pred: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let intro_name = p.rat.int.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[elem_ty, pred, witness, proof])
}

/// `fun qq => conj_ty(pp, qq)`, for a fixed `pp` (possibly itself a bound
/// variable, when building the outer predicate's body).
fn inner_pred_lambda(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    carrier: ExprId,
    pp: ExprId,
) -> ExprId {
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let body = conj_ty(d, p, f, cp, cq, eps, width_half, pp, qq);
    d.lam_fv(qq_fv, carrier, body)
}

/// `fun pp => Exists CReal (fun qq => conj_ty(pp, qq))`.
fn outer_pred_lambda(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    carrier: ExprId,
) -> ExprId {
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let inner_pred = inner_pred_lambda(d, p, f, cp, cq, eps, width_half, carrier, pp);
    let inner_exists = cexists_ty(d, p, carrier, inner_pred);
    d.lam_fv(pp_fv, carrier, inner_exists)
}

/// `Exists CReal (fun pp => Exists CReal (fun qq => conj_ty(pp, qq)))` — the
/// full target type of `CReal.ivt_step`'s conclusion.
fn full_exists_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    carrier: ExprId,
) -> ExprId {
    let outer_pred = outer_pred_lambda(d, p, f, cp, cq, eps, width_half, carrier);
    cexists_ty(d, p, carrier, outer_pred)
}

/// A witness proof of [`full_exists_ty`] at concrete `pp_val`, `qq_val`.
fn full_exists_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    carrier: ExprId,
    pp_val: ExprId,
    qq_val: ExprId,
    h1: ExprId,
    h2: ExprId,
    h3: ExprId,
    h4: ExprId,
    h5: ExprId,
    h6: ExprId,
) -> ExprId {
    let inner_pred = inner_pred_lambda(d, p, f, cp, cq, eps, width_half, carrier, pp_val);
    let conj_pf = conj_proof(
        d, p, f, cp, cq, eps, width_half, pp_val, qq_val, h1, h2, h3, h4, h5, h6,
    );
    let inner_proof = cexists_intro(d, p, carrier, inner_pred, qq_val, conj_pf);
    let outer_pred = outer_pred_lambda(d, p, f, cp, cq, eps, width_half, carrier);
    cexists_intro(d, p, carrier, outer_pred, pp_val, inner_proof)
}

// --- the theorem -------------------------------------------------------------

/// `CReal.ivt_step` — see the module documentation for the paper argument.
fn declare_ivt_step(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cp_fv = d.fresh_fvar();
    let cp = d.kernel().fvar(cp_fv);
    let cq_fv = d.fresh_fvar();
    let cq = d.kernel().fvar(cq_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);

    let zero_c = czero(d, p);
    let heps_ty = clt(d, p, zero_c, eps);
    let heps_fv = d.fresh_fvar();
    let heps = d.kernel().fvar(heps_fv);

    let hpq_ty = cle(d, p, cp, cq);
    let hpq_fv = d.fresh_fvar();
    let hpq = d.kernel().fvar(hpq_fv);

    let fp = d.apply(f, &[cp]);
    let hfp_ty = cle(d, p, fp, eps);
    let hfp_fv = d.fresh_fvar();
    let hfp = d.kernel().fvar(hfp_fv);

    let neg_eps = cneg(d, p, eps);
    let fq = d.apply(f, &[cq]);
    let hfq_ty = cle(d, p, neg_eps, fq);
    let hfq_fv = d.fresh_fvar();
    let hfq = d.kernel().fvar(hfq_fv);

    // width, half, step (= width_half)
    let neg_cp = cneg(d, p, cp);
    let width = cadd(d, p, cq, neg_cp);
    let one_nat = d.num(1);
    let (half, half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let width_half = cmul(d, p, width, half);

    let m = cadd(d, p, cp, width_half);

    let width_nonneg = sub_nonneg_of_le(d, p, cp, cq, hpq);
    let step_nonneg = d.lemma(p.mul_nonneg, &[width, half, width_nonneg, half_nonneg]);

    // le P m
    let m_minus_p_eq_step = cancel_right(d, p, cp, width_half);
    // Equiv (add m (neg cp)) width_half
    let m_minus_p_nonneg = {
        let m_minus_p = cadd(d, p, m, neg_cp);
        let flipped = esymm(d, p, m_minus_p, width_half, m_minus_p_eq_step);
        let refl_zero = erefl(d, p, zero_c);
        d.lemma(
            p.le_congr,
            &[
                zero_c,
                zero_c,
                width_half,
                m_minus_p,
                refl_zero,
                flipped,
                step_nonneg,
            ],
        )
    };
    let le_p_m = le_of_nonneg_sub(d, p, cp, m, m_minus_p_nonneg);

    // width relation: Equiv (add width_half width_half) width
    let width_eq_2step = width_eq_two_step(d, p, width, width_half, one_nat);

    // Equiv (add cp width) cq
    let restore = restore_from_width(d, p, cp, cq);

    // Equiv (add m width_half) cq
    let q_eq_m_plus_step = {
        let step_step = cadd(d, p, width_half, width_half);
        let assoc1 = d.lemma(p.add_assoc, &[cp, width_half, width_half]);
        // Equiv (add m width_half) (add cp step_step)
        let cp_step_step = cadd(d, p, cp, step_step);
        let cp_width = cadd(d, p, cp, width);
        let refl_cp = erefl(d, p, cp);
        let step_b = d.lemma(
            p.add_congr,
            &[cp, cp, step_step, width, refl_cp, width_eq_2step],
        );
        // Equiv (add cp step_step) (add cp width)
        let m_width_half = cadd(d, p, m, width_half);
        let mid = d.lemma(
            p.equiv_trans,
            &[m_width_half, cp_step_step, cp_width, assoc1, step_b],
        );
        d.lemma(p.equiv_trans, &[m_width_half, cp_width, cq, mid, restore])
    };

    // le m Q
    let q_minus_m_eq_step = {
        let m_width_half = cadd(d, p, m, width_half);
        let cancel2 = cancel_right(d, p, m, width_half);
        // Equiv (add m_width_half (neg m)) width_half
        let q_eq_reversed = esymm(d, p, m_width_half, cq, q_eq_m_plus_step);
        // Equiv cq m_width_half
        let neg_m = cneg(d, p, m);
        let refl_neg_m = erefl(d, p, neg_m);
        let congr_step = d.lemma(
            p.add_congr,
            &[cq, m_width_half, neg_m, neg_m, q_eq_reversed, refl_neg_m],
        );
        // Equiv (add cq neg_m) (add m_width_half neg_m)
        let q_minus_m = cadd(d, p, cq, neg_m);
        let m_width_half_minus_m = cadd(d, p, m_width_half, neg_m);
        d.lemma(
            p.equiv_trans,
            &[
                q_minus_m,
                m_width_half_minus_m,
                width_half,
                congr_step,
                cancel2,
            ],
        )
    };
    let q_minus_m_nonneg = {
        let neg_m2 = cneg(d, p, m);
        let q_minus_m = cadd(d, p, cq, neg_m2);
        let flipped = esymm(d, p, q_minus_m, width_half, q_minus_m_eq_step);
        let refl_zero2 = erefl(d, p, zero_c);
        d.lemma(
            p.le_congr,
            &[
                zero_c,
                zero_c,
                width_half,
                q_minus_m,
                refl_zero2,
                flipped,
                step_nonneg,
            ],
        )
    };
    let le_m_q = le_of_nonneg_sub(d, p, m, cq, q_minus_m_nonneg);

    // --- the decision ---
    let neg_lt_eps = neg_lt_of_pos(d, p, eps, heps);
    let fm = d.apply(f, &[m]);
    let cotrans = d.lemma(p.lt_cotrans, &[neg_eps, eps, neg_lt_eps, fm]);

    let target_ty = full_exists_ty(d, p, f, cp, cq, eps, width_half, carrier);
    let left_ty = clt(d, p, neg_eps, fm);
    let right_ty = clt(d, p, fm, eps);

    let body = d.or_elim(
        left_ty,
        right_ty,
        target_ty,
        cotrans,
        &|d, hb| {
            // −eps < F m: new bracket [P, m].
            let hb_le = d.lemma(p.le_of_lt, &[neg_eps, fm, hb]);
            let refl_p = d.lemma(p.le_refl, &[cp]);
            full_exists_proof(
                d,
                p,
                f,
                cp,
                cq,
                eps,
                width_half,
                carrier,
                cp,
                m,
                refl_p,
                le_p_m,
                le_m_q,
                hfp,
                hb_le,
                m_minus_p_eq_step,
            )
        },
        &|d, ha| {
            // F m < eps: new bracket [m, Q].
            let ha_le = d.lemma(p.le_of_lt, &[fm, eps, ha]);
            let refl_q = d.lemma(p.le_refl, &[cq]);
            full_exists_proof(
                d,
                p,
                f,
                cp,
                cq,
                eps,
                width_half,
                carrier,
                m,
                cq,
                le_p_m,
                le_m_q,
                refl_q,
                ha_le,
                hfq,
                q_minus_m_eq_step,
            )
        },
    );

    let value = {
        let with_hfq = d.lam_fv(hfq_fv, hfq_ty, body);
        let with_hfp = d.lam_fv(hfp_fv, hfp_ty, with_hfq);
        let with_hpq = d.lam_fv(hpq_fv, hpq_ty, with_hfp);
        let with_heps = d.lam_fv(heps_fv, heps_ty, with_hpq);
        let with_eps = d.lam_fv(eps_fv, carrier, with_heps);
        let with_cq = d.lam_fv(cq_fv, carrier, with_eps);
        let with_cp = d.lam_fv(cp_fv, carrier, with_cq);
        d.lam_fv(f_fv, fn_ty, with_cp)
    };
    let ty = {
        let with_hfq = d.arrow(hfq_ty, target_ty);
        let with_hfp = d.arrow(hfp_ty, with_hfq);
        let with_hpq = d.arrow(hpq_ty, with_hfp);
        let with_heps = d.arrow(heps_ty, with_hpq);
        let with_eps = d.pi_fv(eps_fv, carrier, with_heps);
        let with_cq = d.pi_fv(cq_fv, carrier, with_eps);
        let with_cp = d.pi_fv(cp_fv, carrier, with_cq);
        d.pi_fv(f_fv, fn_ty, with_cp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_step,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_iter` -- `ivt_step` iterated `n` times.
//
// See `CRealPrelude::ivt_iter`'s own doc comment in `creal.rs` for the
// statement and the width-tracking argument (`pow`'s ι-reduction, no explicit
// `pow_succ`/`pow_zero` lemma application). What follows is the plumbing:
// `full_exists_proof`/`conj_ty` above only ever PRODUCE the nested
// `Exists`/`And` shape `ivt_step` returns; the induction step here must also
// CONSUME one (to unpack the inductive hypothesis, and again to unpack
// `ivt_step`'s own result) -- `cexists_elim`/`with_ivt_witness` below are the
// mirror image of `cexists_ty`/`cexists_intro`/`full_exists_proof`.
// =============================================================================

/// `Exists elem_ty predicate`, eliminated into `target` (which must not
/// mention the witness) via a `minor : ∀ x, predicate x → target`. Generic in
/// `elem_ty` -- unlike
/// [`exists_elim`](crate::int_prelude::ops::exists_elim), which is hardcoded
/// to `Nat` -- because this file's existentials range over `CReal`.
fn cexists_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let one = d.level_one();
    let exists_name = p.rat.int.logic.exists_;
    let exists_const = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists_const, &[elem_ty, predicate]);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, exists_ty, target)
    };
    let rec_name = p.rat.int.logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[elem_ty, predicate, motive, minor, witness])
}

/// Eliminate `witness : full_exists_ty(f, cp, cq, eps, width, carrier)` into
/// `target` (which must not mention the two witnesses `pp, qq`), given a
/// continuation building the proof of `target` from `pp, qq` and the six
/// conjuncts, in [`conj_ty`]'s order: `le cp pp`, `le pp qq`, `le qq cq`,
/// `le (F pp) eps`, `le (neg eps) (F qq)`, `Equiv (add qq (neg pp)) width`.
///
/// The mirror image of [`full_exists_proof`]: that function BUILDS this
/// nested `Exists`/`And` shape; this one CONSUMES it. Every minor premise
/// below binds both the witness and the hypothesis it introduces, per this
/// module's own hard constraint on nested `Exists.rec` chains -- dropping
/// either produces `UnboundFVar` only at full re-verification.
/// `(d, pp, qq, h1, h2, h3, h4, h5, h6) -> proof of target`, the continuation
/// [`with_ivt_witness`] hands the six unpacked conjuncts to.
type IvtWitnessCont<'a> = dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId
    + 'a;

#[allow(clippy::too_many_arguments)]
fn with_ivt_witness(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width: ExprId,
    carrier: ExprId,
    target: ExprId,
    witness: ExprId,
    cont: &IvtWitnessCont<'_>,
) -> ExprId {
    let outer_pred = outer_pred_lambda(d, p, f, cp, cq, eps, width, carrier);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let inner_pred_pp = inner_pred_lambda(d, p, f, cp, cq, eps, width, carrier, pp);
    let exists_inner_ty = cexists_ty(d, p, carrier, inner_pred_pp);

    let outer_minor = {
        let h_inner_fv = d.fresh_fvar();
        let h_inner = d.kernel().fvar(h_inner_fv);

        let inner_minor = {
            let qq_fv = d.fresh_fvar();
            let qq = d.kernel().fvar(qq_fv);

            let le1 = cle(d, p, cp, pp);
            let le2 = cle(d, p, pp, qq);
            let le3 = cle(d, p, qq, cq);
            let fpp = d.apply(f, &[pp]);
            let le4 = cle(d, p, fpp, eps);
            let neg_eps_l = cneg(d, p, eps);
            let fqq = d.apply(f, &[qq]);
            let le5 = cle(d, p, neg_eps_l, fqq);
            let neg_pp = cneg(d, p, pp);
            let diff = cadd(d, p, qq, neg_pp);
            let le6 = equiv(d, p, diff, width);
            let and5 = d.and(le5, le6);
            let and4 = d.and(le4, and5);
            let and3 = d.and(le3, and4);
            let and2 = d.and(le2, and3);
            let conj = d.and(le1, and2);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h1 = d.and_left(le1, and2, h);
            let rest2 = d.and_right(le1, and2, h);
            let h2 = d.and_left(le2, and3, rest2);
            let rest3 = d.and_right(le2, and3, rest2);
            let h3 = d.and_left(le3, and4, rest3);
            let rest4 = d.and_right(le3, and4, rest3);
            let h4 = d.and_left(le4, and5, rest4);
            let rest5 = d.and_right(le4, and5, rest4);
            let h5 = d.and_left(le5, le6, rest5);
            let h6 = d.and_right(le5, le6, rest5);

            let body = cont(d, pp, qq, h1, h2, h3, h4, h5, h6);
            let with_h = d.lam_fv(h_fv, conj, body);
            d.lam_fv(qq_fv, carrier, with_h)
        };

        let inner_elim = cexists_elim(d, p, carrier, inner_pred_pp, target, h_inner, inner_minor);
        let with_h_inner = d.lam_fv(h_inner_fv, exists_inner_ty, inner_elim);
        d.lam_fv(pp_fv, carrier, with_h_inner)
    };

    cexists_elim(d, p, carrier, outer_pred, target, witness, outer_minor)
}

/// `mul w0 (pow half x)` -- the width at index `x`.
fn ivt_iter_width(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w0: ExprId,
    half: ExprId,
    x: ExprId,
) -> ExprId {
    let px = d.const_app(p.pow, &[half, x]);
    cmul(d, p, w0, px)
}

/// `full_exists_ty(f, cp0, cq0, eps, ivt_iter_width(w0, half, x), carrier)` --
/// the invariant proved by induction on `x`.
#[allow(clippy::too_many_arguments)]
fn ivt_iter_motive(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp0: ExprId,
    cq0: ExprId,
    eps: ExprId,
    w0: ExprId,
    half: ExprId,
    carrier: ExprId,
    x: ExprId,
) -> ExprId {
    let width_x = ivt_iter_width(d, p, w0, half, x);
    full_exists_ty(d, p, f, cp0, cq0, eps, width_x, carrier)
}

/// The base case (`n = 0`): the bracket `[P0, Q0]` itself, unmoved. The width
/// obligation is `Equiv w0 (mul w0 (pow half zero))`, and `pow half zero`
/// ι-reduces to `one`, so the reverse of [`CRealPrelude::mul_one`] suffices.
#[allow(clippy::too_many_arguments)]
fn ivt_iter_base(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp0: ExprId,
    cq0: ExprId,
    eps: ExprId,
    w0: ExprId,
    half: ExprId,
    carrier: ExprId,
    hpq: ExprId,
    hfp: ExprId,
    hfq: ExprId,
) -> ExprId {
    let zero_nat = d.num(0);
    let width0 = ivt_iter_width(d, p, w0, half, zero_nat);
    let h1 = d.lemma(p.le_refl, &[cp0]);
    let h3 = d.lemma(p.le_refl, &[cq0]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let mul_w0_one = cmul(d, p, w0, one_c);
    let mo = d.lemma(p.mul_one, &[w0]); // Equiv (mul w0 one) w0
    let h6 = esymm(d, p, mul_w0_one, w0, mo); // Equiv w0 (mul w0 one), defeq to Equiv w0 width0
    full_exists_proof(
        d, p, f, cp0, cq0, eps, width0, carrier, cp0, cq0, h1, hpq, h3, hfp, hfq, h6,
    )
}

/// The induction step: unpack the inductive hypothesis at index `j` into a
/// bracket `[pp, qq]`, apply `ivt_step` once, unpack ITS result into `[pp2,
/// qq2]`, and re-derive all six invariants against the FIXED `cp0, cq0` (the
/// outer-range facts chain through `le_trans`; the width fact chains through
/// `mul_congr` against the inductive hypothesis's own width equation, then
/// `mul_assoc` to regroup `mul (mul w0 (pow half j)) half` into `mul w0 (mul
/// (pow half j) half)` -- defeq to `mul w0 (pow half (succ j))`, per `pow`'s
/// own ι-reduction, so no `pow_succ` lemma application is needed).
#[allow(clippy::too_many_arguments)]
fn ivt_iter_step(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp0: ExprId,
    cq0: ExprId,
    eps: ExprId,
    w0: ExprId,
    half: ExprId,
    carrier: ExprId,
    heps: ExprId,
    j: ExprId,
    ih: ExprId,
) -> ExprId {
    let width_j = ivt_iter_width(d, p, w0, half, j);
    let succ_j = d.succ(j);
    let target = ivt_iter_motive(d, p, f, cp0, cq0, eps, w0, half, carrier, succ_j);

    with_ivt_witness(
        d,
        p,
        f,
        cp0,
        cq0,
        eps,
        width_j,
        carrier,
        target,
        ih,
        &|d, pp, qq, h1, h2, h3, h4, h5, h6| {
            let step_result = d.lemma(p.ivt_step, &[f, pp, qq, eps, heps, h2, h4, h5]);
            let neg_pp = cneg(d, p, pp);
            let gap = cadd(d, p, qq, neg_pp);
            let step_width = cmul(d, p, gap, half);

            with_ivt_witness(
                d,
                p,
                f,
                pp,
                qq,
                eps,
                step_width,
                carrier,
                target,
                step_result,
                &|d, pp2, qq2, g1, g2, g3, g4, g5, g6| {
                    let big_h1 = d.lemma(p.le_trans, &[cp0, pp, pp2, h1, g1]);
                    let big_h3 = d.lemma(p.le_trans, &[qq2, qq, cq0, g3, h3]);

                    // width chain: step_width ~ mul width_j half [mul_congr
                    // via h6] ~ mul w0 (mul (pow half j) half) [mul_assoc].
                    let pow_half_j = d.const_app(p.pow, &[half, j]);
                    let refl_half = erefl(d, p, half);
                    let congr_step =
                        d.lemma(p.mul_congr, &[gap, width_j, half, half, h6, refl_half]);
                    let mul_width_j_half = cmul(d, p, width_j, half);
                    let assoc_step = d.lemma(p.mul_assoc, &[w0, pow_half_j, half]);
                    let inner_half = cmul(d, p, pow_half_j, half);
                    let final_width = cmul(d, p, w0, inner_half);
                    let width_chain = d.lemma(
                        p.equiv_trans,
                        &[
                            step_width,
                            mul_width_j_half,
                            final_width,
                            congr_step,
                            assoc_step,
                        ],
                    );
                    let neg_pp2 = cneg(d, p, pp2);
                    let gap2 = cadd(d, p, qq2, neg_pp2);
                    let big_h6 = d.lemma(
                        p.equiv_trans,
                        &[gap2, step_width, final_width, g6, width_chain],
                    );

                    full_exists_proof(
                        d,
                        p,
                        f,
                        cp0,
                        cq0,
                        eps,
                        final_width,
                        carrier,
                        pp2,
                        qq2,
                        big_h1,
                        g2,
                        big_h3,
                        g4,
                        g5,
                        big_h6,
                    )
                },
            )
        },
    )
}

/// `CReal.ivt_iter` -- see [`CRealPrelude::ivt_iter`]'s doc comment for the
/// statement and [`ivt_iter_step`] for the induction step's argument.
fn declare_ivt_iter(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cp0_fv = d.fresh_fvar();
    let cp0 = d.kernel().fvar(cp0_fv);
    let cq0_fv = d.fresh_fvar();
    let cq0 = d.kernel().fvar(cq0_fv);
    let eps_fv = d.fresh_fvar();
    let eps = d.kernel().fvar(eps_fv);

    let zero_c = czero(d, p);
    let heps_ty = clt(d, p, zero_c, eps);
    let heps_fv = d.fresh_fvar();
    let heps = d.kernel().fvar(heps_fv);

    let hpq_ty = cle(d, p, cp0, cq0);
    let hpq_fv = d.fresh_fvar();
    let hpq = d.kernel().fvar(hpq_fv);

    let fp0 = d.apply(f, &[cp0]);
    let hfp_ty = cle(d, p, fp0, eps);
    let hfp_fv = d.fresh_fvar();
    let hfp = d.kernel().fvar(hfp_fv);

    let neg_eps = cneg(d, p, eps);
    let fq0 = d.apply(f, &[cq0]);
    let hfq_ty = cle(d, p, neg_eps, fq0);
    let hfq_fv = d.fresh_fvar();
    let hfq = d.kernel().fvar(hfq_fv);

    let one_nat = d.num(1);
    let (half, _half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let neg_cp0 = cneg(d, p, cp0);
    let w0 = cadd(d, p, cq0, neg_cp0);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        ivt_iter_motive(d, p, f, cp0, cq0, eps, w0, half, carrier, x)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        ivt_iter_base(d, p, f, cp0, cq0, eps, w0, half, carrier, hpq, hfp, hfq)
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        ivt_iter_step(d, p, f, cp0, cq0, eps, w0, half, carrier, heps, j, ih)
    };

    let final_proof = d.induct(&motive, &base, &step, n);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, final_proof);
        let with_hfq = d.lam_fv(hfq_fv, hfq_ty, with_n);
        let with_hfp = d.lam_fv(hfp_fv, hfp_ty, with_hfq);
        let with_hpq = d.lam_fv(hpq_fv, hpq_ty, with_hfp);
        let with_heps = d.lam_fv(heps_fv, heps_ty, with_hpq);
        let with_eps = d.lam_fv(eps_fv, carrier, with_heps);
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_eps);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let motive_n = motive(d, n);
        let stmt_n = d.pi_fv(n_fv, nat, motive_n);
        let with_hfq = d.arrow(hfq_ty, stmt_n);
        let with_hfp = d.arrow(hfp_ty, with_hfq);
        let with_hpq = d.arrow(hpq_ty, with_hfp);
        let with_heps = d.arrow(heps_ty, with_hpq);
        let with_eps = d.pi_fv(eps_fv, carrier, with_heps);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_eps);
        let with_cp0 = d.pi_fv(cp0_fv, carrier, with_cq0);
        d.pi_fv(f_fv, fn_ty, with_cp0)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_iter,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_approx` -- the closing combination: `ivt_iter` against
// `UniformlyContinuousOn` and the Archimedean property (via `CReal.bound`,
// not `CReal.archimedean`'s `Exists` wrapper), plus
// `CReal.pow_half_le_natDivSucc`. See the module documentation's "Addendum"
// and `CRealPrelude::ivt_approx`'s own doc comment for the choice of `n`,
// `delta` and `bisect_n`.
// =============================================================================

/// `Equiv (neg zero) zero`. Verbatim reproduction of `series.rs::neg_zero_equiv`
/// (private there, and reused by `power.rs` the same way).
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]); // add nz zero ~ nz
    let step1 = esymm(d, p, padded, nz, h1); // nz ~ padded
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]); // padded ~ flipped
    let h3 = d.lemma(p.add_neg, &[zero_c]); // flipped ~ zero
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// From `h : le zero x`, `le (neg x) zero` -- negation of a nonneg quantity
/// is nonpositive, via [`neg_zero_equiv`].
fn neg_nonpos_of_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, h: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let step = d.lemma(p.neg_le_neg, &[zero_c, x, h]); // le nx (neg zero)
    let nz_eq_zero = neg_zero_equiv(d, p);
    let refl_nx = erefl(d, p, nx);
    let neg_zero_c = cneg(d, p, zero_c);
    d.lemma(
        p.le_congr,
        &[nx, nx, neg_zero_c, zero_c, refl_nx, nz_eq_zero, step],
    )
}

/// `Equiv (add (add x (neg y)) y) x` -- adding back what was subtracted.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let xy = cadd(d, p, x, ny); // x - y
    let start = cadd(d, p, xy, y); // (x-y)+y
    let yxy = cadd(d, p, y, xy); // y+(x-y)
    let comm = d.lemma(p.add_comm, &[xy, y]); // Equiv start yxy
    let restored = restore_from_width(d, p, y, x); // Equiv yxy x
    echain(d, p, start, &[(yxy, comm), (x, restored)])
}

/// `n := succ(2*e)`, `sgn_eps := ofRat (natDivSucc 1 n)`, and a proof `lt
/// zero sgn_eps`. This is both the bisection sign-slack and the continuity
/// output accuracy at index `n` -- chosen so `sgn_eps + sgn_eps ~ ofRat
/// (natDivSucc 1 e)` (see [`sgn_eps_double_eq_target`]).
fn sgn_eps_of(d: &mut IntDev<'_>, p: CRealPrelude, e: ExprId) -> (ExprId, ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let two_nat = d.num(2);
    let two_e = d.mul(two_nat, e);
    let n = d.succ(two_e);
    let sgn_eps_rat = div_succ(d, p, 1, n);
    let sgn_eps = embed(d, p, sgn_eps_rat);

    let one_nat = d.num(1);
    let le11 = {
        let np = d.prelude();
        d.const_app(np.le_refl, &[one_nat])
    };
    let rat_pos = d.lemma(rat.nat_div_succ_pos, &[one_nat, n, le11]);
    let sgn_eps_pos = d.lemma(p.of_rat_pos, &[sgn_eps_rat, rat_pos]);
    (n, sgn_eps, sgn_eps_rat, sgn_eps_pos)
}

/// `Equiv (add sgn_eps sgn_eps) (ofRat (natDivSucc 1 e))`, given `n :=
/// succ(2*e)` and `sgn_eps_rat := natDivSucc 1 n` (see [`sgn_eps_of`]).
/// `Rat.natDivSucc_add` fuses the two summands to `natDivSucc (1+1) n`; `1+1`
/// and `2` are both closed numerals, so `Eq.refl` bridges them by
/// ι-reduction alone; `n`'s own shape `succ(2*e)` then matches
/// `Rat.natDivSucc_halve`'s index exactly, folding straight to `natDivSucc 1
/// e`. Returns `(natDivSucc 1 e, proof)`.
fn sgn_eps_double_eq_target(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    e: ExprId,
    n: ExprId,
    sgn_eps: ExprId,
    sgn_eps_rat: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);

    let sum_rat = radd(d, sgn_eps_rat, sgn_eps_rat);
    let eq_add = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, n]);
    let sum11 = d.add(one_nat, one_nat);
    let natdiv_11_n = d.const_app(rat.nat_div_succ, &[sum11, n]);
    let natdiv_2_n = d.const_app(rat.nat_div_succ, &[two_nat, n]);
    // `sum11` (`Nat.add one_nat one_nat`) ι-reduces to `two_nat`: both are
    // closed numerals, so `Eq.refl two_nat` also proves `Eq sum11 two_nat`
    // by defeq at the final kernel check.
    let h_11_eq_2 = d.refl(two_nat);
    let eq_11_to_2 = nat_eq_to_rat(d, sum11, two_nat, h_11_eq_2, &|d, x| {
        d.const_app(rat.nat_div_succ, &[x, n])
    });

    let target_e_rat = div_succ(d, p, 1, e);
    let eq_halve = d.lemma(rat.nat_div_succ_halve, &[e]);

    let sum_creal = cadd(d, p, sgn_eps, sgn_eps);
    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[sum_creal, oft])
    };
    let of_rat_add_proof = d.lemma(p.of_rat_add, &[sgn_eps_rat, sgn_eps_rat]);
    let step_a = rat_eq_rewrite(d, sum_rat, natdiv_11_n, eq_add, of_rat_add_proof, &motive);
    let step_b = rat_eq_rewrite(d, natdiv_11_n, natdiv_2_n, eq_11_to_2, step_a, &motive);
    let step_c = rat_eq_rewrite(d, natdiv_2_n, target_e_rat, eq_halve, step_b, &motive);
    (target_e_rat, step_c)
}

/// Given `w0` (nonneg) and `delta : Nat`, compute a bisection depth
/// `bisect_n`, the width term `mul w0 (pow half bisect_n)`, the target bound
/// `ofRat (natDivSucc 1 delta)` (with its own nonnegativity), and a proof
/// that the width term is `le` the target.
///
/// `bisect_n := big_m * delta + magnitude`, `magnitude := CReal.bound w0`,
/// `big_m := succ magnitude` -- `Rat.natDivSucc_scale`'s own `(c+1)*m+c`
/// index shape, chosen so `big_m * natDivSucc 1 bisect_n = natDivSucc 1
/// delta` is an EQUALITY, not merely a bound. `CReal.bound` is a total
/// computable projection, so `le w0 (ofRat (natDivSucc big_m 0))` is
/// reproduced directly from [`super::CRealPrelude::bound_within`] -- the
/// non-`Exists` core of [`super::CRealPrelude::archimedean`]'s own
/// construction (`archimedean.rs`, out of this file's edit boundary) -- with
/// no `Exists.rec` needed to choose `bisect_n`.
fn width_le_via_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    w0: ExprId,
    w0_nonneg: ExprId,
    delta: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let (half, _half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);

    let magnitude = d.const_app(p.bound, &[w0]);
    let big_m = d.succ(magnitude);
    let target_rat = d.const_app(rat.nat_div_succ, &[big_m, zero_nat]);
    let m_creal = embed(d, p, target_rat);

    // `le w0 m_creal`, reproduced directly from `bound_within` -- the
    // non-`Exists` core of `archimedean::declare_archimedean_property`'s own
    // `le_proof`.
    let w0_le_m = {
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let point = sample(d, p, w0, k);
        let bw = d.lemma(p.bound_within, &[w0, k]);
        let (_, upper) = halves(d, p, point, target_rat, bw);

        let two_nat = d.num(2);
        let bound2 = d.const_app(rat.nat_div_succ, &[two_nat, k]);
        let nonneg2 = d.lemma(rat.zero_le_nat_div_succ, &[two_nat, k]);

        let zero = rzero(d, rat);
        let target_refl = d.lemma(rat.le_refl, &[target_rat]);
        let widened = d.lemma(
            rat.add_le_add,
            &[target_rat, target_rat, zero, bound2, target_refl, nonneg2],
        );
        let padded_target = radd(d, target_rat, zero);
        let sum = radd(d, target_rat, bound2);
        let trim = d.lemma(rat.add_zero, &[target_rat]);
        let target_le_sum = rat_eq_rewrite(d, padded_target, target_rat, trim, widened, &|d, t| {
            rle(d, rat, t, sum)
        });
        let chained = d.lemma(
            rat.le_trans,
            &[point, target_rat, sum, upper, target_le_sum],
        );
        let at_index = d.lemma(rat.sub_le_of_le, &[point, target_rat, bound2, chained]);
        d.lam_fv(k_fv, nat, at_index)
    };

    let scaled = d.mul(big_m, delta);
    let bisect_n = d.add(scaled, magnitude);

    let (bound_creal_n, bound_creal_n_nonneg) = nonneg_rat_bound(d, p, 1, bisect_n);
    let bound_rat_n = div_succ(d, p, 1, bisect_n);

    let pow_half_n = d.const_app(p.pow, &[half, bisect_n]);
    let pow_le = d.lemma(p.pow_half_le_nat_div_succ, &[bisect_n]);

    let mul_w0_pow = cmul(d, p, w0, pow_half_n);
    let mul_w0_bcn = cmul(d, p, w0, bound_creal_n);
    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[w0, pow_half_n, bound_creal_n, w0_nonneg, pow_le],
    );

    let step2_pre = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[bound_creal_n, w0, m_creal, bound_creal_n_nonneg, w0_le_m],
    );
    let mul_bcn_w0 = cmul(d, p, bound_creal_n, w0);
    let mul_bcn_m = cmul(d, p, bound_creal_n, m_creal);
    let mul_m_bcn = cmul(d, p, m_creal, bound_creal_n);
    let comm_left = d.lemma(p.mul_comm, &[bound_creal_n, w0]);
    let comm_right = d.lemma(p.mul_comm, &[bound_creal_n, m_creal]);
    let step2 = d.lemma(
        p.le_congr,
        &[
            mul_bcn_w0, mul_w0_bcn, mul_bcn_m, mul_m_bcn, comm_left, comm_right, step2_pre,
        ],
    );

    let (target_creal, target_nonneg) = nonneg_rat_bound(d, p, 1, delta);
    let target_delta_rat = div_succ(d, p, 1, delta);

    let rat_prod = rmul(d, target_rat, bound_rat_n);
    let mul_bigm_1 = d.mul(big_m, one_nat);
    let natdiv_mul_bigm1_n = d.const_app(rat.nat_div_succ, &[mul_bigm_1, bisect_n]);
    let natdiv_bigm_n = d.const_app(rat.nat_div_succ, &[big_m, bisect_n]);

    let eq_mul = d.lemma(rat.nat_div_succ_mul, &[big_m, one_nat, bisect_n]);
    let mul_one_eq = d.lemma(rat.int.nat.mul_one, &[big_m]);
    let eq_fold = nat_eq_to_rat(d, mul_bigm_1, big_m, mul_one_eq, &|d, x| {
        d.const_app(rat.nat_div_succ, &[x, bisect_n])
    });
    let eq_scale = d.lemma(rat.nat_div_succ_scale, &[magnitude, delta]);

    let of_rat_mul_proof = d.lemma(p.of_rat_mul, &[target_rat, bound_rat_n]);
    let motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[mul_m_bcn, oft])
    };
    let step_a = rat_eq_rewrite(
        d,
        rat_prod,
        natdiv_mul_bigm1_n,
        eq_mul,
        of_rat_mul_proof,
        &motive,
    );
    let step_b = rat_eq_rewrite(
        d,
        natdiv_mul_bigm1_n,
        natdiv_bigm_n,
        eq_fold,
        step_a,
        &motive,
    );
    let step_c = rat_eq_rewrite(
        d,
        natdiv_bigm_n,
        target_delta_rat,
        eq_scale,
        step_b,
        &motive,
    );
    // step_c : Equiv mul_m_bcn target_creal

    let le_trans_12 = d.lemma(
        p.le_trans,
        &[mul_w0_pow, mul_w0_bcn, mul_m_bcn, step1, step2],
    );
    let refl_lhs = erefl(d, p, mul_w0_pow);
    let final_le = d.lemma(
        p.le_congr,
        &[
            mul_w0_pow,
            mul_w0_pow,
            mul_m_bcn,
            target_creal,
            refl_lhs,
            step_c,
            le_trans_12,
        ],
    );

    (bisect_n, mul_w0_pow, target_creal, target_nonneg, final_le)
}

/// `And (le a x) (And (le x b) (le (abs (f x)) (ofRat (natDivSucc 1 e))))`.
fn approx_pred_body(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    target_e_rat: ExprId,
    x: ExprId,
) -> ExprId {
    let le1 = cle(d, p, a, x);
    let le2 = cle(d, p, x, b);
    let fx = d.apply(f, &[x]);
    let absfx = d.const_app(p.abs, &[fx]);
    let target_e = embed(d, p, target_e_rat);
    let le3 = cle(d, p, absfx, target_e);
    let and2 = d.and(le2, le3);
    d.and(le1, and2)
}

fn approx_pred_lambda(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    target_e_rat: ExprId,
    carrier: ExprId,
) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = approx_pred_body(d, p, f, a, b, target_e_rat, x);
    d.lam_fv(x_fv, carrier, body)
}

/// `Exists CReal (fun x => approx_pred_body(f,a,b,e,x))`.
fn approx_exists_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    target_e_rat: ExprId,
    carrier: ExprId,
) -> ExprId {
    let pred = approx_pred_lambda(d, p, f, a, b, target_e_rat, carrier);
    cexists_ty(d, p, carrier, pred)
}

/// A witness proof of [`approx_exists_ty`] at concrete `x`.
#[allow(clippy::too_many_arguments)]
fn approx_exists_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    target_e_rat: ExprId,
    carrier: ExprId,
    x: ExprId,
    h1: ExprId,
    h2: ExprId,
    h3: ExprId,
) -> ExprId {
    let le2 = cle(d, p, x, b);
    let fx = d.apply(f, &[x]);
    let absfx = d.const_app(p.abs, &[fx]);
    let target_e = embed(d, p, target_e_rat);
    let le3 = cle(d, p, absfx, target_e);
    let and2ty = d.and(le2, le3);
    let p2 = and_intro(d, p, le2, le3, h2, h3);
    let le1 = cle(d, p, a, x);
    let p1 = and_intro(d, p, le1, and2ty, h1, p2);
    let pred = approx_pred_lambda(d, p, f, a, b, target_e_rat, carrier);
    cexists_intro(d, p, carrier, pred, x, p1)
}

/// `CReal.ivt_approx` -- see [`super::CRealPrelude::ivt_approx`]'s doc
/// comment for the statement and this module's documentation "Addendum" for
/// how `n`, `delta`, `bisect_n` are chosen.
fn declare_ivt_approx(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let uc_ty_ab = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);

    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let zero_c = czero(d, p);
    let fa = d.apply(f, &[a]);
    let hfa_ty = cle(d, p, fa, zero_c);
    let hfa_fv = d.fresh_fvar();
    let hfa = d.kernel().fvar(hfa_fv);

    let fb = d.apply(f, &[b]);
    let hfb_ty = cle(d, p, zero_c, fb);
    let hfb_fv = d.fresh_fvar();
    let hfb = d.kernel().fvar(hfb_fv);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    // --- `n`, `sgn_eps`, `delta`, `bisect_n` ---------------------------------
    let (n, sgn_eps, sgn_eps_rat, sgn_eps_pos) = sgn_eps_of(d, p, e);
    let (target_e_rat, double_eq_target) =
        sgn_eps_double_eq_target(d, p, e, n, sgn_eps, sgn_eps_rat);

    let sgn_eps_nonneg = d.lemma(p.le_of_lt, &[zero_c, sgn_eps, sgn_eps_pos]);
    let hfp = d.lemma(p.le_trans, &[fa, zero_c, sgn_eps, hfa, sgn_eps_nonneg]);
    let neg_sgn_eps = cneg(d, p, sgn_eps);
    let neg_sgn_eps_le_zero = neg_nonpos_of_nonneg(d, p, sgn_eps, sgn_eps_nonneg);
    let hfq = d.lemma(
        p.le_trans,
        &[neg_sgn_eps, zero_c, fb, neg_sgn_eps_le_zero, hfb],
    );

    let mod_fn = d.const_app(p.uc_modulus, &[f, a, b, huc]);
    let delta = d.apply(mod_fn, &[n]);

    let neg_a = cneg(d, p, a);
    let w0 = cadd(d, p, b, neg_a);
    let w0_nonneg = sub_nonneg_of_le(d, p, a, b, hab);
    let (bisect_n, width_term, target_creal, target_nonneg, width_le) =
        width_le_via_bound(d, p, w0, w0_nonneg, delta);

    let iter_at_n = d.lemma(
        p.ivt_iter,
        &[f, a, b, sgn_eps, sgn_eps_pos, hab, hfp, hfq, bisect_n],
    );

    let target_ty = approx_exists_ty(d, p, f, a, b, target_e_rat, carrier);

    let body = with_ivt_witness(
        d,
        p,
        f,
        a,
        b,
        sgn_eps,
        width_term,
        carrier,
        target_ty,
        iter_at_n,
        &|d, pp2, qq2, h1, h2, h3, h4, h5, h6| {
            let neg_pp2 = cneg(d, p, pp2);
            let diff = cadd(d, p, qq2, neg_pp2);

            // `le diff target_creal`, from `h6 : Equiv diff width_term` and
            // `width_le : le width_term target_creal`.
            let diff_le_t = {
                let h6_symm = esymm(d, p, diff, width_term, h6);
                let refl_target = erefl(d, p, target_creal);
                d.lemma(
                    p.le_congr,
                    &[
                        width_term,
                        diff,
                        target_creal,
                        target_creal,
                        h6_symm,
                        refl_target,
                        width_le,
                    ],
                )
            };
            let neg_diff_le_t = {
                let diff_nonneg = sub_nonneg_of_le(d, p, pp2, qq2, h2);
                let neg_diff_le_zero = neg_nonpos_of_nonneg(d, p, diff, diff_nonneg);
                let neg_diff = cneg(d, p, diff);
                d.lemma(
                    p.le_trans,
                    &[
                        neg_diff,
                        zero_c,
                        target_creal,
                        neg_diff_le_zero,
                        target_nonneg,
                    ],
                )
            };
            let abs_diff_le_t = d.lemma(p.abs_le, &[diff, target_creal, diff_le_t, neg_diff_le_t]);

            let range_a_qq2 = d.lemma(p.le_trans, &[a, pp2, qq2, h1, h2]);
            let range_pp2_b = d.lemma(p.le_trans, &[pp2, qq2, b, h2, h3]);

            let uc_spec_term = d.const_app(p.uc_spec, &[f, a, b, huc]);
            let uc_concl = d.apply(
                uc_spec_term,
                &[n, qq2, pp2, range_a_qq2, h3, h1, range_pp2_b, abs_diff_le_t],
            );
            // uc_concl : le (abs (add (f qq2) (neg (f pp2)))) sgn_eps

            let f_qq2 = d.apply(f, &[qq2]);
            let f_pp2 = d.apply(f, &[pp2]);
            let neg_f_pp2 = cneg(d, p, f_pp2);
            let diff_f = cadd(d, p, f_qq2, neg_f_pp2);
            let abs_diff_f = d.const_app(p.abs, &[diff_f]);

            let le_abs_self_proof = d.lemma(p.le_abs_self, &[diff_f]);
            let diff_f_le_eps = d.lemma(
                p.le_trans,
                &[diff_f, abs_diff_f, sgn_eps, le_abs_self_proof, uc_concl],
            );

            // `f_qq2 ~ diff_f + f_pp2 ≤ sgn_eps + f_pp2 ≤ sgn_eps + sgn_eps
            // ~ target_e`.
            let diff_f_fpp2 = cadd(d, p, diff_f, f_pp2);
            let eps_fpp2 = cadd(d, p, sgn_eps, f_pp2);
            let eps_eps = cadd(d, p, sgn_eps, sgn_eps);
            let target_e_creal = embed(d, p, target_e_rat);

            let refl_f_pp2 = d.lemma(p.le_refl, &[f_pp2]);
            let add_le_1 = d.lemma(
                p.add_le_add,
                &[diff_f, sgn_eps, f_pp2, f_pp2, diff_f_le_eps, refl_f_pp2],
            );
            let cancel_eq = add_sub_cancel(d, p, f_qq2, f_pp2); // Equiv diff_f_fpp2 f_qq2
            let refl_eps_fpp2 = erefl(d, p, eps_fpp2);
            let add_le_1_congr = d.lemma(
                p.le_congr,
                &[
                    diff_f_fpp2,
                    f_qq2,
                    eps_fpp2,
                    eps_fpp2,
                    cancel_eq,
                    refl_eps_fpp2,
                    add_le_1,
                ],
            );
            let refl_sgn_eps_1 = d.lemma(p.le_refl, &[sgn_eps]);
            let add_le_2 = d.lemma(
                p.add_le_add,
                &[sgn_eps, sgn_eps, f_pp2, sgn_eps, refl_sgn_eps_1, h4],
            );
            let upper_pre = d.lemma(
                p.le_trans,
                &[f_qq2, eps_fpp2, eps_eps, add_le_1_congr, add_le_2],
            );
            let refl_f_qq2 = erefl(d, p, f_qq2);
            let f_qq2_le_target = d.lemma(
                p.le_congr,
                &[
                    f_qq2,
                    f_qq2,
                    eps_eps,
                    target_e_creal,
                    refl_f_qq2,
                    double_eq_target,
                    upper_pre,
                ],
            );

            let sgn_eps_le_target = {
                let refl_sgn_eps_2 = d.lemma(p.le_refl, &[sgn_eps]);
                let add_le = d.lemma(
                    p.add_le_add,
                    &[
                        sgn_eps,
                        sgn_eps,
                        zero_c,
                        sgn_eps,
                        refl_sgn_eps_2,
                        sgn_eps_nonneg,
                    ],
                );
                let sgn_eps_zero = cadd(d, p, sgn_eps, zero_c);
                let add_zero_eq = d.lemma(p.add_zero, &[sgn_eps]);
                let refl_eps_eps_1 = erefl(d, p, eps_eps);
                let lhs_congr = d.lemma(
                    p.le_congr,
                    &[
                        sgn_eps_zero,
                        sgn_eps,
                        eps_eps,
                        eps_eps,
                        add_zero_eq,
                        refl_eps_eps_1,
                        add_le,
                    ],
                );
                let refl_sgn_eps_3 = erefl(d, p, sgn_eps);
                d.lemma(
                    p.le_congr,
                    &[
                        sgn_eps,
                        sgn_eps,
                        eps_eps,
                        target_e_creal,
                        refl_sgn_eps_3,
                        double_eq_target,
                        lhs_congr,
                    ],
                )
            };
            // `le (neg f_qq2) target_e_creal`, from `h5 : le (neg sgn_eps)
            // f_qq2` via `neg_le_neg` (giving `le (neg f_qq2) (neg (neg
            // sgn_eps))`), `double_neg` to fold `neg (neg sgn_eps) ~
            // sgn_eps`, then `sgn_eps_le_target`.
            let neg_f_qq2 = cneg(d, p, f_qq2);
            let step_nn = d.lemma(p.neg_le_neg, &[neg_sgn_eps, f_qq2, h5]);
            // step_nn : le neg_f_qq2 (neg neg_sgn_eps)
            let neg_neg_sgn_eps = cneg(d, p, neg_sgn_eps);
            let dn = double_neg(d, p, sgn_eps); // Equiv neg_neg_sgn_eps sgn_eps
            let neg_f_qq2_eq_refl = erefl(d, p, neg_f_qq2);
            let neg_f_qq2_le_sgn = d.lemma(
                p.le_congr,
                &[
                    neg_f_qq2,
                    neg_f_qq2,
                    neg_neg_sgn_eps,
                    sgn_eps,
                    neg_f_qq2_eq_refl,
                    dn,
                    step_nn,
                ],
            );
            let neg_fqq2_le_target = d.lemma(
                p.le_trans,
                &[
                    neg_f_qq2,
                    sgn_eps,
                    target_e_creal,
                    neg_f_qq2_le_sgn,
                    sgn_eps_le_target,
                ],
            );

            let abs_fqq2_le_target = d.lemma(
                p.abs_le,
                &[f_qq2, target_e_creal, f_qq2_le_target, neg_fqq2_le_target],
            );

            approx_exists_proof(
                d,
                p,
                f,
                a,
                b,
                target_e_rat,
                carrier,
                qq2,
                range_a_qq2,
                h3,
                abs_fqq2_le_target,
            )
        },
    );

    let value = {
        let with_e = d.lam_fv(e_fv, nat, body);
        let with_hfb = d.lam_fv(hfb_fv, hfb_ty, with_e);
        let with_hfa = d.lam_fv(hfa_fv, hfa_ty, with_hfb);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hfa);
        let with_huc = d.lam_fv(huc_fv, uc_ty_ab, with_hab);
        let with_b = d.lam_fv(b_fv, carrier, with_huc);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, fn_ty, with_a)
    };
    let ty = {
        let with_e = d.pi_fv(e_fv, nat, target_ty);
        let with_hfb = d.arrow(hfb_ty, with_e);
        let with_hfa = d.arrow(hfa_ty, with_hfb);
        let with_hab = d.arrow(hab_ty, with_hfa);
        let with_huc = d.arrow(uc_ty_ab, with_hab);
        let with_b = d.pi_fv(b_fv, carrier, with_huc);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, fn_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_approx,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_bisect` -- a DATA-VALUED bisection, replacing the `Exists`-
// wrapped `ivt_iter` above. See `docs/mathematics-2026-08/diary-exact-root-
// obstruction.md` for why the existential route is dead (two independent
// obstructions), and `CRealPrelude::ivt_bisect`'s own doc comment in
// `creal.rs` for the three design decisions this construction makes:
//
//   1. `eps` is the explicit `Nat` `n` (`eps_n := ofRat (natDivSucc 1 n)`),
//      not an arbitrary `CReal` -- a real carries no `Nat` a construction
//      could sample at.
//   2. The per-step branch is read off a RATIONAL sample of `F m` via
//      `Rat.ble`, a genuine `Bool`, at the FIXED index `j := succ (2*n)`
//      (the same `j` at every step -- the slack `eps_n` never shrinks,
//      matching `ivt_iter`, not `ivt_approx`'s per-accuracy schedule).
//   3. The bracket carrier is `Bool → CReal`, not a new `Prod`/`Sigma` (this
//      kernel has neither) and not two independently-recursing functions
//      (which would need the identical pairing anyway, since each step's
//      midpoint needs BOTH current endpoints). One `Nat.rec` computes the
//      pair; `ivt_bisect_lo`/`ivt_bisect_hi` are its two projections.
//
// Sampling-index derivation (the "sufficiently precise" question): write
// `eps_n := ofRat (natDivSucc 1 n)` and `j := succ (2*n)`. By
// `Rat.natDivSucc_halve n : Eq (natDivSucc 2 j) (natDivSucc 1 n)`,
// `thresh := natDivSucc 1 j` satisfies `thresh + thresh ~ eps_n` -- i.e.
// `thresh = eps_n / 2` exactly (the same "Bishop shift 2n+1" identity
// `sgn_eps_of`/`sgn_eps_double_eq_target` above already package for
// `ivt_approx`, reused here as pure arithmetic; this slice does not yet
// PROVE the invariant, so `sgn_eps_of`'s own positivity/doubling proofs are
// not invoked, only its index shape). Given `s := seq (F m) j`:
//
//   - `CReal.rat_approx_upper (F m) j : le (F m) (ofRat (add s (natDivSucc 1
//     j)))`, i.e. `F m ≤ s + thresh`. If `Rat.ble s thresh = true` (`s ≤
//     thresh`), `F m ≤ thresh + thresh = eps_n` -- the "F m < eps" branch,
//     bracket `(m, hi)`.
//   - `CReal.rat_approx_lower (F m) j : le (ofRat (sub s (natDivSucc 1 j)))
//     (F m)`, i.e. `s − thresh ≤ F m`. If `Rat.ble s thresh = false`, `s >
//     thresh` (from `Rat.ble`'s spec plus totality), so `F m ≥ s − thresh >
//     0 > −eps_n` -- the "−eps < F m" branch, bracket `(lo, m)`. (This
//     branch's bound is in fact stronger than the invariant needs; the test
//     only has to be SOUND for `ivt_step`'s six-part invariant, not tight.)
//
// This derivation is recorded here for the Step 3 invariant proof (not
// attempted in this slice); this file only builds the COMPUTATION.
// =============================================================================

/// `j := succ (2*n)`, `thresh := Rat.natDivSucc 1 j` -- the fixed sampling
/// index and branch threshold for a bisection at slack index `n`. See this
/// section's module documentation for why `thresh` is exactly half of
/// `eps_n := ofRat (natDivSucc 1 n)`.
fn bisect_sample_index(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> (ExprId, ExprId) {
    let two_nat = d.num(2);
    let two_n = d.mul(two_nat, n);
    let j = d.succ(two_n);
    let thresh = div_succ(d, p, 1, j);
    (j, thresh)
}

/// `m := lo + (hi − lo) * (1/2)` -- exact midpoint, the same construction
/// [`declare_ivt_step`]'s own `m` uses.
fn midpoint(d: &mut IntDev<'_>, p: CRealPrelude, lo: ExprId, hi: ExprId) -> ExprId {
    let neg_lo = cneg(d, p, lo);
    let width = cadd(d, p, hi, neg_lo);
    let one_nat = d.num(1);
    let (half, _half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let width_half = cmul(d, p, width, half);
    cadd(d, p, lo, width_half)
}

/// `Bool.rec (fun _ => CReal) on_false on_true condition` -- the `if
/// condition then on_true else on_false` idiom at `CReal` (`Sort 1`, hence
/// `level_one()`). A copy of [`NatOps::bool_select_nat`]'s pattern with the
/// target type generalized from the hardcoded `Nat` to `carrier` (`Nat` and
/// `CReal` happen to share the same sort, which is why the level argument is
/// unchanged, not because the two targets are otherwise related).
fn bool_select_creal(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    carrier: ExprId,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, carrier, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = p.rat.int.logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `Nat.rec.{1} motive base step target` -- the TYPE-valued analogue of
/// [`NatOps::induct`] (which hardcodes `level_zero`, i.e. is `Prop`-only).
/// Needed for `ivt_bisect`'s motive `fun _ : Nat => Bool → CReal`, a `Sort
/// 1` family: legal unconditionally, since `Nat`'s OWN sort is nonzero, per
/// `inductive.rs`'s `allows_large_elimination` rule (see this file's
/// top-of-module documentation and the diary this slice starts from).
fn data_induct(
    d: &mut IntDev<'_>,
    motive_body: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    base: &dyn Fn(&mut IntDev<'_>) -> ExprId,
    step: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
    target: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = motive_body(d, x);
        d.lam_fv(x_fv, nat, body)
    };
    let base_term = base(d);
    let step_term = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let hyp_ty = motive_body(d, j);
        let body = step(d, j, ih);
        let inner = d.lam_fv(ih_fv, hyp_ty, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let one = d.level_one();
    let name = d.prelude().rec;
    let rec = d.kernel().const_(name, vec![one]);
    d.apply(rec, &[motive, base_term, step_term, target])
}

/// `CReal.ivt_bisect` -- see this section's module documentation and
/// [`super::CRealPrelude::ivt_bisect`]'s own doc comment for the statement
/// and the three design decisions.
fn declare_ivt_bisect(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let bracket_ty = d.arrow(bool_ty, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cp0_fv = d.fresh_fvar();
    let cp0 = d.kernel().fvar(cp0_fv);
    let cq0_fv = d.fresh_fvar();
    let cq0 = d.kernel().fvar(cq0_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let (sample_idx, thresh_rat) = bisect_sample_index(d, p, n);

    let motive_body = |d: &mut IntDev<'_>, _x: ExprId| -> ExprId { d.arrow(bool_ty, carrier) };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        // b = true -> hi = cq0; b = false -> lo = cp0.
        let body = bool_select_creal(d, p, carrier, b, cq0, cp0);
        d.lam_fv(b_fv, bool_ty, body)
    };

    let step = |d: &mut IntDev<'_>, _j: ExprId, ih: ExprId| -> ExprId {
        let lo = {
            let fls = d.bool_false();
            d.apply(ih, &[fls])
        };
        let hi = {
            let tru = d.bool_true();
            d.apply(ih, &[tru])
        };
        let m = midpoint(d, p, lo, hi);
        let fm = d.apply(f, &[m]);
        let s = sample(d, p, fm, sample_idx);
        // br = true  <->  s <= thresh  <->  (derivable) F m <= eps_n
        // br = false <->  s >  thresh  <->  (derivable) F m >  0 > -eps_n
        let br = d.const_app(p.rat.ble, &[s, thresh_rat]);
        // br=true: F m is small (<= eps_n), so the new bracket is (m, hi);
        // br=false: F m is large (> 0 > -eps_n), so the new bracket is
        // (lo, m). See this section's module documentation for the proof
        // sketch relating `br` to the `ivt_step` branch it mirrors.
        let new_lo = bool_select_creal(d, p, carrier, br, m, lo);
        let new_hi = bool_select_creal(d, p, carrier, br, hi, m);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let body = bool_select_creal(d, p, carrier, b, new_hi, new_lo);
        d.lam_fv(b_fv, bool_ty, body)
    };

    let bracket = data_induct(d, &motive_body, &base, &step, k);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, bracket);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_n);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, bracket_ty);
        let with_n = d.pi_fv(n_fv, nat, with_k);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_n);
        let with_cp0 = d.pi_fv(cp0_fv, carrier, with_cq0);
        d.pi_fv(f_fv, fn_ty, with_cp0)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ivt_bisect,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 60),
    })
}

/// Shared body for [`declare_ivt_bisect_lo`]/[`declare_ivt_bisect_hi`]:
/// `fun F P Q n k => ivt_bisect F P Q n k selector`.
fn declare_ivt_bisect_projection(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    name: NameId,
    height: u16,
    which: bool,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cp0_fv = d.fresh_fvar();
    let cp0 = d.kernel().fvar(cp0_fv);
    let cq0_fv = d.fresh_fvar();
    let cq0 = d.kernel().fvar(cq0_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let selector = if which { d.bool_true() } else { d.bool_false() };
    let bisect = d.kernel().const_(p.ivt_bisect, vec![]);
    let applied = d.apply(bisect, &[f, cp0, cq0, n, k, selector]);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, applied);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_n);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, carrier);
        let with_n = d.pi_fv(n_fv, nat, with_k);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_n);
        let with_cp0 = d.pi_fv(cp0_fv, carrier, with_cq0);
        d.pi_fv(f_fv, fn_ty, with_cp0)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(height),
    })
}

/// `CReal.ivt_bisect_lo := fun F P Q n k => ivt_bisect F P Q n k Bool.false`.
fn declare_ivt_bisect_lo(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_ivt_bisect_projection(d, p, p.ivt_bisect_lo, super::DERIVED_HEIGHT + 61, false)
}

/// `CReal.ivt_bisect_hi := fun F P Q n k => ivt_bisect F P Q n k Bool.true`.
fn declare_ivt_bisect_hi(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_ivt_bisect_projection(d, p, p.ivt_bisect_hi, super::DERIVED_HEIGHT + 61, true)
}
