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
//! The invariant spec theorem this paragraph once called not-yet-landed is
//! [`CReal.ivt_bisect_invariant`](super::CRealPrelude::ivt_bisect_invariant),
//! and the chain it unlocked runs to the end of the file:
//! [`ivt_bisect_approx`](super::CRealPrelude::ivt_bisect_approx) (that
//! invariant's estimate at a NAMED point),
//! [`abs_diff_le_of_small_image`](super::CRealPrelude::abs_diff_le_of_small_image),
//! [`cauchy_of_abs_diff_le`](super::CRealPrelude::cauchy_of_abs_diff_le),
//! [`ivt_bisect_cauchy`](super::CRealPrelude::ivt_bisect_cauchy) and
//! [`ivt_exact_root`](super::CRealPrelude::ivt_exact_root).
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
//! needs is available.
//!
//! **And the exact direction is available too, under one extra hypothesis.**
//! [`CReal.ivt_exact_root`](super::CRealPrelude::ivt_exact_root) (this
//! file's last section) produces a `c` with `Equiv (F c) zero` outright,
//! given a uniformly positive derivative on `[a,b]`. That does not
//! contradict "Why the classical statement is unavailable" above: nothing in
//! it decides the sign of a real, and the classical statement -- for an
//! arbitrary continuous `F` -- stays unavailable. The positive derivative
//! makes the root unique WITH A MODULUS, which is what turns a sequence of
//! approximate roots into a Cauchy sequence.

#![allow(
    clippy::too_many_arguments,
    clippy::many_single_char_names,
    clippy::too_many_lines
)]

use super::ring_helpers::right_distrib;
use super::{
    CRealPrelude, and_intro, cadd, cle, clt, creal_ty, div_succ, div_succ_k, embed, equiv, halves,
    modulus, sample, weaken, within,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsub, rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, rle, rlt, rmul, rneg,
    rone, rsymm, rzero,
};

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
    declare_ivt_bisect_hi(d, p)?;
    declare_ivt_bisect_invariant(d, p)?;
    // The DIAGONAL bisection -- one `Nat.rec`, no external slack parameter,
    // each step sampling at its own recursion depth. See
    // `CRealPrelude::ivt_bisect_diag`'s own doc comment and this file's
    // "Diagonal bisection" section (near `declare_ivt_bisect_diag`, below)
    // for the construction and the two counterexamples that close off an
    // exact root via this route.
    declare_ivt_bisect_diag(d, p)?;
    declare_ivt_bisect_diag_lo(d, p)?;
    declare_ivt_bisect_diag_hi(d, p)?;
    // `ivt_approx` with the `Exists` removed: the same estimate, run against
    // the concrete `ivt_bisect_hi` bracket via `ivt_bisect_invariant`.
    declare_ivt_bisect_approx(d, p)?;
    // The order-free two-point separation bound the EXACT root needs -- see
    // the section header above `declare_abs_diff_le_of_small_image` for why
    // this is a `lt_cotrans` and not the lattice detour the diary proposed.
    declare_abs_diff_le_of_small_image(d, p)?;
    // ...and the two composed: the exact root's Cauchy estimate at the
    // `CReal` level. Runs AFTER both of its inputs.
    declare_ivt_bisect_cauchy_bound(d, p)?;
    // The general real-bound-to-`CReal.Cauchy` bridge. Nothing about it is
    // IVT-specific; it lives here only because this is the file that first
    // needed it.
    declare_cauchy_of_abs_diff_le(d, p)?;
    // ...applied to the bisection sequence, as a `Nat -> CReal` LAMBDA.
    declare_ivt_bisect_cauchy(d, p)?;
    // ...and the EXACT root the whole chapter is aimed at.
    declare_ivt_exact_root(d, p)
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

/// Everything `approx_endpoint_bound` reads from its caller's scope: the
/// function, the interval, the uniform-continuity witness, the slack index
/// and its `CReal` slack, and the width bound `width_le_via_bound` produced.
#[derive(Clone, Copy)]
struct ApproxCtx {
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
    n: ExprId,
    sgn_eps: ExprId,
    neg_sgn_eps: ExprId,
    sgn_eps_nonneg: ExprId,
    target_e_rat: ExprId,
    double_eq_target: ExprId,
    width_term: ExprId,
    target_creal: ExprId,
    target_nonneg: ExprId,
    width_le: ExprId,
}

/// [`approx_setup`]'s result: the shared context plus the three things only
/// the `ivt_iter` route consumes (`sgn_eps_pos` and the two sign hypotheses
/// at the FIXED slack, which `ivt_bisect_invariant` also takes).
struct ApproxSetup {
    ctx: ApproxCtx,
    bisect_n: ExprId,
    sgn_eps_pos: ExprId,
    hfp: ExprId,
    hfq: ExprId,
}

/// The accuracy schedule both IVT closings share, at outer accuracy `e`:
/// the slack index `n := succ (2*e)` and its `sgn_eps := 1/(n+1)`, the two
/// sign hypotheses weakened from `F a <= 0 <= F b` to the slack form, the
/// continuity modulus at `n`, and the bisection depth
/// [`width_le_via_bound`] computes from the initial width.
///
/// Extracted rather than copied: [`declare_ivt_approx`] and
/// [`declare_ivt_bisect_approx`] must agree on every one of these terms
/// (they instantiate the SAME invariant at the SAME slack), and two copies
/// that drifted would be accepted by the kernel as two different theorems.
#[allow(clippy::too_many_arguments)]
fn approx_setup(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
    hab: ExprId,
    hfa: ExprId,
    hfb: ExprId,
    e: ExprId,
) -> ApproxSetup {
    let zero_c = czero(d, p);
    let fa = d.apply(f, &[a]);
    let fb = d.apply(f, &[b]);

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

    ApproxSetup {
        ctx: ApproxCtx {
            f,
            a,
            b,
            huc,
            n,
            sgn_eps,
            neg_sgn_eps,
            sgn_eps_nonneg,
            target_e_rat,
            double_eq_target,
            width_term,
            target_creal,
            target_nonneg,
            width_le,
        },
        bisect_n,
        sgn_eps_pos,
        hfp,
        hfq,
    }
}

/// The estimate `declare_ivt_approx` runs on ONE bracket, factored out so
/// the concrete data-valued bracket can run the identical argument.
///
/// Given the six-part invariant at `(pp2, qq2)` -- whichever route produced
/// it, `ivt_iter`'s existential or `ivt_bisect_invariant`'s concrete pair --
/// returns `(le a qq2, le (abs (F qq2)) (ofRat target_e_rat))`. The width
/// conjunct plus `uc_spec` bound `|F qq2 - F pp2|` by `sgn_eps`; the two
/// sign conjuncts then pin `F qq2` into `[-sgn_eps, 2*sgn_eps]`, and
/// `double_eq_target` folds `sgn_eps + sgn_eps` to the caller's accuracy.
fn approx_endpoint_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: &ApproxCtx,
    pp2: ExprId,
    qq2: ExprId,
    h1: ExprId,
    h2: ExprId,
    h3: ExprId,
    h4: ExprId,
    h5: ExprId,
    h6: ExprId,
) -> (ExprId, ExprId) {
    let ApproxCtx {
        f,
        a,
        b,
        huc,
        n,
        sgn_eps,
        neg_sgn_eps,
        sgn_eps_nonneg,
        target_e_rat,
        double_eq_target,
        width_term,
        target_creal,
        target_nonneg,
        width_le,
    } = *c;
    let zero_c = czero(d, p);
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
    (range_a_qq2, abs_fqq2_le_target)
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
    let setup = approx_setup(d, p, f, a, b, huc, hab, hfa, hfb, e);
    let ctx = setup.ctx;
    let target_e_rat = ctx.target_e_rat;
    let sgn_eps = ctx.sgn_eps;
    let width_term = ctx.width_term;

    let iter_at_n = d.lemma(
        p.ivt_iter,
        &[
            f,
            a,
            b,
            sgn_eps,
            setup.sgn_eps_pos,
            hab,
            setup.hfp,
            setup.hfq,
            setup.bisect_n,
        ],
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
            let (range_a_qq2, abs_fqq2_le_target) =
                approx_endpoint_bound(d, p, &ctx, pp2, qq2, h1, h2, h3, h4, h5, h6);

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

// =============================================================================
// `CReal.ivt_bisect_invariant` -- the invariant spec theorem for
// `CReal.ivt_bisect`: the concrete bracket it computes satisfies the SAME
// six-part invariant `ivt_step`/`ivt_iter` prove, for the fixed slack
// `eps_n := ofRat (natDivSucc 1 n)`. See `CRealPrelude::ivt_bisect_invariant`
// for the exact statement and the "remembering `Bool.rec`" proof sketch.
// =============================================================================

/// From `h : Rat.le y z`, `Rat.le rzero (Rat.add z (Rat.neg y))` -- the
/// RAT-level analogue of this file's own [`sub_nonneg_of_le`] (which works
/// over `CReal.Equiv`). `Rat`'s own equality is ordinary `Eq`, so
/// [`rat_eq_rewrite`] substitutes directly and no `le_congr`-shaped lemma is
/// needed.
fn rat_sub_nonneg_of_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    y: ExprId,
    z: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let ny = rneg(d, y);
    let gap = radd(d, z, ny);
    let cancelled = radd(d, y, ny);
    let reflexive = d.lemma(rat.le_refl, &[ny]);
    let shifted = d.lemma(rat.add_le_add, &[y, z, ny, ny, h, reflexive]); // Rat.le cancelled gap
    let vanish = d.lemma(rat.add_neg, &[y]); // Eq cancelled rzero
    let rzero_val = rzero(d, rat);
    rat_eq_rewrite(d, cancelled, rzero_val, vanish, shifted, &|d, t| {
        rle(d, rat, t, gap)
    })
}

/// Bracket midpoint facts shared by [`declare_ivt_step`]'s own bisection
/// argument and the invariant proof below: given `hpq : le lo hi`, the exact
/// midpoint `m`, `width_half := (hi - lo) * (1/2)`, `le lo m`, `le m hi`, and
/// the two width identities `Equiv (add m (neg lo)) width_half` / `Equiv (add
/// hi (neg m)) width_half`. Verbatim reproduction of `declare_ivt_step`'s own
/// internal derivation (`cp,cq` renamed `lo,hi`) -- duplicated per this
/// codebase's own convention (see this file's `cneg`/`cmul`/`czero`/...
/// note) rather than factored into `declare_ivt_step`, which stays untouched.
#[allow(clippy::similar_names)]
fn bisect_midpoint_facts(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    lo: ExprId,
    hi: ExprId,
    hpq: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let neg_lo = cneg(d, p, lo);
    let width = cadd(d, p, hi, neg_lo);
    let one_nat = d.num(1);
    let (half, half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let width_half = cmul(d, p, width, half);

    let m = cadd(d, p, lo, width_half);

    let width_nonneg = sub_nonneg_of_le(d, p, lo, hi, hpq);
    let step_nonneg = d.lemma(p.mul_nonneg, &[width, half, width_nonneg, half_nonneg]);
    let zero_c = czero(d, p);

    // le lo m
    let m_minus_lo_eq_step = cancel_right(d, p, lo, width_half);
    let m_minus_lo_nonneg = {
        let m_minus_lo = cadd(d, p, m, neg_lo);
        let flipped = esymm(d, p, m_minus_lo, width_half, m_minus_lo_eq_step);
        let refl_zero = erefl(d, p, zero_c);
        d.lemma(
            p.le_congr,
            &[
                zero_c,
                zero_c,
                width_half,
                m_minus_lo,
                refl_zero,
                flipped,
                step_nonneg,
            ],
        )
    };
    let le_lo_m = le_of_nonneg_sub(d, p, lo, m, m_minus_lo_nonneg);

    let width_eq_2step = width_eq_two_step(d, p, width, width_half, one_nat);
    let restore = restore_from_width(d, p, lo, hi);

    let hi_eq_m_plus_step = {
        let step_step = cadd(d, p, width_half, width_half);
        let assoc1 = d.lemma(p.add_assoc, &[lo, width_half, width_half]);
        let lo_step_step = cadd(d, p, lo, step_step);
        let lo_width = cadd(d, p, lo, width);
        let refl_lo = erefl(d, p, lo);
        let step_b = d.lemma(
            p.add_congr,
            &[lo, lo, step_step, width, refl_lo, width_eq_2step],
        );
        let m_width_half = cadd(d, p, m, width_half);
        let mid = d.lemma(
            p.equiv_trans,
            &[m_width_half, lo_step_step, lo_width, assoc1, step_b],
        );
        d.lemma(p.equiv_trans, &[m_width_half, lo_width, hi, mid, restore])
    };

    let hi_minus_m_eq_step = {
        let m_width_half = cadd(d, p, m, width_half);
        let cancel2 = cancel_right(d, p, m, width_half);
        let hi_eq_reversed = esymm(d, p, m_width_half, hi, hi_eq_m_plus_step);
        let neg_m = cneg(d, p, m);
        let refl_neg_m = erefl(d, p, neg_m);
        let congr_step = d.lemma(
            p.add_congr,
            &[hi, m_width_half, neg_m, neg_m, hi_eq_reversed, refl_neg_m],
        );
        let hi_minus_m = cadd(d, p, hi, neg_m);
        let m_width_half_minus_m = cadd(d, p, m_width_half, neg_m);
        d.lemma(
            p.equiv_trans,
            &[
                hi_minus_m,
                m_width_half_minus_m,
                width_half,
                congr_step,
                cancel2,
            ],
        )
    };
    let hi_minus_m_nonneg = {
        let neg_m2 = cneg(d, p, m);
        let hi_minus_m = cadd(d, p, hi, neg_m2);
        let flipped = esymm(d, p, hi_minus_m, width_half, hi_minus_m_eq_step);
        let refl_zero2 = erefl(d, p, zero_c);
        d.lemma(
            p.le_congr,
            &[
                zero_c,
                zero_c,
                width_half,
                hi_minus_m,
                refl_zero2,
                flipped,
                step_nonneg,
            ],
        )
    };
    let le_m_hi = le_of_nonneg_sub(d, p, m, hi, hi_minus_m_nonneg);

    (
        m,
        width_half,
        le_lo_m,
        le_m_hi,
        m_minus_lo_eq_step,
        hi_minus_m_eq_step,
    )
}

/// Extract the six conjuncts from a proof of `conj_ty(f,cp,cq,eps,width_half,
/// pp,qq)`, in [`conj_ty`]'s own order. The mirror image of `conj_proof`;
/// verbatim reproduction of `with_ivt_witness`'s own inner extraction (which
/// is buried inside that function's `Exists`-elimination and not reusable
/// standalone).
#[allow(clippy::too_many_arguments)]
fn conj_split(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    cp: ExprId,
    cq: ExprId,
    eps: ExprId,
    width_half: ExprId,
    pp: ExprId,
    qq: ExprId,
    h: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
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
    (h1, h2, h3, h4, h5, h6)
}

/// `CReal.ivt_bisect_invariant` -- see `CRealPrelude::ivt_bisect_invariant`'s
/// own doc comment for the statement and this section's module documentation
/// for the proof sketch.
#[allow(clippy::too_many_lines)]
fn declare_ivt_bisect_invariant(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cp0_fv = d.fresh_fvar();
    let cp0 = d.kernel().fvar(cp0_fv);
    let cq0_fv = d.fresh_fvar();
    let cq0 = d.kernel().fvar(cq0_fv);
    let slack_fv = d.fresh_fvar();
    let slack_n = d.kernel().fvar(slack_fv);

    // `eps_n := ofRat (natDivSucc 1 slack_n)`, and the sampling index/
    // threshold `ivt_bisect`'s own `step` closure computes internally
    // (`bisect_sample_index`) -- reused here via `sgn_eps_of`, the SAME
    // construction (`j := succ (2*slack_n)`, `thresh := natDivSucc 1 j`), so
    // the two calls build the same `ExprId`s (checked below).
    let (sample_idx, thresh_creal, thresh_rat, _thresh_pos) = sgn_eps_of(d, p, slack_n);
    {
        let (check_j, check_thresh) = bisect_sample_index(d, p, slack_n);
        debug_assert_eq!(sample_idx, check_j);
        debug_assert_eq!(thresh_rat, check_thresh);
    }
    let (eps_n_rat, thresh_double_eq_eps_n) =
        sgn_eps_double_eq_target(d, p, slack_n, sample_idx, thresh_creal, thresh_rat);
    let eps_n = embed(d, p, eps_n_rat);
    let neg_eps_n = cneg(d, p, eps_n);

    let hpq_ty = cle(d, p, cp0, cq0);
    let hpq_fv = d.fresh_fvar();
    let hpq = d.kernel().fvar(hpq_fv);

    let fp0 = d.apply(f, &[cp0]);
    let hfp_ty = cle(d, p, fp0, eps_n);
    let hfp_fv = d.fresh_fvar();
    let hfp = d.kernel().fvar(hfp_fv);

    let fq0 = d.apply(f, &[cq0]);
    let hfq_ty = cle(d, p, neg_eps_n, fq0);
    let hfq_fv = d.fresh_fvar();
    let hfq = d.kernel().fvar(hfq_fv);

    let one_nat = d.num(1);
    let (half, _half_nonneg) = nonneg_rat_bound(d, p, 1, one_nat);
    let neg_cp0 = cneg(d, p, cp0);
    let w0 = cadd(d, p, cq0, neg_cp0);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let lo_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        d.const_app(p.ivt_bisect_lo, &[f, cp0, cq0, slack_n, x])
    };
    let hi_at = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        d.const_app(p.ivt_bisect_hi, &[f, cp0, cq0, slack_n, x])
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let width_x = ivt_iter_width(d, p, w0, half, x);
        let lo = lo_at(d, x);
        let hi = hi_at(d, x);
        conj_ty(d, p, f, cp0, cq0, eps_n, width_x, lo, hi)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_nat = d.num(0);
        let width0 = ivt_iter_width(d, p, w0, half, zero_nat);
        let h1 = d.lemma(p.le_refl, &[cp0]);
        let h3 = d.lemma(p.le_refl, &[cq0]);
        let one_c = d.kernel().const_(p.one, vec![]);
        let mul_w0_one = cmul(d, p, w0, one_c);
        let mo = d.lemma(p.mul_one, &[w0]);
        let h6 = esymm(d, p, mul_w0_one, w0, mo);
        // `lo_at(0)`/`hi_at(0)` are defeq to `cp0`/`cq0` (`Nat.rec` at zero,
        // then `Bool.rec` at `false`/`true`); the kernel accepts this
        // `conj_proof` (stated directly at `cp0`/`cq0`) at `motive(0)` by
        // unfolding `ivt_bisect_lo`/`ivt_bisect_hi`/`ivt_bisect` through that
        // iota-reduction.
        conj_proof(
            d, p, f, cp0, cq0, eps_n, width0, cp0, cq0, h1, hpq, h3, hfp, hfq, h6,
        )
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let width_j = ivt_iter_width(d, p, w0, half, j);
        let lo = lo_at(d, j);
        let hi = hi_at(d, j);
        let (h1, h2, h3, h4, h5, h6) = conj_split(d, p, f, cp0, cq0, eps_n, width_j, lo, hi, ih);

        let (m, width_half_j, le_lo_m, le_m_hi, m_minus_lo_eq_step, hi_minus_m_eq_step) =
            bisect_midpoint_facts(d, p, lo, hi, h2);

        let fm = d.apply(f, &[m]);
        let s = sample(d, p, fm, sample_idx);
        let br = d.const_app(p.rat.ble, &[s, thresh_rat]);

        // width chaining: width_half_j ~ mul width_j half [via h6, mul_congr]
        // ~ mul w0 (mul (pow half j) half) [mul_assoc] =(defeq, `pow`
        // ι-reduces) width at step `succ j`.
        let pow_half_j = d.const_app(p.pow, &[half, j]);
        let refl_half = erefl(d, p, half);
        let neg_lo_here = cneg(d, p, lo);
        let gap = cadd(d, p, hi, neg_lo_here);
        let congr_step = d.lemma(p.mul_congr, &[gap, width_j, half, half, h6, refl_half]);
        let mul_width_j_half = cmul(d, p, width_j, half);
        let assoc_step = d.lemma(p.mul_assoc, &[w0, pow_half_j, half]);
        let inner_half = cmul(d, p, pow_half_j, half);
        let final_width = cmul(d, p, w0, inner_half);
        let width_chain = d.lemma(
            p.equiv_trans,
            &[
                width_half_j,
                mul_width_j_half,
                final_width,
                congr_step,
                assoc_step,
            ],
        );

        let neg_m_here = cneg(d, p, m);
        let hi_minus_m = cadd(d, p, hi, neg_m_here);
        let true_width = d.lemma(
            p.equiv_trans,
            &[
                hi_minus_m,
                width_half_j,
                final_width,
                hi_minus_m_eq_step,
                width_chain,
            ],
        );
        let neg_lo_here2 = cneg(d, p, lo);
        let m_minus_lo = cadd(d, p, m, neg_lo_here2);
        let false_width = d.lemma(
            p.equiv_trans,
            &[
                m_minus_lo,
                width_half_j,
                final_width,
                m_minus_lo_eq_step,
                width_chain,
            ],
        );

        let true_val = d.bool_true();
        let false_val = d.bool_false();

        let motive_b = |d: &mut IntDev<'_>, b: ExprId| -> ExprId {
            let heq_ty = d.bool_eq(br, b);
            let new_lo = bool_select_creal(d, p, carrier, b, m, lo);
            let new_hi = bool_select_creal(d, p, carrier, b, hi, m);
            let body = conj_ty(d, p, f, cp0, cq0, eps_n, final_width, new_lo, new_hi);
            d.arrow(heq_ty, body)
        };

        // `br = true`: `Rat.ble s thresh = true`, i.e. `s <= thresh`, so
        // `F m <= thresh + thresh ~ eps_n` via `rat_approx_upper`. New
        // bracket `(m, hi)`.
        let true_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let heq_ty = d.bool_eq(br, true_val);

            let hle = d.lemma(p.rat.le_of_ble_eq_true, &[s, thresh_rat, h]);
            let hup = d.lemma(p.rat_approx_upper, &[fm, sample_idx]);
            let refl_thresh = d.lemma(p.rat.le_refl, &[thresh_rat]);
            let radd_le = d.lemma(
                p.rat.add_le_add,
                &[s, thresh_rat, thresh_rat, thresh_rat, hle, refl_thresh],
            );
            let sum_st = radd(d, s, thresh_rat);
            let sum_tt = radd(d, thresh_rat, thresh_rat);
            let hrle = d.lemma(p.of_rat_le, &[sum_st, sum_tt, radd_le]);

            let of_rat_add_tt = d.lemma(p.of_rat_add, &[thresh_rat, thresh_rat]);
            let thresh_thresh = cadd(d, p, thresh_creal, thresh_creal);
            let ofrat_sum_tt = embed(d, p, sum_tt);
            let flipped = esymm(d, p, thresh_thresh, ofrat_sum_tt, of_rat_add_tt);
            let hde = d.lemma(
                p.equiv_trans,
                &[
                    ofrat_sum_tt,
                    thresh_thresh,
                    eps_n,
                    flipped,
                    thresh_double_eq_eps_n,
                ],
            );
            let ofrat_sum_st = embed(d, p, sum_st);
            let refl_left = erefl(d, p, ofrat_sum_st);
            let hcre = d.lemma(
                p.le_congr,
                &[
                    ofrat_sum_st,
                    ofrat_sum_st,
                    ofrat_sum_tt,
                    eps_n,
                    refl_left,
                    hde,
                    hrle,
                ],
            );
            let sign_true = d.lemma(p.le_trans, &[fm, ofrat_sum_st, eps_n, hup, hcre]);

            let h1p = d.lemma(p.le_trans, &[cp0, lo, m, h1, le_lo_m]);
            let body = conj_proof(
                d,
                p,
                f,
                cp0,
                cq0,
                eps_n,
                final_width,
                m,
                hi,
                h1p,
                le_m_hi,
                h3,
                sign_true,
                h5,
                true_width,
            );
            d.lam_fv(h_fv, heq_ty, body)
        };

        // `br = false`: `Rat.ble s thresh = false`, so (by totality)
        // `Rat.lt thresh s`, hence `-eps_n <= F m` via `rat_approx_lower`.
        // New bracket `(lo, m)`.
        let false_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let heq_ty = d.bool_eq(br, false_val);

            let target_sign_ty = cle(d, p, neg_eps_n, fm);
            let dis = d.lemma(p.rat.le_or_lt, &[s, thresh_rat]);
            let rle_ty = rle(d, p.rat, s, thresh_rat);
            let rlt_ty = rlt(d, p.rat, thresh_rat, s);

            let sign_false = d.or_elim(
                rle_ty,
                rlt_ty,
                target_sign_ty,
                dis,
                &|d, hp| {
                    let hc = d.lemma(p.rat.ble_eq_true_of_le, &[s, thresh_rat, hp]);
                    let symm_h = d.bool_symm(br, false_val, h);
                    let combined = d.bool_trans(false_val, br, true_val, symm_h, hc);
                    d.false_true_elim(target_sign_ty, combined)
                },
                &|d, hlt| {
                    let hle2 = d.lemma(p.rat.le_of_lt, &[thresh_rat, s, hlt]);
                    let gap_rat = rsub(d, p.rat, s, thresh_rat);
                    let nonneg = rat_sub_nonneg_of_le(d, p, thresh_rat, s, hle2);
                    let one_c = d.num(1);
                    let eps_n_rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[one_c, slack_n]);
                    let neg_eps_n_rat = rneg(d, eps_n_rat);
                    let neg_nonpos =
                        d.lemma(p.rat.neg_nonpos_of_nonneg, &[eps_n_rat, eps_n_rat_nonneg]);
                    let rzero_val = rzero(d, p.rat);
                    let chained = d.lemma(
                        p.rat.le_trans,
                        &[neg_eps_n_rat, rzero_val, gap_rat, neg_nonpos, nonneg],
                    );
                    let hrle2 = d.lemma(p.of_rat_le, &[neg_eps_n_rat, gap_rat, chained]);
                    let lower = d.lemma(p.rat_approx_lower, &[fm, sample_idx]);
                    let of_rat_neg_pf = d.lemma(p.of_rat_neg, &[eps_n_rat]);
                    let ofrat_neg = embed(d, p, neg_eps_n_rat);
                    let hab = esymm(d, p, neg_eps_n, ofrat_neg, of_rat_neg_pf);
                    let ofrat_gap = embed(d, p, gap_rat);
                    let refl_right = erefl(d, p, ofrat_gap);
                    let hcre2 = d.lemma(
                        p.le_congr,
                        &[
                            ofrat_neg, neg_eps_n, ofrat_gap, ofrat_gap, hab, refl_right, hrle2,
                        ],
                    );
                    d.lemma(p.le_trans, &[neg_eps_n, ofrat_gap, fm, hcre2, lower])
                },
            );

            let h3pp = d.lemma(p.le_trans, &[m, hi, cq0, le_m_hi, h3]);
            let body = conj_proof(
                d,
                p,
                f,
                cp0,
                cq0,
                eps_n,
                final_width,
                lo,
                m,
                h1,
                le_lo_m,
                h3pp,
                h4,
                sign_false,
                false_width,
            );
            d.lam_fv(h_fv, heq_ty, body)
        };

        let motive_lam = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let body = motive_b(d, b);
            d.lam_fv(b_fv, bool_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d
            .kernel()
            .const_(p.rat.int.logic.bool_rec, vec![level_zero]);
        let selected = d.apply(bool_rec, &[motive_lam, false_minor, true_minor, br]);
        let br_refl = d.bool_refl(br);
        d.apply(selected, &[br_refl])
    };

    let final_proof = d.induct(&motive, &base, &step, k);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, final_proof);
        let with_hfq = d.lam_fv(hfq_fv, hfq_ty, with_k);
        let with_hfp = d.lam_fv(hfp_fv, hfp_ty, with_hfq);
        let with_hpq = d.lam_fv(hpq_fv, hpq_ty, with_hfp);
        let with_slack = d.lam_fv(slack_fv, nat, with_hpq);
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_slack);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let motive_k = motive(d, k);
        let stmt_k = d.pi_fv(k_fv, nat, motive_k);
        let with_hfq = d.arrow(hfq_ty, stmt_k);
        let with_hfp = d.arrow(hfp_ty, with_hfq);
        let with_hpq = d.arrow(hpq_ty, with_hfp);
        let with_slack = d.pi_fv(slack_fv, nat, with_hpq);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_slack);
        let with_cp0 = d.pi_fv(cp0_fv, carrier, with_cq0);
        d.pi_fv(f_fv, fn_ty, with_cp0)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_bisect_invariant,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_bisect_diag` -- the DIAGONAL bisection, per
// `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s "diagonal
// bisection with shrinking slack" addendum. `CRealPrelude::ivt_bisect_diag`'s
// own doc comment has the statement and both counterexamples; the summary:
//
// `declare_ivt_bisect`'s `step` closure receives the recursion depth `j` as
// its first argument (`data_induct`'s own `step: ... Fn(&mut IntDev<'_>,
// ExprId, ExprId) -> ExprId`) and DISCARDS it (`|d, _j, ih| ...`), instead
// closing over a FIXED `n` computed once outside the recursion. This
// construction uses `j` itself in place of that fixed `n`: `(sample_idx,
// thresh_rat) := bisect_sample_index(d, p, j)`, recomputed AT EVERY STEP from
// the step's own depth. No second `Nat` parameter is needed at all -- the
// slack shrinks along the SAME diagonal the bisection depth walks, which is
// what "diagonal" names here.
//
// This is NOT a sound route to an exact root, and the diary records why with
// two independent, kernel-verified counterexamples on `F := id` on `[-1,2]`:
//
//   1. THIS construction (shrinking slack folded into one recursion): the
//      LOWER endpoint is accepted once, against the COARSEST slack
//      (`thresh_0 = 1/2`, `F(1/2) = 1/2 <= 1/2`), and is never re-examined
//      against any tighter threshold thereafter (only the endpoint that
//      MOVES gets tested at the new depth's slack; the stationary one keeps
//      whatever bound justified its last move). The upper endpoint keeps
//      moving and the width keeps halving, so the bracket DOES converge --
//      to `L = 1/2`, not to the true root `0`, and `F(1/2) = 1/2` is bounded
//      away from `0`.
//   2. The OTHER natural diagonal reading -- re-run `ivt_bisect` FRESH from
//      `(P0, Q0)` for `k` steps at slack `n := k` (i.e. `ivt_bisect F P Q k
//      k`, `ivt_bisect`'s own two-parameter interface with both arguments
//      set equal) -- fails for the opposite reason: since ALL `k` steps of a
//      given run share `n`'s SINGLE threshold, a threshold change at one `k`
//      can flip an EARLY branch decision, and brackets across different `k`
//      are then NOT nested. Concretely: at `k=3` the bracket is `(1/8, 1/2)`
//      and at `k=4` it is `(-1/16, 1/8)` -- disjoint interiors, not nested,
//      so there is no shared refinement for a limit argument to close over.
//
// Both natural constructions are closed off for GENERAL `F` satisfying only
// the one-sided approximate-IVT hypothesis; this file lands the DATA and a
// concrete reduction test recording counterexample (1) at the kernel level
// (an exact rational computation, not an informal claim), and stops there --
// no invariant/exactness theorem is attempted, because none holds.
// =============================================================================

/// `CReal.ivt_bisect_diag` -- see this section's module documentation and
/// [`super::CRealPrelude::ivt_bisect_diag`]'s own doc comment for the
/// construction and the two counterexamples that close off an exact root via
/// this route.
fn declare_ivt_bisect_diag(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let motive_body = |d: &mut IntDev<'_>, _x: ExprId| -> ExprId { d.arrow(bool_ty, carrier) };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        // b = true -> hi = cq0; b = false -> lo = cp0.
        let body = bool_select_creal(d, p, carrier, b, cq0, cp0);
        d.lam_fv(b_fv, bool_ty, body)
    };

    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
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
        // THE difference from `declare_ivt_bisect`: sample/threshold at THIS
        // step's own depth `j`, not a fixed external `n` captured outside
        // the recursion.
        let (sample_idx, thresh_rat) = bisect_sample_index(d, p, j);
        let s = sample(d, p, fm, sample_idx);
        let br = d.const_app(p.rat.ble, &[s, thresh_rat]);
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
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_k);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, bracket_ty);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_k);
        let with_cp0 = d.pi_fv(cp0_fv, carrier, with_cq0);
        d.pi_fv(f_fv, fn_ty, with_cp0)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ivt_bisect_diag,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 62),
    })
}

/// Shared body for [`declare_ivt_bisect_diag_lo`]/[`declare_ivt_bisect_diag_hi`]:
/// `fun F P Q k => ivt_bisect_diag F P Q k selector`.
fn declare_ivt_bisect_diag_projection(
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
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let selector = if which { d.bool_true() } else { d.bool_false() };
    let bisect = d.kernel().const_(p.ivt_bisect_diag, vec![]);
    let applied = d.apply(bisect, &[f, cp0, cq0, k, selector]);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, applied);
        let with_cq0 = d.lam_fv(cq0_fv, carrier, with_k);
        let with_cp0 = d.lam_fv(cp0_fv, carrier, with_cq0);
        d.lam_fv(f_fv, fn_ty, with_cp0)
    };
    let ty = {
        let with_k = d.pi_fv(k_fv, nat, carrier);
        let with_cq0 = d.pi_fv(cq0_fv, carrier, with_k);
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

/// `CReal.ivt_bisect_diag_lo := fun F P Q k => ivt_bisect_diag F P Q k
/// Bool.false`.
fn declare_ivt_bisect_diag_lo(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_ivt_bisect_diag_projection(
        d,
        p,
        p.ivt_bisect_diag_lo,
        super::DERIVED_HEIGHT + 63,
        false,
    )
}

/// `CReal.ivt_bisect_diag_hi := fun F P Q k => ivt_bisect_diag F P Q k
/// Bool.true`.
fn declare_ivt_bisect_diag_hi(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_ivt_bisect_diag_projection(d, p, p.ivt_bisect_diag_hi, super::DERIVED_HEIGHT + 63, true)
}

// =============================================================================
// `CReal.abs_diff_le_of_small_image` -- the ORDER-FREE two-point separation
// bound an exact IVT root needs, and the piece
// `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s "step 3" got
// wrong.
//
// That section proposed routing around the undecidability of `CReal.le` via
// the LATTICE: apply `diff_le_of_strict_mono_magnitude` to the ordered pair
// `(min x y, max x y)` and close with `abs_le`. The ordering half of that is
// fine -- `min_le_left`/`le_max_left`/`le_trans` do order the pair -- but the
// bound it produces is
//
//     max x y - min x y <= (2k+2) * (|F (min x y)| + |F (max x y)|)
//
// whose right-hand side mentions `F` at the LATTICE points, not at `x` and
// `y`. Recovering `|F (min x y)| <= eps` from `|F x| <= eps` and
// `|F y| <= eps` needs a LOWER bound on `F (min x y)`, and every bound
// available points the other way: `min_le_left`/`min_le_right` plus the
// monotonicity `strict_mono_magnitude` supplies bound `F (min x y)` ABOVE, by
// `F x` and by `F y`. A lower bound would need an UPPER bound on `F'`, which
// `HasDerivativeOn` does not carry -- the same asymmetry that section already
// identifies one step earlier, for `F lo`. The meet-semilattice interface
// (`min_le_left`, `min_le_right`, `le_min`) does not entail
// `Equiv (min x y) x ∨ Equiv (min x y) y`, which is exactly the case split
// the detour was supposed to avoid, so the missing bound is not derivable
// from it either.
//
// COTRANSITIVITY supplies the case split instead, and does so without ever
// deciding an order -- the same move `declare_ivt_step` already makes one
// section up. For a target `x - y <= R` and any strictly positive `q`,
// `lt_cotrans` at the pair `(zero, q)` evaluated at `x - y` gives
//
//     Or (lt zero (x - y))  (lt (x - y) q)
//
// and BOTH disjuncts close the goal at slack `q`:
//
//   * `0 < x - y` gives `le y x` (via this file's own `le_of_nonneg_sub`),
//     which is precisely the ordering `diff_le_of_strict_mono_magnitude`
//     wants -- at the pair `(y, x)`, so its right-hand side is
//     `|F y| + |F x|`, the two terms the hypotheses actually bound;
//   * `x - y < q` gives the goal outright, since `R >= 0`.
//
// Quantifying `q` over `1/(e+1)` and closing with
// `le_of_forall_le_add_small` removes the slack. No positivity hypothesis on
// `eps` is needed, and no lattice operation appears anywhere in the proof.
// =============================================================================

/// `CReal.abs x`.
fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

/// `le zero (ofNat n)`, for a SYMBOLIC `n : Nat`.
///
/// This file's own [`nonneg_rat_bound`] at a symbolic numerator: `CReal.ofNat
/// n` is *defined* as `ofRat (Rat.natDivSucc n 0)` (`archimedean.rs`) and
/// `CReal.zero` as `ofRat Rat.zero`, so [`super::CRealPrelude::of_rat_le`]
/// against `Rat.zero_le_natDivSucc` proves this with both sides related by
/// δ-reduction alone -- the same defeq every `nonneg_rat_bound` caller in
/// this file already relies on.
fn nonneg_of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let zero_idx = d.num(0);
    let q = d.const_app(p.rat.nat_div_succ, &[n, zero_idx]);
    let rzero_expr = rzero(d, p.rat);
    let rat_nonneg = d.lemma(p.rat.zero_le_nat_div_succ, &[n, zero_idx]);
    d.lemma(p.of_rat_le, &[rzero_expr, q, rat_nonneg])
}

/// `(ofRat (natDivSucc 1 e), lt zero that)` -- the two lines [`sgn_eps_of`]
/// runs at its own index, at a bare `e`.
fn unit_frac_pos(d: &mut IntDev<'_>, p: CRealPrelude, e: ExprId) -> (ExprId, ExprId) {
    let one_nat = d.num(1);
    let q_rat = div_succ(d, p, 1, e);
    let q = embed(d, p, q_rat);
    let le11 = {
        let np = d.prelude();
        d.const_app(np.le_refl, &[one_nat])
    };
    let rat_pos = d.lemma(p.rat.nat_div_succ_pos, &[one_nat, e, le11]);
    let pos = d.lemma(p.of_rat_pos, &[q_rat, rat_pos]);
    (q, pos)
}

/// The derivative package every caller of
/// [`super::CRealPrelude::diff_le_of_strict_mono_magnitude`] carries, bundled
/// so [`small_image_one_sided`] can be called twice without a
/// twelve-argument signature.
#[derive(Clone, Copy)]
struct DerivPack {
    f: ExprId,
    fp: ExprId,
    a: ExprId,
    b: ExprId,
    hf: ExprId,
    k: ExprId,
    hderiv: ExprId,
}

/// `le (add hi (neg lo)) rhs`, where `rhs := mul csucc eps_sum` and
/// `csucc := ofNat (Nat.succ (Nat.succ (Nat.mul 2 k)))`.
///
/// The one-sided half of [`declare_abs_diff_le_of_small_image`]; called twice,
/// once per orientation, and the two results joined by
/// [`super::CRealPrelude::abs_le`]. See this section's header for why the case
/// split is a `lt_cotrans` rather than a lattice detour.
///
/// `widen` -- `le (add (abs (F lo)) (abs (F hi))) eps_sum` -- is supplied by
/// the caller rather than assembled here, because the two orientations put
/// the caller's two epsilons in opposite order and only one of them needs the
/// `add_comm` transport.
fn small_image_one_sided(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    dp: DerivPack,
    csucc: ExprId,
    eps_sum: ExprId,
    rhs: ExprId,
    rhs_nonneg: ExprId,
    csucc_nonneg: ExprId,
    lo: ExprId,
    hi: ExprId,
    ha_lo: ExprId,
    hhi_b: ExprId,
    widen: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_c = czero(d, p);
    let neg_lo = cneg(d, p, lo);
    let diff = cadd(d, p, hi, neg_lo);

    let f_lo = d.apply(dp.f, &[lo]);
    let f_hi = d.apply(dp.f, &[hi]);
    let abs_f_lo = cabs(d, p, f_lo);
    let abs_f_hi = cabs(d, p, f_hi);
    let sum_abs = cadd(d, p, abs_f_lo, abs_f_hi);
    let scaled_sum = cmul(d, p, csucc, sum_abs);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let (q, q_pos) = unit_frac_pos(d, p, e);
    let rhs_q = cadd(d, p, rhs, q);
    let target_e = cle(d, p, diff, rhs_q);

    let left_ty = clt(d, p, zero_c, diff);
    let right_ty = clt(d, p, diff, q);
    let cotrans = d.lemma(p.lt_cotrans, &[zero_c, q, q_pos, diff]);

    let body = d.or_elim(
        left_ty,
        right_ty,
        target_e,
        cotrans,
        &|d, hpos| {
            // `0 < hi - lo`, so `lo <= hi` and the ordered-pair lemma applies
            // at `(lo, hi)` -- whose right-hand side is `|F lo| + |F hi|`.
            let nonneg = d.lemma(p.le_of_lt, &[zero_c, diff, hpos]);
            let le_lo_hi = le_of_nonneg_sub(d, p, lo, hi, nonneg);
            let raw = d.lemma(
                p.diff_le_of_strict_mono_magnitude,
                &[
                    dp.f, dp.fp, dp.a, dp.b, dp.hf, dp.k, dp.hderiv, lo, hi, ha_lo, le_lo_hi, hhi_b,
                ],
            );
            // raw : le diff scaled_sum
            let scale = d.lemma(
                p.mul_le_mul_of_nonneg_left,
                &[csucc, sum_abs, eps_sum, csucc_nonneg, widen],
            );
            let bounded = d.lemma(p.le_trans, &[diff, scaled_sum, rhs, raw, scale]);
            // rhs <= rhs + q
            let widen_q = {
                let q_nonneg = d.lemma(p.le_of_lt, &[zero_c, q, q_pos]);
                let refl_rhs = d.lemma(p.le_refl, &[rhs]);
                let step = d.lemma(p.add_le_add, &[rhs, rhs, zero_c, q, refl_rhs, q_nonneg]);
                let rhs_zero = cadd(d, p, rhs, zero_c);
                let trim = d.lemma(p.add_zero, &[rhs]);
                let refl_target = erefl(d, p, rhs_q);
                d.lemma(
                    p.le_congr,
                    &[rhs_zero, rhs, rhs_q, rhs_q, trim, refl_target, step],
                )
            };
            d.lemma(p.le_trans, &[diff, rhs, rhs_q, bounded, widen_q])
        },
        &|d, hsmall| {
            // `hi - lo < q`, and `0 <= rhs`, so the goal holds with room to
            // spare -- no derivative fact is consulted in this branch.
            let le_diff_q = d.lemma(p.le_of_lt, &[diff, q, hsmall]);
            let widen_rhs = {
                let refl_q = d.lemma(p.le_refl, &[q]);
                let step = d.lemma(p.add_le_add, &[zero_c, rhs, q, q, rhs_nonneg, refl_q]);
                let zero_q = cadd(d, p, zero_c, q);
                let q_zero = cadd(d, p, q, zero_c);
                let comm = d.lemma(p.add_comm, &[zero_c, q]);
                let trim = d.lemma(p.add_zero, &[q]);
                let lhs_eq = echain(d, p, zero_q, &[(q_zero, comm), (q, trim)]);
                let refl_target = erefl(d, p, rhs_q);
                d.lemma(
                    p.le_congr,
                    &[zero_q, q, rhs_q, rhs_q, lhs_eq, refl_target, step],
                )
            };
            d.lemma(p.le_trans, &[diff, q, rhs_q, le_diff_q, widen_rhs])
        },
    );

    let per_e = d.lam_fv(e_fv, nat, body);
    d.lemma(p.le_of_forall_le_add_small, &[diff, rhs, per_e])
}

/// `CReal.abs_diff_le_of_small_image` -- see
/// [`super::CRealPrelude::abs_diff_le_of_small_image`] for the statement and
/// this section's header for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_abs_diff_le_of_small_image(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hf_ty = d.const_app(p.has_derivative_on, &[f, fp, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // The SAME hypothesis shape `strict_mono_magnitude` /
    // `diff_le_of_strict_mono_magnitude` state, binder for binder.
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let a_k_rat = div_succ(d, p, 1, k);
        let a_k = embed(d, p, a_k_rat);
        let concl = cle(d, p, a_k, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    // TWO accuracies, not one. A single shared `eps` would force a caller
    // comparing indices `m` and `n` to widen both bounds to a common value
    // first, and the natural common value `1/(m+1) + 1/(n+1)` then has to be
    // un-rearranged again downstream. Kept separate, a Cauchy caller's
    // conclusion is `mul C (add (ofRat (1/(m+1))) (ofRat (1/(n+1))))`, one
    // `of_rat_add` from the `natDivSucc K m + natDivSucc K n` shape
    // `CReal.Cauchy` states.
    let eps_x_fv = d.fresh_fvar();
    let eps_x = d.kernel().fvar(eps_x_fv);
    let eps_y_fv = d.fresh_fvar();
    let eps_y = d.kernel().fvar(eps_y_fv);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hax_ty = cle(d, p, a, x);
    let hax_fv = d.fresh_fvar();
    let hax = d.kernel().fvar(hax_fv);
    let hxb_ty = cle(d, p, x, b);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let hay_ty = cle(d, p, a, y);
    let hay_fv = d.fresh_fvar();
    let hay = d.kernel().fvar(hay_fv);
    let hyb_ty = cle(d, p, y, b);
    let hyb_fv = d.fresh_fvar();
    let hyb = d.kernel().fvar(hyb_fv);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let abs_fx = cabs(d, p, fx);
    let abs_fy = cabs(d, p, fy);
    let hfx_ty = cle(d, p, abs_fx, eps_x);
    let hfx_fv = d.fresh_fvar();
    let hfx = d.kernel().fvar(hfx_fv);
    let hfy_ty = cle(d, p, abs_fy, eps_y);
    let hfy_fv = d.fresh_fvar();
    let hfy = d.kernel().fvar(hfy_fv);

    // `csucc := ofNat (2k+2)` -- byte-for-byte the constant
    // `diff_le_of_strict_mono_magnitude`'s own conclusion carries.
    let two_nat = d.num(2);
    let doubled = NatOps::mul(d, two_nat, k);
    let e_acc = d.succ(doubled);
    let e_acc_succ = d.succ(e_acc);
    let csucc = d.const_app(p.of_nat, &[e_acc_succ]);
    let eps_sum = cadd(d, p, eps_x, eps_y);
    let rhs = cmul(d, p, csucc, eps_sum);

    let zero_c = czero(d, p);
    let csucc_nonneg = nonneg_of_nat(d, p, e_acc_succ);
    let eps_x_nonneg = {
        let an = d.lemma(p.abs_nonneg, &[fx]);
        d.lemma(p.le_trans, &[zero_c, abs_fx, eps_x, an, hfx])
    };
    let eps_y_nonneg = {
        let an = d.lemma(p.abs_nonneg, &[fy]);
        d.lemma(p.le_trans, &[zero_c, abs_fy, eps_y, an, hfy])
    };
    let eps_sum_nonneg = {
        let step = d.lemma(
            p.add_le_add,
            &[zero_c, eps_x, zero_c, eps_y, eps_x_nonneg, eps_y_nonneg],
        );
        let zero_zero = cadd(d, p, zero_c, zero_c);
        let trim = d.lemma(p.add_zero, &[zero_c]);
        let refl_eps_sum = erefl(d, p, eps_sum);
        d.lemma(
            p.le_congr,
            &[
                zero_zero,
                zero_c,
                eps_sum,
                eps_sum,
                trim,
                refl_eps_sum,
                step,
            ],
        )
    };
    let rhs_nonneg = d.lemma(
        p.mul_nonneg,
        &[csucc, eps_sum, csucc_nonneg, eps_sum_nonneg],
    );

    let dp = DerivPack {
        f,
        fp,
        a,
        b,
        hf,
        k,
        hderiv,
    };

    // `le (add (abs (F y)) (abs (F x))) eps_sum` -- the `(y, x)` orientation
    // produces `eps_y + eps_x` and the statement fixes `eps_x + eps_y`, so
    // this one pays an `add_comm`; the mirror below does not.
    let widen_yx = {
        let sum_yx = cadd(d, p, abs_fy, abs_fx);
        let sum_eps_yx = cadd(d, p, eps_y, eps_x);
        let raw = d.lemma(p.add_le_add, &[abs_fy, eps_y, abs_fx, eps_x, hfy, hfx]);
        let comm = d.lemma(p.add_comm, &[eps_y, eps_x]);
        let refl_sum = erefl(d, p, sum_yx);
        d.lemma(
            p.le_congr,
            &[sum_yx, sum_yx, sum_eps_yx, eps_sum, refl_sum, comm, raw],
        )
    };
    let widen_xy = d.lemma(p.add_le_add, &[abs_fx, eps_x, abs_fy, eps_y, hfx, hfy]);

    // `le (add x (neg y)) rhs` -- the `(lo, hi) := (y, x)` orientation.
    let part_i = small_image_one_sided(
        d,
        p,
        dp,
        csucc,
        eps_sum,
        rhs,
        rhs_nonneg,
        csucc_nonneg,
        y,
        x,
        hay,
        hxb,
        widen_yx,
    );
    // `le (add y (neg x)) rhs` -- the mirror.
    let part_ii_raw = small_image_one_sided(
        d,
        p,
        dp,
        csucc,
        eps_sum,
        rhs,
        rhs_nonneg,
        csucc_nonneg,
        x,
        y,
        hax,
        hyb,
        widen_xy,
    );

    let neg_y = cneg(d, p, y);
    let neg_x = cneg(d, p, x);
    let diff_xy = cadd(d, p, x, neg_y);
    let diff_yx = cadd(d, p, y, neg_x);
    let neg_diff_xy = cneg(d, p, diff_xy);
    let part_ii = {
        let swap = d.lemma(p.neg_sub_swap, &[x, y]);
        let flipped = esymm(d, p, neg_diff_xy, diff_yx, swap);
        let refl_rhs = erefl(d, p, rhs);
        d.lemma(
            p.le_congr,
            &[
                diff_yx,
                neg_diff_xy,
                rhs,
                rhs,
                flipped,
                refl_rhs,
                part_ii_raw,
            ],
        )
    };
    let abs_diff_xy = cabs(d, p, diff_xy);
    let proof = d.lemma(p.abs_le, &[diff_xy, rhs, part_i, part_ii]);

    let value = {
        let over_hfy = d.lam_fv(hfy_fv, hfy_ty, proof);
        let over_hfx = d.lam_fv(hfx_fv, hfx_ty, over_hfy);
        let over_hyb = d.lam_fv(hyb_fv, hyb_ty, over_hfx);
        let over_hay = d.lam_fv(hay_fv, hay_ty, over_hyb);
        let over_hxb = d.lam_fv(hxb_fv, hxb_ty, over_hay);
        let over_hax = d.lam_fv(hax_fv, hax_ty, over_hxb);
        let over_y = d.lam_fv(y_fv, carrier, over_hax);
        let over_x = d.lam_fv(x_fv, carrier, over_y);
        let over_eps_y = d.lam_fv(eps_y_fv, carrier, over_x);
        let over_eps = d.lam_fv(eps_x_fv, carrier, over_eps_y);
        let over_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, over_eps);
        let over_k = d.lam_fv(k_fv, nat, over_hderiv);
        let over_hf = d.lam_fv(hf_fv, hf_ty, over_k);
        let over_b = d.lam_fv(b_fv, carrier, over_hf);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_fp = d.lam_fv(fp_fv, func_ty, over_a);
        d.lam_fv(f_fv, func_ty, over_fp)
    };
    let ty = {
        let concl = cle(d, p, abs_diff_xy, rhs);
        let after_hfy = d.arrow(hfy_ty, concl);
        let after_hfx = d.arrow(hfx_ty, after_hfy);
        let after_hyb = d.arrow(hyb_ty, after_hfx);
        let after_hay = d.arrow(hay_ty, after_hyb);
        let after_hxb = d.arrow(hxb_ty, after_hay);
        let after_hax = d.arrow(hax_ty, after_hxb);
        let over_y = d.pi_fv(y_fv, carrier, after_hax);
        let over_x = d.pi_fv(x_fv, carrier, over_y);
        let over_eps_y = d.pi_fv(eps_y_fv, carrier, over_x);
        let over_eps = d.pi_fv(eps_x_fv, carrier, over_eps_y);
        let after_hderiv = d.arrow(hderiv_ty, over_eps);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hf = d.arrow(hf_ty, over_k);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.abs_diff_le_of_small_image,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_bisect_approx` -- `ivt_approx` with the `Exists` removed.
//
// `ivt_approx` says `∀ e, ∃ x ∈ [a,b], |F x| ≤ 1/(e+1)`. Its witness is
// `ivt_iter`'s existentially-quantified bracket, so nothing outside the proof
// can NAME the point, and a SEQUENCE of such points cannot be formed at all:
// extracting one from `∀ e, ∃ x` is an `Exists` elimination into a
// `Type`-valued target, which this kernel (correctly) refuses.
//
// The bracket `ivt_bisect_lo`/`ivt_bisect_hi` computes is data, and
// `ivt_bisect_invariant` proves it satisfies the SAME six-part invariant at
// the same fixed slack. So the estimate `ivt_approx` runs
// ([`approx_endpoint_bound`], shared verbatim between the two -- not copied)
// applies to it unchanged, and the conclusion becomes a bound on a NAMED
// point:
//
//     ivt_bisect_hi F a b (succ (2*e)) (bisect_n e)
//
// with `bisect_n e` the depth [`width_le_via_bound`] already computed for
// `ivt_approx`'s own schedule -- `succ (bound (b−a)) * modulus(succ (2*e)) +
// bound (b−a)`. `fun e => …` is then an ordinary `Nat → CReal` lambda, which
// is what an exact root's Cauchy argument needs and what
// `docs/mathematics-2026-08/diary-exact-root-obstruction.md`'s first
// obstruction was about.
// =============================================================================

/// `CReal.ivt_bisect_approx` -- see
/// [`super::CRealPrelude::ivt_bisect_approx`] for the statement.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_ivt_bisect_approx(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
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

    let setup = approx_setup(d, p, f, a, b, huc, hab, hfa, hfb, e);
    let ctx = setup.ctx;
    let bisect_n = setup.bisect_n;

    // The concrete bracket, and the invariant it satisfies at this slack.
    let lo = d.const_app(p.ivt_bisect_lo, &[f, a, b, ctx.n, bisect_n]);
    let hi = d.const_app(p.ivt_bisect_hi, &[f, a, b, ctx.n, bisect_n]);
    let inv = d.lemma(
        p.ivt_bisect_invariant,
        &[f, a, b, ctx.n, hab, setup.hfp, setup.hfq, bisect_n],
    );
    let (h1, h2, h3, h4, h5, h6) =
        conj_split(d, p, f, a, b, ctx.sgn_eps, ctx.width_term, lo, hi, inv);

    let (range_a_hi, abs_bound) = approx_endpoint_bound(d, p, &ctx, lo, hi, h1, h2, h3, h4, h5, h6);

    let concl = approx_pred_body(d, p, f, a, b, ctx.target_e_rat, hi);
    let proof = {
        let le2 = cle(d, p, hi, b);
        let f_hi = d.apply(f, &[hi]);
        let abs_f_hi = cabs(d, p, f_hi);
        let target_e = embed(d, p, ctx.target_e_rat);
        let le3 = cle(d, p, abs_f_hi, target_e);
        let and2ty = d.and(le2, le3);
        let inner = and_intro(d, p, le2, le3, h3, abs_bound);
        let le1 = cle(d, p, a, hi);
        and_intro(d, p, le1, and2ty, range_a_hi, inner)
    };

    let value = {
        let with_e = d.lam_fv(e_fv, nat, proof);
        let with_hfb = d.lam_fv(hfb_fv, hfb_ty, with_e);
        let with_hfa = d.lam_fv(hfa_fv, hfa_ty, with_hfb);
        let with_hab = d.lam_fv(hab_fv, hab_ty, with_hfa);
        let with_huc = d.lam_fv(huc_fv, uc_ty_ab, with_hab);
        let with_b = d.lam_fv(b_fv, carrier, with_huc);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, fn_ty, with_a)
    };
    let ty = {
        let with_e = d.pi_fv(e_fv, nat, concl);
        let with_hfb = d.arrow(hfb_ty, with_e);
        let with_hfa = d.arrow(hfa_ty, with_hfb);
        let with_hab = d.arrow(hab_ty, with_hfa);
        // `pi_fv`, not `arrow`: the conclusion MENTIONS `huc` (the bisection
        // depth reads the continuity modulus), so a non-dependent arrow would
        // leave that occurrence free -- `UnboundFVar`, which is exactly how
        // this first went wrong.
        let with_huc = d.pi_fv(huc_fv, uc_ty_ab, with_hab);
        let with_b = d.pi_fv(b_fv, carrier, with_huc);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        d.pi_fv(f_fv, fn_ty, with_a)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_bisect_approx,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_bisect_cauchy_bound` -- the exact root's Cauchy estimate, at the
// `CReal` level.
//
// Composition of the two declarations above: `ivt_bisect_approx` says the
// NAMED point `X e := ivt_bisect_hi F a b (succ (2*e)) (K e)` lies in `[a,b]`
// with `|F (X e)| <= 1/(e+1)`, and `abs_diff_le_of_small_image` says two
// points of `[a,b]` with small `F`-values are close -- with no ordering and no
// `Apart`, which is what a bisection can actually supply. Together:
//
//     |X m - X n| <= (2k+2)/(m+1) + (2k+2)/(n+1)
//
// which is `CReal.Cauchy`'s own rate shape at `K := 2k+2`, one level up: this
// is the REAL-valued inequality, and `Cauchy` is stated on the canonical
// rational SAMPLES `seq (X m) m - seq (X n) n`. See this section's closing
// comment (and `docs/mathematics-2026-08/diary-exact-root-obstruction.md`)
// for exactly what that last bridge costs and why it is a separate, general
// lemma rather than part of this one.
// =============================================================================

/// `(n, bisect_n)` for accuracy index `e` -- the slack index `succ (2*e)` and
/// the bisection depth, built as TERMS only.
///
/// [`approx_setup`] computes the same two terms but also builds
/// [`width_le_via_bound`]'s whole proof, which a caller that only needs to
/// NAME the point does not want to pay for. Every line here mirrors
/// [`approx_setup`]/[`width_le_via_bound`] exactly, so the terms are
/// structurally identical to the ones `ivt_bisect_approx`'s statement
/// carries -- if they ever diverge, the `le_congr` in
/// [`declare_ivt_bisect_cauchy_bound`] stops matching and the kernel says so.
fn bisect_index_terms(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
    e: ExprId,
) -> (ExprId, ExprId) {
    let two_nat = d.num(2);
    let two_e = d.mul(two_nat, e);
    let n = d.succ(two_e);

    let mod_fn = d.const_app(p.uc_modulus, &[f, a, b, huc]);
    let delta = d.apply(mod_fn, &[n]);

    let neg_a = cneg(d, p, a);
    let w0 = cadd(d, p, b, neg_a);
    let magnitude = d.const_app(p.bound, &[w0]);
    let big_m = d.succ(magnitude);
    let scaled = d.mul(big_m, delta);
    let bisect_n = d.add(scaled, magnitude);
    (n, bisect_n)
}

/// The bisection point at accuracy `e` and the three facts
/// [`declare_ivt_bisect_approx`] proves about it, split out of its `And`.
///
/// Returns `(X e, le a (X e), le (X e) b, le (abs (F (X e))) (ofRat
/// (natDivSucc 1 e)))`.
#[allow(clippy::too_many_arguments)]
fn bisect_point_facts(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
    hab: ExprId,
    hfa: ExprId,
    hfb: ExprId,
    e: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let (n, bisect_n) = bisect_index_terms(d, p, f, a, b, huc, e);
    let x = d.const_app(p.ivt_bisect_hi, &[f, a, b, n, bisect_n]);
    let whole = d.lemma(p.ivt_bisect_approx, &[f, a, b, huc, hab, hfa, hfb, e]);

    let le1 = cle(d, p, a, x);
    let le2 = cle(d, p, x, b);
    let fx = d.apply(f, &[x]);
    let abs_fx = cabs(d, p, fx);
    let target_rat = div_succ(d, p, 1, e);
    let target = embed(d, p, target_rat);
    let le3 = cle(d, p, abs_fx, target);
    let and2 = d.and(le2, le3);

    let h1 = d.and_left(le1, and2, whole);
    let rest = d.and_right(le1, and2, whole);
    let h2 = d.and_left(le2, le3, rest);
    let h3 = d.and_right(le2, le3, rest);
    (x, h1, h2, h3)
}

/// `CReal.ivt_bisect_cauchy_bound` -- see
/// [`super::CRealPrelude::ivt_bisect_cauchy_bound`] for the statement.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_ivt_bisect_cauchy_bound(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hf_ty = d.const_app(p.has_derivative_on, &[f, fp, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

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

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let a_k_rat = div_succ(d, p, 1, k);
        let a_k = embed(d, p, a_k_rat);
        let concl = cle(d, p, a_k, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let (xm, ham, hmb, habs_m) = bisect_point_facts(d, p, f, a, b, huc, hab, hfa, hfb, m);
    let (xn, han, hnb, habs_n) = bisect_point_facts(d, p, f, a, b, huc, hab, hfa, hfb, n);

    let rm = div_succ(d, p, 1, m);
    let rn = div_succ(d, p, 1, n);
    let eps_x = embed(d, p, rm);
    let eps_y = embed(d, p, rn);

    let raw = d.lemma(
        p.abs_diff_le_of_small_image,
        &[
            f, fp, a, b, hf, k, hderiv, eps_x, eps_y, xm, xn, ham, hmb, han, hnb, habs_m, habs_n,
        ],
    );

    // `csucc := ofNat (2k+2)`, matching `abs_diff_le_of_small_image`'s own
    // conclusion byte for byte.
    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let doubled = NatOps::mul(d, two_nat, k);
    let e_acc = d.succ(doubled);
    let big_c = d.succ(e_acc);
    let csucc = d.const_app(p.of_nat, &[big_c]);
    let eps_sum = cadd(d, p, eps_x, eps_y);
    let lhs = cmul(d, p, csucc, eps_sum);

    // `cq` is the rational `CReal.ofNat (2k+2)` δ-unfolds to, so
    // `mul csucc (ofRat r)` and `mul (ofRat cq) (ofRat r)` are the same term
    // to the kernel and `ofRat_mul` applies directly.
    let zero_nat = d.num(0);
    let cq = d.const_app(rat.nat_div_succ, &[big_c, zero_nat]);

    let sum_rat = radd(d, rm, rn);
    let of_rat_sum = embed(d, p, sum_rat);

    let chain_to_product = {
        let refl_c = erefl(d, p, csucc);
        let add_eq = d.lemma(p.of_rat_add, &[rm, rn]);
        let step_a = d.lemma(
            p.mul_congr,
            &[csucc, csucc, eps_sum, of_rat_sum, refl_c, add_eq],
        );
        // step_a : Equiv lhs (mul csucc of_rat_sum)
        let step_b = d.lemma(p.of_rat_mul, &[cq, sum_rat]);
        // step_b : Equiv (mul (ofRat cq) of_rat_sum) (ofRat (cq * sum_rat)),
        // and its left-hand side IS `mul csucc of_rat_sum` by δ.
        let mul_csucc_sum = cmul(d, p, csucc, of_rat_sum);
        let prod_rat = rmul(d, cq, sum_rat);
        let of_rat_prod = embed(d, p, prod_rat);
        d.lemma(
            p.equiv_trans,
            &[lhs, mul_csucc_sum, of_rat_prod, step_a, step_b],
        )
    };

    // Now rewrite the RATIONAL, one subterm at a time, under the motive
    // `fun t => Equiv lhs (ofRat t)`.
    let prod_rat = rmul(d, cq, sum_rat);
    let cq_rm = rmul(d, cq, rm);
    let cq_rn = rmul(d, cq, rn);
    let distributed = radd(d, cq_rm, cq_rn);
    let c_times_one = NatOps::mul(d, big_c, one_nat);
    let folded_m = d.const_app(rat.nat_div_succ, &[c_times_one, m]);
    let folded_n = d.const_app(rat.nat_div_succ, &[c_times_one, n]);
    let final_m = d.const_app(rat.nat_div_succ, &[big_c, m]);
    let final_n = d.const_app(rat.nat_div_succ, &[big_c, n]);

    let whole_motive = |d: &mut IntDev<'_>, t: ExprId| {
        let oft = d.const_app(p.of_rat, &[t]);
        d.const_app(p.equiv, &[lhs, oft])
    };

    let after_distrib = {
        let eq = d.lemma(rat.left_distrib, &[cq, rm, rn]);
        rat_eq_rewrite(
            d,
            prod_rat,
            distributed,
            eq,
            chain_to_product,
            &whole_motive,
        )
    };
    // Each remaining step rewrites a SUBTERM, so its `from`/`to` are that
    // subterm and the motive carries the surrounding sum. Passing the whole
    // rational as `from` while the motive also wraps it duplicates the
    // context -- the kernel's first rejection here reported a right-hand side
    // with `cq * rn` appearing twice, which is exactly that.
    let after_fold_m = {
        let eq = d.lemma(rat.nat_div_succ_mul, &[big_c, one_nat, m]);
        rat_eq_rewrite(d, cq_rm, folded_m, eq, after_distrib, &|d, t| {
            let sum = radd(d, t, cq_rn);
            whole_motive(d, sum)
        })
    };
    let after_fold_n = {
        let eq = d.lemma(rat.nat_div_succ_mul, &[big_c, one_nat, n]);
        rat_eq_rewrite(d, cq_rn, folded_n, eq, after_fold_m, &|d, t| {
            let sum = radd(d, folded_m, t);
            whole_motive(d, sum)
        })
    };
    // `Nat.mul C 1 = C`, lifted into the numerator slot on each side.
    let mul_one_eq = d.lemma(rat.int.nat.mul_one, &[big_c]);
    let after_trim_m = {
        let eq = nat_eq_to_rat(d, c_times_one, big_c, mul_one_eq, &|d, x| {
            d.const_app(rat.nat_div_succ, &[x, m])
        });
        rat_eq_rewrite(d, folded_m, final_m, eq, after_fold_n, &|d, t| {
            let sum = radd(d, t, folded_n);
            whole_motive(d, sum)
        })
    };
    let after_trim_n = {
        let eq = nat_eq_to_rat(d, c_times_one, big_c, mul_one_eq, &|d, x| {
            d.const_app(rat.nat_div_succ, &[x, n])
        });
        rat_eq_rewrite(d, folded_n, final_n, eq, after_trim_m, &|d, t| {
            let sum = radd(d, final_m, t);
            whole_motive(d, sum)
        })
    };
    // after_trim_n : Equiv lhs (ofRat (natDivSucc C m + natDivSucc C n))

    let target_rat = radd(d, final_m, final_n);
    let target = embed(d, p, target_rat);
    let neg_xn = cneg(d, p, xn);
    let diff = cadd(d, p, xm, neg_xn);
    let abs_diff = cabs(d, p, diff);

    let proof = {
        let refl_lhs = erefl(d, p, abs_diff);
        d.lemma(
            p.le_congr,
            &[abs_diff, abs_diff, lhs, target, refl_lhs, after_trim_n, raw],
        )
    };

    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, over_m);
        let over_k = d.lam_fv(k_fv, nat, over_hderiv);
        let over_hfb = d.lam_fv(hfb_fv, hfb_ty, over_k);
        let over_hfa = d.lam_fv(hfa_fv, hfa_ty, over_hfb);
        let over_hab = d.lam_fv(hab_fv, hab_ty, over_hfa);
        let over_huc = d.lam_fv(huc_fv, uc_ty_ab, over_hab);
        let over_hf = d.lam_fv(hf_fv, hf_ty, over_huc);
        let over_b = d.lam_fv(b_fv, carrier, over_hf);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_fp = d.lam_fv(fp_fv, func_ty, over_a);
        d.lam_fv(f_fv, func_ty, over_fp)
    };
    let ty = {
        let concl = cle(d, p, abs_diff, target);
        let over_n = d.pi_fv(n_fv, nat, concl);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let after_hderiv = d.arrow(hderiv_ty, over_m);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hfb = d.arrow(hfb_ty, over_k);
        let after_hfa = d.arrow(hfa_ty, after_hfb);
        let after_hab = d.arrow(hab_ty, after_hfa);
        // `pi_fv`: the conclusion names `X m`/`X n`, whose bisection depth
        // reads `ucModulus F a b huc`.
        let over_huc = d.pi_fv(huc_fv, uc_ty_ab, after_hab);
        let after_hf = d.arrow(hf_ty, over_huc);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_bisect_cauchy_bound,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.cauchy_of_abs_diff_le` -- the REAL-valued Cauchy criterion to
// `CReal.Cauchy`'s canonical-sample form.
//
// `Cauchy f` is stated on the canonical rational SAMPLES,
// `Within (seq (f m) m - seq (f n) n) (K/(m+1) + K/(n+1))`, while every
// estimate that produces a Cauchy sequence in this development produces a
// REAL inequality, `le (abs (f m - f n)) (ofRat (K/(m+1) + K/(n+1)))`. No
// lemma crossed that gap in this direction: `close_within_of_within` and
// `close_within_of_within_indexed` run the other way, and
// `riemannSum_cauchy`'s own doc comment records the same gap for the
// integral ("NOT `CReal.Cauchy` in that definition's own canonical-index
// shape ... separate, unattempted work").
//
// The route, and the two index choices that make the arithmetic exact:
//
//   1. `within_of_two_sided_le` turns the real bound into
//      `Within (seq (f m - f n) i) (qmn + 2/(i+1))` at an arbitrary SHARED
//      index `i`, where `qmn := K/(m+1) + K/(n+1)`.
//   2. `sharedIndexToCanonical` moves from that shared index to the two
//      canonical ones, at the cost of two regularity legs:
//
//          ((1/(m+1) + 1/(sj+1)) + (qmn + 2/(j+1))) + (1/(sj+1) + 1/(n+1))
//
//      with `sj := 2j+1` and `j` free.
//   3. Choose `j := 3*m + 2`. Then BOTH slack groups collapse EXACTLY, with
//      no inequality: `Rat.natDivSucc_halve j` makes `1/(sj+1) + 1/(sj+1)`
//      exactly `1/(j+1)`, `Rat.natDivSucc_add` fuses that with `2/(j+1)` to
//      `3/(j+1)`, and `Rat.natDivSucc_scale 2 m` makes `3/(j+1)` exactly
//      `1/(m+1)`. The seven-term bound is therefore EQUAL to
//      `(K+2)/(m+1) + (K+1)/(n+1)`, and the only inequality in the whole
//      proof is the final `Rat.natDivSucc_le_add_left` widening the second
//      numerator to `K+2`.
//
// The permutation that groups the seven summands is `rsum_perm`, not an
// inline chain of `add_assoc`/`add_comm`: it panics on a non-permutation, so
// a mis-derived rearrangement fails with a Rust message naming the two lists
// rather than as an opaque `TypeMismatch` a thousand terms deep.
// =============================================================================

/// `CReal.cauchy_of_abs_diff_le` -- see
/// [`super::CRealPrelude::cauchy_of_abs_diff_le`] for the statement and this
/// section's header for the route.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_cauchy_of_abs_diff_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, carrier);
    let rat = p.rat;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let cap_k_fv = d.fresh_fvar();
    let cap_k = d.kernel().fvar(cap_k_fv);

    // The hypothesis, at a fresh pair of indices.
    let hyp_ty = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fm = d.apply(f, &[m]);
        let fn_ = d.apply(f, &[n]);
        let neg_fn = cneg(d, p, fn_);
        let diff = cadd(d, p, fm, neg_fn);
        let abs_diff = cabs(d, p, diff);
        let qm = div_succ_k(d, p, cap_k, m);
        let qn = div_succ_k(d, p, cap_k, n);
        let qmn = radd(d, qm, qn);
        let bound = embed(d, p, qmn);
        let claim = cle(d, p, abs_diff, bound);
        let over_n = d.pi_fv(n_fv, nat, claim);
        d.pi_fv(m_fv, nat, over_n)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let two_nat = d.num(2);
    let one_nat = d.num(1);
    let k2 = d.add(cap_k, two_nat);

    // `λ K, ∀ m n, Within (seq (f m) m − seq (f n) n)
    //   (natDivSucc K m + natDivSucc K n)` -- `convergence.rs`'s
    // `cauchy_predicate`, rebuilt here because that helper is private to its
    // own module. `Cauchy f` δ-reduces to `Exists Nat` of exactly this.
    let cauchy_pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fm = d.apply(f, &[m]);
        let fn_ = d.apply(f, &[n]);
        let left = sample(d, p, fm, m);
        let right = sample(d, p, fn_, n);
        let difference = rsub(d, rat, left, right);
        let bm = div_succ_k(d, p, k, m);
        let bn = div_succ_k(d, p, k, n);
        let bound = radd(d, bm, bn);
        let claim = within(d, p, difference, bound);
        let over_n = d.pi_fv(n_fv, nat, claim);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.lam_fv(k_fv, nat, over_m)
    };

    // The body, at a concrete pair `(m, n)`.
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let fm = d.apply(f, &[m]);
    let fn_ = d.apply(f, &[n]);
    let neg_fn = cneg(d, p, fn_);
    let t = cadd(d, p, fm, neg_fn);
    let abs_t = cabs(d, p, t);

    let a_atom = div_succ(d, p, 1, m);
    let e_atom = div_succ(d, p, 1, n);
    let qm = div_succ_k(d, p, cap_k, m);
    let qn = div_succ_k(d, p, cap_k, n);
    let qmn = radd(d, qm, qn);
    let y = embed(d, p, qmn);

    let h_mn = d.apply(hyp, &[m, n]);
    let ht = {
        let self_le = d.lemma(p.le_abs_self, &[t]);
        d.lemma(p.le_trans, &[t, abs_t, y, self_le, h_mn])
    };
    let hnt = {
        let neg_t = cneg(d, p, t);
        let neg_le = d.lemma(p.neg_le_abs, &[t]);
        d.lemma(p.le_trans, &[neg_t, abs_t, y, neg_le, h_mn])
    };

    // `bound i := seq y i + 2/(i+1)` -- exactly `within_of_two_sided_le`'s
    // own conclusion, so `w` inhabits `∀ i, Within (seq t i) (bound i)`
    // with no transport.
    let bound_lam = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let seq_y_i = sample(d, p, y, i);
        let slack = div_succ(d, p, 2, i);
        let body = radd(d, seq_y_i, slack);
        d.lam_fv(i_fv, nat, body)
    };
    let w = d.lemma(p.within_of_two_sided_le, &[t, y, ht, hnt]);

    // `j := 3*m + 2` -- `Rat.natDivSucc_scale`'s own `(c+1)*m + c` index at
    // `c := 2`, so `3/(j+1)` is EXACTLY `1/(m+1)`.
    let three_nat = d.succ(two_nat);
    let j = {
        let scaled = NatOps::mul(d, three_nat, m);
        d.add(scaled, two_nat)
    };
    let sj = {
        let doubled = NatOps::mul(d, two_nat, j);
        d.succ(doubled)
    };

    let sic = d.lemma(
        p.shared_index_to_canonical,
        &[fm, fn_, bound_lam, w, m, n, j],
    );

    // The bound `sic` carries, with `bound_lam j` β-reduced and
    // `seq (ofRat qmn) j` ι-reduced to `qmn` (both hold definitionally, so
    // `sic` inhabits this type unchanged).
    let b_atom = div_succ(d, p, 1, sj);
    let d_atom = div_succ(d, p, 2, j);
    let leg1 = modulus(d, p, m, sj);
    let leg3 = modulus(d, p, sj, n);
    let bound_j = radd(d, qmn, d_atom);
    let leg12 = radd(d, leg1, bound_j);
    let total = radd(d, leg12, leg3);

    // --- the rational identity -------------------------------------------
    // total = rsum [A, B, QM, QN, D, B, E]
    let flat = [a_atom, b_atom, qm, qn, d_atom, b_atom, e_atom];
    let flatten = {
        // (QM + QN) + D  =  rsum [QM, QN, D]
        let qmn_d = rsum(d, rat, &[qm, qn, d_atom]);
        let step_inner = rsum_append(d, rat, &[qm, qn], &[d_atom]);
        // (A + B) + ((QM+QN)+D)  =  (A + B) + rsum [QM,QN,D]
        let ab = radd(d, a_atom, b_atom);
        let step_leg12 = rcongr(d, bound_j, qmn_d, step_inner, &|d, tm| radd(d, ab, tm));
        let leg12_mid = radd(d, ab, qmn_d);
        // (A + B) + rsum [QM,QN,D]  =  rsum [A,B,QM,QN,D]
        let five = rsum(d, rat, &[a_atom, b_atom, qm, qn, d_atom]);
        let step_five = rsum_append(d, rat, &[a_atom, b_atom], &[qm, qn, d_atom]);
        let (_, leg12_eq) = rchain(d, leg12, &[(leg12_mid, step_leg12), (five, step_five)]);
        // total = rsum[A,B,QM,QN,D] + (B + E)
        let step_top = rcongr(d, leg12, five, leg12_eq, &|d, tm| radd(d, tm, leg3));
        let top_mid = radd(d, five, leg3);
        let all = rsum(d, rat, &flat);
        let step_join = rsum_append(d, rat, &[a_atom, b_atom, qm, qn, d_atom], &[b_atom, e_atom]);
        let (_, eq) = rchain(d, total, &[(top_mid, step_top), (all, step_join)]);
        eq
    };
    let flat_sum = rsum(d, rat, &flat);

    // Permute so the three slack atoms sit at the TAIL, where `B + (B + D)`
    // is a genuine subterm of the right-nested sum.
    let sorted = [qm, a_atom, qn, e_atom, b_atom, b_atom, d_atom];
    let perm = rsum_perm(d, rat, &flat, &sorted);
    let sorted_sum = rsum(d, rat, &sorted);

    // `B + (B + D) = 1/(m+1)`, exactly.
    let slack_sum = rsum(d, rat, &[b_atom, b_atom, d_atom]);
    let slack_eq = {
        // B + (B + D) = (B + B) + D
        let bb = radd(d, b_atom, b_atom);
        let assoc = d.lemma(rat.add_assoc, &[b_atom, b_atom, d_atom]);
        let left_nested = radd(d, bb, d_atom);
        let step0 = rsymm(d, left_nested, slack_sum, assoc);
        // B + B = natDivSucc (1+1) sj = natDivSucc 2 sj
        let one_one = d.add(one_nat, one_nat);
        let fused_raw = d.const_app(rat.nat_div_succ, &[one_one, sj]);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, sj]);
        let two_sj = d.const_app(rat.nat_div_succ, &[two_nat, sj]);
        let renumber = {
            let refl_two = d.refl(two_nat);
            nat_eq_to_rat(d, one_one, two_nat, refl_two, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, sj])
            })
        };
        // natDivSucc 2 sj = natDivSucc 1 j
        let halve = d.lemma(rat.nat_div_succ_halve, &[j]);
        let one_j = div_succ(d, p, 1, j);
        let (_, bb_eq) = rchain(
            d,
            bb,
            &[(fused_raw, fuse), (two_sj, renumber), (one_j, halve)],
        );
        let step1 = rcongr(d, bb, one_j, bb_eq, &|d, tm| radd(d, tm, d_atom));
        let after_bb = radd(d, one_j, d_atom);
        // 1/(j+1) + 2/(j+1) = natDivSucc (1+2) j = natDivSucc 3 j
        let one_two = d.add(one_nat, two_nat);
        let fused3_raw = d.const_app(rat.nat_div_succ, &[one_two, j]);
        let fuse3 = d.lemma(rat.nat_div_succ_add, &[one_nat, two_nat, j]);
        let three_j = d.const_app(rat.nat_div_succ, &[three_nat, j]);
        let renumber3 = {
            let refl_three = d.refl(three_nat);
            nat_eq_to_rat(d, one_two, three_nat, refl_three, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, j])
            })
        };
        // natDivSucc 3 (3*m+2) = natDivSucc 1 m
        let scale = d.lemma(rat.nat_div_succ_scale, &[two_nat, m]);
        let (_, eq) = rchain(
            d,
            slack_sum,
            &[
                (left_nested, step0),
                (after_bb, step1),
                (fused3_raw, fuse3),
                (three_j, renumber3),
                (a_atom, scale),
            ],
        );
        eq
    };
    let collapsed = [qm, a_atom, qn, e_atom, a_atom];
    let collapse_step = rcongr(d, slack_sum, a_atom, slack_eq, &|d, tm| {
        let i1 = radd(d, e_atom, tm);
        let i2 = radd(d, qn, i1);
        let i3 = radd(d, a_atom, i2);
        radd(d, qm, i3)
    });
    let collapsed_sum = rsum(d, rat, &collapsed);

    // Group the two indices.
    let grouped = [qm, a_atom, a_atom, qn, e_atom];
    let regroup = rsum_perm(d, rat, &collapsed, &grouped);
    let grouped_sum = rsum(d, rat, &grouped);
    let left_three = rsum(d, rat, &[qm, a_atom, a_atom]);
    let right_two = rsum(d, rat, &[qn, e_atom]);
    let split = {
        let app = rsum_append(d, rat, &[qm, a_atom, a_atom], &[qn, e_atom]);
        let joined = radd(d, left_three, right_two);
        rsymm(d, joined, grouped_sum, app)
    };
    let joined = radd(d, left_three, right_two);

    // `QM + (A + A) = natDivSucc (K+2) m` and `QN + E = natDivSucc (K+1) n`.
    let km = div_succ_k(d, p, k2, m);
    let k1 = d.add(cap_k, one_nat);
    let kn1 = div_succ_k(d, p, k1, n);
    let kn2 = div_succ_k(d, p, k2, n);
    let left_eq = {
        let aa = radd(d, a_atom, a_atom);
        let one_one = d.add(one_nat, one_nat);
        let fused_raw = d.const_app(rat.nat_div_succ, &[one_one, m]);
        let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, m]);
        let two_m = d.const_app(rat.nat_div_succ, &[two_nat, m]);
        let renumber = {
            let refl_two = d.refl(two_nat);
            nat_eq_to_rat(d, one_one, two_nat, refl_two, &|d, x| {
                d.const_app(rat.nat_div_succ, &[x, m])
            })
        };
        let (_, aa_eq) = rchain(d, aa, &[(fused_raw, fuse), (two_m, renumber)]);
        let step = rcongr(d, aa, two_m, aa_eq, &|d, tm| radd(d, qm, tm));
        let mid = radd(d, qm, two_m);
        let fuse_k = d.lemma(rat.nat_div_succ_add, &[cap_k, two_nat, m]);
        let (_, eq) = rchain(d, left_three, &[(mid, step), (km, fuse_k)]);
        eq
    };
    let right_eq = d.lemma(rat.nat_div_succ_add, &[cap_k, one_nat, n]);
    let fold_left = rcongr(d, left_three, km, left_eq, &|d, tm| radd(d, tm, right_two));
    let after_left = radd(d, km, right_two);
    let fold_right = rcongr(d, right_two, kn1, right_eq, &|d, tm| radd(d, km, tm));
    let target1 = radd(d, km, kn1);
    let target2 = radd(d, km, kn2);

    let (_, total_eq) = rchain(
        d,
        total,
        &[
            (flat_sum, flatten),
            (sorted_sum, perm),
            (collapsed_sum, collapse_step),
            (grouped_sum, regroup),
            (joined, split),
            (after_left, fold_left),
            (target1, fold_right),
        ],
    );
    // total_eq : Eq total (natDivSucc (K+2) m + natDivSucc (K+1) n)

    let order = {
        let refl_km = d.lemma(rat.le_refl, &[km]);
        let widen_n = d.lemma(rat.nat_div_succ_le_add_left, &[k1, one_nat, n]);
        d.lemma(rat.add_le_add, &[km, km, kn1, kn2, refl_km, widen_n])
    };
    // order : Rat.le target1 target2
    let total_le = {
        let back = rsymm(d, total, target1, total_eq);
        rat_eq_rewrite(d, target1, total, back, order, &|d, tm| {
            rle(d, rat, tm, target2)
        })
    };
    // total_le : Rat.le total target2

    let left_sample = sample(d, p, fm, m);
    let right_sample = sample(d, p, fn_, n);
    let difference = rsub(d, rat, left_sample, right_sample);
    let body = weaken(d, p, difference, total, target2, sic, total_le);

    let per_pair = {
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n)
    };

    // The RAW `(K+2, per-pair)` pair, landed as its own declaration before the
    // existential closes over `K`.
    //
    // `CReal.regular_of_scaled_cauchy` needs exactly this shape as DATA, and
    // kernel fact 2 (`Exists.rec` is `Prop`-only) means it can never be
    // recovered from `Cauchy f`. So every construction that turns a
    // real-valued Cauchy estimate into an actual `CReal` -- `CReal.supOn`
    // (`creal/supremum.rs`) is the first -- would otherwise have to reproduce
    // this whole 300-line seven-term bound beside it. Extracted rather than
    // duplicated: two proofs of one fact that must stay in sync is worse than
    // one shared lemma, and the kernel would happily verify both.
    let raw_ty = {
        let mm_fv = d.fresh_fvar();
        let mm = d.kernel().fvar(mm_fv);
        let nn_fv = d.fresh_fvar();
        let nn = d.kernel().fvar(nn_fv);
        let fmm = d.apply(f, &[mm]);
        let fnn = d.apply(f, &[nn]);
        let left = sample(d, p, fmm, mm);
        let right = sample(d, p, fnn, nn);
        let difference = rsub(d, rat, left, right);
        let bm = div_succ_k(d, p, k2, mm);
        let bn = div_succ_k(d, p, k2, nn);
        let bound = radd(d, bm, bn);
        let claim = within(d, p, difference, bound);
        let over_n = d.pi_fv(nn_fv, nat, claim);
        d.pi_fv(mm_fv, nat, over_n)
    };
    let raw_decl_ty = {
        let after_hyp = d.arrow(hyp_ty, raw_ty);
        let over_k = d.pi_fv(cap_k_fv, nat, after_hyp);
        d.pi_fv(f_fv, seq_ty, over_k)
    };
    let raw_decl_value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, per_pair);
        let over_k = d.lam_fv(cap_k_fv, nat, over_hyp);
        d.lam_fv(f_fv, seq_ty, over_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.scaled_cauchy_of_abs_diff_le,
        uparams: vec![],
        ty: raw_decl_ty,
        value: raw_decl_value,
    })?;

    let raw = d.lemma(p.scaled_cauchy_of_abs_diff_le, &[f, cap_k, hyp]);
    let witness = cexists_intro(d, p, nat, cauchy_pred, k2, raw);

    let value = {
        let over_hyp = d.lam_fv(hyp_fv, hyp_ty, witness);
        let over_k = d.lam_fv(cap_k_fv, nat, over_hyp);
        d.lam_fv(f_fv, seq_ty, over_k)
    };
    let ty = {
        let concl = d.const_app(p.cauchy, &[f]);
        let after_hyp = d.arrow(hyp_ty, concl);
        let over_k = d.pi_fv(cap_k_fv, nat, after_hyp);
        d.pi_fv(f_fv, seq_ty, over_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.cauchy_of_abs_diff_le,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_bisect_cauchy` -- the bisection sequence is Cauchy, as a
// `Nat -> CReal` LAMBDA.
//
// `ivt_bisect_cauchy_bound` composed with `cauchy_of_abs_diff_le`. What is
// new here is not the estimate but the SHAPE: the sequence
//
//     fun e => ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) (K e)
//
// is an ordinary lambda, so it can be the argument of `Cauchy`,
// `Converges`, `converges_of_cauchy`, `converges_lower_bound`, and
// `converges_comp_eventually` -- none of which a sequence of `ivt_approx`
// witnesses could ever be, because `forall e, exists x` does not eliminate
// into a `Type`.
// =============================================================================

/// The bisection sequence as a `Nat -> CReal` lambda:
/// `fun e => ivt_bisect_hi F a b (Nat.succ (Nat.mul 2 e)) (K e)`.
fn bisect_sequence(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    huc: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let (n, bisect_n) = bisect_index_terms(d, p, f, a, b, huc, e);
    let body = d.const_app(p.ivt_bisect_hi, &[f, a, b, n, bisect_n]);
    d.lam_fv(e_fv, nat, body)
}

/// `CReal.ivt_bisect_cauchy` -- see
/// [`super::CRealPrelude::ivt_bisect_cauchy`] for the statement.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_ivt_bisect_cauchy(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hf_ty = d.const_app(p.has_derivative_on, &[f, fp, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

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

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let a_k_rat = div_succ(d, p, 1, k);
        let a_k = embed(d, p, a_k_rat);
        let concl = cle(d, p, a_k, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let seq_lam = bisect_sequence(d, p, f, a, b, huc);

    let two_nat = d.num(2);
    let doubled = NatOps::mul(d, two_nat, k);
    let e_acc = d.succ(doubled);
    let big_c = d.succ(e_acc);

    // `fun m n => ivt_bisect_cauchy_bound … m n`. Its body's type names the
    // bisection point directly; `seq_lam m` β-reduces to exactly that, so the
    // kernel accepts this against `cauchy_of_abs_diff_le`'s hypothesis with
    // no transport.
    let hyp = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.lemma(
            p.ivt_bisect_cauchy_bound,
            &[f, fp, a, b, hf, huc, hab, hfa, hfb, k, hderiv, m, n],
        );
        let over_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(m_fv, nat, over_n)
    };
    let proof = d.lemma(p.cauchy_of_abs_diff_le, &[seq_lam, big_c, hyp]);

    let value = {
        let over_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, proof);
        let over_k = d.lam_fv(k_fv, nat, over_hderiv);
        let over_hfb = d.lam_fv(hfb_fv, hfb_ty, over_k);
        let over_hfa = d.lam_fv(hfa_fv, hfa_ty, over_hfb);
        let over_hab = d.lam_fv(hab_fv, hab_ty, over_hfa);
        let over_huc = d.lam_fv(huc_fv, uc_ty_ab, over_hab);
        let over_hf = d.lam_fv(hf_fv, hf_ty, over_huc);
        let over_b = d.lam_fv(b_fv, carrier, over_hf);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_fp = d.lam_fv(fp_fv, func_ty, over_a);
        d.lam_fv(f_fv, func_ty, over_fp)
    };
    let ty = {
        let concl = d.const_app(p.cauchy, &[seq_lam]);
        let after_hderiv = d.arrow(hderiv_ty, concl);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hfb = d.arrow(hfb_ty, over_k);
        let after_hfa = d.arrow(hfa_ty, after_hfb);
        let after_hab = d.arrow(hab_ty, after_hfa);
        let over_huc = d.pi_fv(huc_fv, uc_ty_ab, after_hab);
        let after_hf = d.arrow(hf_ty, over_huc);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_bisect_cauchy,
        uparams: vec![],
        ty,
        value,
    })
}

// =============================================================================
// `CReal.ivt_exact_root` -- an EXACT root: a point `c` with `Equiv (F c) zero`
// outright, not `|F c| <= eps` per accuracy.
//
// This is the statement `ivt_approx` deliberately declines to prove, and the
// classical IVT is genuinely unavailable constructively (see this file's
// module documentation). It becomes available under ONE extra hypothesis:
// a uniformly positive derivative, `1/(k+1) <= F' z` on `[a,b]`. That
// hypothesis does not make the sign of a real decidable -- nothing here
// decides one -- it makes the root UNIQUE with a modulus, which is exactly
// what turns a sequence of approximate roots into a Cauchy sequence.
//
// The five steps, each discharged by a named declaration:
//
//   1. the sequence, as DATA -- `ivt_bisect_hi`, and `ivt_bisect_cauchy`'s
//      `fun e => ...` lambda. No `Exists.rec` into `Type` anywhere.
//   2. `|F (X e)| <= 1/(e+1)` -- `ivt_bisect_approx`.
//   3. `X` is Cauchy -- `ivt_bisect_cauchy` (via `abs_diff_le_of_small_image`
//      and `cauchy_of_abs_diff_le`).
//   4. the limit -- `converges_of_cauchy`, whose existential IS eliminable
//      here because the final target is a `Prop`; the domain conjuncts are
//      `converges_lower_bound`/`converges_upper_bound` against step 2's own
//      per-index bounds.
//   5. `F L ~ 0` -- `converges_comp_eventually` at accuracy `2e+1` gives an
//      `N` past which `|F (X n) - F L| <= 1/(2e+2)`; step 2 at any
//      `n := N + (2e+1)` gives `|F (X n)| <= 1/(n+1) <= 1/(2e+2)`; the
//      triangle inequality sums them to `1/(e+1)`, and
//      `equiv_zero_of_small` converts "under every 1/(e+1)" into `Equiv`.
//
// Step 5's two `1/(2e+2)` halves fuse to `1/(e+1)` by the same
// `sgn_eps_double_eq_target` identity `ivt_approx` uses, at the same index
// shape `2e+1`.
// =============================================================================

/// `le (abs (add x (neg y))) (ofRat q)` — the real-valued closeness bound
/// `converges_comp_eventually` concludes in. A private copy of the same
/// helper in `convergence.rs`/`uniform_continuity.rs`/`integral.rs`, per this
/// file's own convention (each is a sibling module, so none sees another's
/// `fn`).
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let magnitude = cabs(d, p, diff);
    let target = embed(d, p, q);
    cle(d, p, magnitude, target)
}

/// From `h : le (abs (add x (neg y))) bound`, the same bound on the REVERSED
/// difference, `le (abs (add y (neg x))) bound`.
///
/// [`super::CRealPrelude::abs_le`] over the two halves, each transported
/// across [`super::CRealPrelude::neg_sub_swap`]; there is no
/// `CReal.abs_neg`/`abs_sub_comm` to do it in one step.
fn abs_diff_symm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let neg_y = cneg(d, p, y);
    let neg_x = cneg(d, p, x);
    let diff_xy = cadd(d, p, x, neg_y);
    let diff_yx = cadd(d, p, y, neg_x);
    let abs_xy = cabs(d, p, diff_xy);
    let neg_diff_yx = cneg(d, p, diff_yx);

    let upper_xy = {
        let self_le = d.lemma(p.le_abs_self, &[diff_xy]);
        d.lemma(p.le_trans, &[diff_xy, abs_xy, bound, self_le, h])
    };
    let lower_xy = {
        let neg_diff_xy = cneg(d, p, diff_xy);
        let neg_le = d.lemma(p.neg_le_abs, &[diff_xy]);
        d.lemma(p.le_trans, &[neg_diff_xy, abs_xy, bound, neg_le, h])
    };

    // `neg (add y (neg x)) ~ add x (neg y)`, so `upper_xy` IS the lower half
    // of the reversed bound.
    let lower_yx = {
        let swap = d.lemma(p.neg_sub_swap, &[y, x]);
        let back = esymm(d, p, neg_diff_yx, diff_xy, swap);
        let refl_bound = erefl(d, p, bound);
        d.lemma(
            p.le_congr,
            &[
                diff_xy,
                neg_diff_yx,
                bound,
                bound,
                back,
                refl_bound,
                upper_xy,
            ],
        )
    };
    // `neg (add x (neg y)) ~ add y (neg x)`, so `lower_xy` IS the upper half.
    let upper_yx = {
        let neg_diff_xy = cneg(d, p, diff_xy);
        let swap = d.lemma(p.neg_sub_swap, &[x, y]);
        let refl_bound = erefl(d, p, bound);
        d.lemma(
            p.le_congr,
            &[
                neg_diff_xy,
                diff_yx,
                bound,
                bound,
                swap,
                refl_bound,
                lower_xy,
            ],
        )
    };
    d.lemma(p.abs_le, &[diff_yx, bound, upper_yx, lower_yx])
}

/// `CReal.ivt_exact_root` -- see
/// [`super::CRealPrelude::ivt_exact_root`] for the statement and this
/// section's header for the five steps.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_ivt_exact_root(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = d.arrow(carrier, carrier);
    let nat = d.nat_ty();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let hf_ty = d.const_app(p.has_derivative_on, &[f, fp, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

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

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hderiv_ty = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let fpz = d.apply(fp, &[z]);
        let a_k_rat = div_succ(d, p, 1, k);
        let a_k = embed(d, p, a_k_rat);
        let concl = cle(d, p, a_k, fpz);
        let z_le_b = cle(d, p, z, b);
        let after_upper = d.arrow(z_le_b, concl);
        let a_le_z = cle(d, p, a, z);
        let after_lower = d.arrow(a_le_z, after_upper);
        d.pi_fv(z_fv, carrier, after_lower)
    };
    let hderiv_fv = d.fresh_fvar();
    let hderiv = d.kernel().fvar(hderiv_fv);

    let seq_lam = bisect_sequence(d, p, f, a, b, huc);

    // The three per-index facts, as lambdas over the accuracy. Each body's
    // type names the bisection point directly; `seq_lam e` β-reduces to it.
    let mk_pointwise = |d: &mut IntDev<'_>, which: usize| -> ExprId {
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let (_, h1, h2, h3) = bisect_point_facts(d, p, f, a, b, huc, hab, hfa, hfb, e);
        let body = match which {
            0 => h1,
            1 => h2,
            _ => h3,
        };
        d.lam_fv(e_fv, nat, body)
    };
    let hlow = mk_pointwise(d, 0);
    let hhigh = mk_pointwise(d, 1);
    let habs = mk_pointwise(d, 2);

    let hcauchy = d.lemma(
        p.ivt_bisect_cauchy,
        &[f, fp, a, b, hf, huc, hab, hfa, hfb, k, hderiv],
    );
    let hex = d.lemma(p.converges_of_cauchy, &[seq_lam, hcauchy]);

    // The target: `∃ c, le a c ∧ (le c b ∧ Equiv (F c) zero)`.
    let root_pred = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let le1 = cle(d, p, a, c);
        let le2 = cle(d, p, c, b);
        let fc = d.apply(f, &[c]);
        let eq0 = equiv(d, p, fc, zero_c);
        let inner = d.and(le2, eq0);
        let body = d.and(le1, inner);
        d.lam_fv(c_fv, carrier, body)
    };
    let target_ty = cexists_ty(d, p, carrier, root_pred);

    // `λ L, Converges seq_lam L` -- `converges_of_cauchy`'s own predicate.
    let conv_pred = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let body = d.const_app(p.converges, &[seq_lam, l]);
        d.lam_fv(l_fv, carrier, body)
    };

    let minor = {
        let l_fv = d.fresh_fvar();
        let big_l = d.kernel().fvar(l_fv);
        let hl_ty = d.const_app(p.converges, &[seq_lam, big_l]);
        let hl_fv = d.fresh_fvar();
        let hl = d.kernel().fvar(hl_fv);

        let ha_l = d.lemma(p.converges_lower_bound, &[a, seq_lam, big_l, hlow, hl]);
        let hl_b = d.lemma(p.converges_upper_bound, &[seq_lam, big_l, b, hhigh, hl]);

        let f_l = d.apply(f, &[big_l]);

        // `∀ e, le (abs (F L)) (ofRat (natDivSucc 1 e))`.
        let per_e = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let (n0, sgn_eps, sgn_eps_rat, _sgn_eps_pos) = sgn_eps_of(d, p, e);
            let (target_e_rat, double_eq_target) =
                sgn_eps_double_eq_target(d, p, e, n0, sgn_eps, sgn_eps_rat);
            let target_e = embed(d, p, target_e_rat);
            let abs_f_l = cabs(d, p, f_l);
            let goal_e = cle(d, p, abs_f_l, target_e);

            let h_big_n = d.lemma(
                p.converges_comp_eventually,
                &[f, a, b, huc, seq_lam, big_l, hlow, hhigh, hl, n0],
            );

            // `λ N, ∀ n, Nat.le N n → close_within (F (seq_lam n)) (F L)
            //   (natDivSucc 1 n0)` -- `convergence.rs`'s own `comp_predicate`.
            let comp_pred = {
                let bign_fv = d.fresh_fvar();
                let bign = d.kernel().fvar(bign_fv);
                let body = {
                    let n_fv = d.fresh_fvar();
                    let n = d.kernel().fvar(n_fv);
                    let hn_ty = d.le(bign, n);
                    let x_n = d.apply(seq_lam, &[n]);
                    let f_x_n = d.apply(f, &[x_n]);
                    let concl = close_within(d, p, f_x_n, f_l, sgn_eps_rat);
                    let inner = d.arrow(hn_ty, concl);
                    d.pi_fv(n_fv, nat, inner)
                };
                d.lam_fv(bign_fv, nat, body)
            };

            let inner_minor = {
                let bign_fv = d.fresh_fvar();
                let bign = d.kernel().fvar(bign_fv);
                let spec_ty = {
                    let n_fv = d.fresh_fvar();
                    let n = d.kernel().fvar(n_fv);
                    let hn_ty = d.le(bign, n);
                    let x_n = d.apply(seq_lam, &[n]);
                    let f_x_n = d.apply(f, &[x_n]);
                    let concl = close_within(d, p, f_x_n, f_l, sgn_eps_rat);
                    let inner = d.arrow(hn_ty, concl);
                    d.pi_fv(n_fv, nat, inner)
                };
                let spec_fv = d.fresh_fvar();
                let spec = d.kernel().fvar(spec_fv);

                // `n := N + (2e+1)`, so BOTH `N <= n` and `n0 <= n` hold and
                // `1/(n+1) <= 1/(n0+1)`.
                let n_idx = d.add(bign, n0);
                let hle_n = d.lemma(p.rat.int.nat.le_add_right, &[bign, n0]);
                let hle_n0 = {
                    let swapped = d.add(n0, bign);
                    let raw = d.lemma(p.rat.int.nat.le_add_right, &[n0, bign]);
                    let comm = d.lemma(p.rat.int.nat.add_comm, &[n0, bign]);
                    nat_rewrite_prop(d, swapped, n_idx, comm, raw, &|d, t| d.le(n0, t))
                };

                let x_n = d.apply(seq_lam, &[n_idx]);
                let f_x_n = d.apply(f, &[x_n]);
                let cw = d.apply(spec, &[n_idx, hle_n]);
                // cw : le (abs (add (F Xn) (neg (F L)))) sgn_eps

                // Reversed: `|F L - F Xn| <= sgn_eps`.
                let gap = abs_diff_symm(d, p, f_x_n, f_l, sgn_eps, cw);

                // `|F Xn| <= 1/(n+1) <= 1/(n0+1) = sgn_eps`.
                let habs_n = d.apply(habs, &[n_idx]);
                let small_n = {
                    let rat_n = div_succ(d, p, 1, n_idx);
                    let creal_n = embed(d, p, rat_n);
                    let antitone = d.lemma(p.rat.nat_div_succ_antitone, &[n0, n_idx, hle_n0]);
                    let lifted = d.lemma(p.of_rat_le, &[rat_n, sgn_eps_rat, antitone]);
                    let abs_f_x_n = cabs(d, p, f_x_n);
                    d.lemma(p.le_trans, &[abs_f_x_n, creal_n, sgn_eps, habs_n, lifted])
                };

                // `|F L| <= |F L - F Xn| + |F Xn| <= sgn_eps + sgn_eps
                //        ~ 1/(e+1)`.
                let neg_f_x_n = cneg(d, p, f_x_n);
                let gap_term = cadd(d, p, f_l, neg_f_x_n);
                let abs_gap = cabs(d, p, gap_term);
                let abs_f_x_n = cabs(d, p, f_x_n);
                let sum_abs = cadd(d, p, abs_gap, abs_f_x_n);
                let rebuilt = cadd(d, p, gap_term, f_x_n);
                let abs_rebuilt = cabs(d, p, rebuilt);

                let triangle = d.lemma(p.abs_add_le, &[gap_term, f_x_n]);
                // triangle : le abs_rebuilt sum_abs
                let cancel = add_sub_cancel(d, p, f_l, f_x_n);
                // cancel : Equiv rebuilt f_l
                let abs_cancel = d.lemma(p.abs_congr, &[rebuilt, f_l, cancel]);
                let refl_sum = erefl(d, p, sum_abs);
                let step_a = d.lemma(
                    p.le_congr,
                    &[
                        abs_rebuilt,
                        abs_f_l,
                        sum_abs,
                        sum_abs,
                        abs_cancel,
                        refl_sum,
                        triangle,
                    ],
                );
                let eps_eps = cadd(d, p, sgn_eps, sgn_eps);
                let step_b = d.lemma(
                    p.add_le_add,
                    &[abs_gap, sgn_eps, abs_f_x_n, sgn_eps, gap, small_n],
                );
                let chained = d.lemma(p.le_trans, &[abs_f_l, sum_abs, eps_eps, step_a, step_b]);
                let refl_abs = erefl(d, p, abs_f_l);
                let final_bound = d.lemma(
                    p.le_congr,
                    &[
                        abs_f_l,
                        abs_f_l,
                        eps_eps,
                        target_e,
                        refl_abs,
                        double_eq_target,
                        chained,
                    ],
                );
                let over_spec = d.lam_fv(spec_fv, spec_ty, final_bound);
                d.lam_fv(bign_fv, nat, over_spec)
            };

            let body = cexists_elim(d, p, nat, comp_pred, goal_e, h_big_n, inner_minor);
            d.lam_fv(e_fv, nat, body)
        };

        let hzero = d.lemma(p.equiv_zero_of_small, &[f_l, per_e]);

        let le2 = cle(d, p, big_l, b);
        let eq0 = equiv(d, p, f_l, zero_c);
        let inner_ty = d.and(le2, eq0);
        let inner = and_intro(d, p, le2, eq0, hl_b, hzero);
        let le1 = cle(d, p, a, big_l);
        let conj = and_intro(d, p, le1, inner_ty, ha_l, inner);
        let witness = cexists_intro(d, p, carrier, root_pred, big_l, conj);

        let over_hl = d.lam_fv(hl_fv, hl_ty, witness);
        d.lam_fv(l_fv, carrier, over_hl)
    };

    let proof = cexists_elim(d, p, carrier, conv_pred, target_ty, hex, minor);

    let value = {
        let over_hderiv = d.lam_fv(hderiv_fv, hderiv_ty, proof);
        let over_k = d.lam_fv(k_fv, nat, over_hderiv);
        let over_hfb = d.lam_fv(hfb_fv, hfb_ty, over_k);
        let over_hfa = d.lam_fv(hfa_fv, hfa_ty, over_hfb);
        let over_hab = d.lam_fv(hab_fv, hab_ty, over_hfa);
        let over_huc = d.lam_fv(huc_fv, uc_ty_ab, over_hab);
        let over_hf = d.lam_fv(hf_fv, hf_ty, over_huc);
        let over_b = d.lam_fv(b_fv, carrier, over_hf);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        let over_fp = d.lam_fv(fp_fv, func_ty, over_a);
        d.lam_fv(f_fv, func_ty, over_fp)
    };
    let ty = {
        let after_hderiv = d.arrow(hderiv_ty, target_ty);
        let over_k = d.pi_fv(k_fv, nat, after_hderiv);
        let after_hfb = d.arrow(hfb_ty, over_k);
        let after_hfa = d.arrow(hfa_ty, after_hfb);
        let after_hab = d.arrow(hab_ty, after_hfa);
        // `arrow` is enough here, unlike the declarations above: the target
        // never names the bisection point, so `huc` does not occur in it.
        let after_huc = d.arrow(uc_ty_ab, after_hab);
        let after_hf = d.arrow(hf_ty, after_huc);
        let over_b = d.pi_fv(b_fv, carrier, after_hf);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        let over_fp = d.pi_fv(fp_fv, func_ty, over_a);
        d.pi_fv(f_fv, func_ty, over_fp)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_exact_root,
        uparams: vec![],
        ty,
        value,
    })
}
