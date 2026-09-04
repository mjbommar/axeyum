//! **The omniscience principles, as hypotheses** (roadmap W1-9, reviewer
//! 10.1) — LPO, WLPO, Markov's principle and LLPO over `Nat`, each spelled
//! out inline in the statement of every theorem that mentions it, so the
//! reverse-mathematics map grows from one calibration point
//! (`least_number.rs`'s EM ↔ unrestricted LNP) to seven, with **every
//! declaration's `Kernel::axiom_footprint` still empty**.
//!
//! ## Why this file exists
//!
//! `least_number.rs` establishes exactly one point of the map: the
//! *unrestricted* least-number principle over `Nat` is interderivable with
//! full excluded middle, while its decidable restriction is an ordinary
//! theorem. That is one calibration and it says nothing about the principles
//! *between* constructive arithmetic and excluded middle — the ones Bishop's
//! school actually argues about, and the ones the analysis shelf keeps
//! landing on: `creal/ivt_boundary.rs` and `creal/extreme_value.rs` both
//! reduce a classical conclusion to *analytic LLPO*, and until this file the
//! library had no statement of LLPO to point at.
//!
//! ## The four principles
//!
//! Everything is stated over a **`Bool`-valued** sequence `f : Nat → Bool`,
//! which is Bishop's formulation and the honest one here: a `Prop`-valued
//! predicate would let the decidability question leak into the predicate
//! itself, and `least_number.rs` already covers that case (dropping the
//! pointwise-decision hypothesis on a `Prop`-valued predicate *is* excluded
//! middle). Write
//!
//! ```text
//! Hits f    :=  ∃ n, Eq Bool (f n) Bool.true      -- "f fires somewhere"
//! Misses f  :=  ∀ n, Eq Bool (f n) Bool.false     -- "f never fires"
//! ```
//!
//! | principle | statement |
//! |---|---|
//! | **LPO** (limited principle of omniscience) | `∀ f, Or (Hits f) (Misses f)` |
//! | **WLPO** (weak LPO) | `∀ f, Or (Misses f) (Not (Misses f))` |
//! | **MP** (Markov's principle) | `∀ f, Not (Misses f) → Hits f` |
//! | **LLPO** (lesser LPO) | `∀ f g, Not (And (Hits f) (Hits g)) → Or (Misses f) (Misses g)` |
//! | **EM** | `∀ (P : Prop), Or P (Not P)` |
//!
//! Each is written out **inline** in every type below, never behind a
//! `Definition`. That is deliberate and follows `least_number.rs`: a reader
//! of a rendered type must see the whole hypothesis, so that nothing about
//! the conclusion can be smuggled into an abbreviation. It also means this
//! file adds **no new `Definition` to the kernel** — six theorems, nothing
//! else.
//!
//! ## The seven implications
//!
//! Proved here, all constructively, all with an empty axiom footprint:
//!
//! ```text
//!   unrestricted LNP  ──(least_number.rs)──>  EM  ──>  LPO  ──>  WLPO
//!                                                       │         │
//!                                                       ├──> MP ──┤
//!                                                       │         │ (WLPO ∧ MP → LPO)
//!                                                       └──> LLPO
//! ```
//!
//! - [`Nat.em_implies_lpo`](OmniscienceNames::em_implies_lpo)
//! - [`Nat.lpo_implies_wlpo`](OmniscienceNames::lpo_implies_wlpo)
//! - [`Nat.lpo_implies_markov`](OmniscienceNames::lpo_implies_markov)
//! - [`Nat.lpo_implies_llpo`](OmniscienceNames::lpo_implies_llpo)
//! - [`Nat.wlpo_and_markov_imply_lpo`](OmniscienceNames::wlpo_and_markov_imply_lpo)
//!   — the **converse half**, and the reason this is a map and not a chain:
//!   LPO factors exactly as WLPO plus Markov.
//! - [`Nat.lnp_unrestricted_implies_lpo`](OmniscienceNames::lnp_unrestricted_implies_lpo)
//!   — joins the new picture to the existing calibration point.
//!
//! ## What is NOT proved here, and is only cited
//!
//! The **non-implications** are the other half of the standard picture and
//! none of them is proved in this kernel:
//!
//! - LPO is not derivable constructively (Bishop, *Constructive Analysis*
//!   ch. 1). This kernel cannot state that as a theorem about itself; the
//!   nearest thing it *does* have is `ipc_excluded_middle_not_provable`, an
//!   unprovability result for an **encoded** propositional logic, and
//!   ADR-1600 explains why an internal metatheorem about this kernel is
//!   unavailable by Gödel.
//! - LLPO does not imply LPO, and WLPO does not imply LPO (Markov's
//!   principle is exactly the missing half — which is the content of
//!   [`wlpo_and_markov_imply_lpo`](OmniscienceNames::wlpo_and_markov_imply_lpo),
//!   the one direction that *is* provable).
//! - MP does not imply WLPO.
//!
//! Each of those is a **separation**, and a separation needs a model of the
//! kernel, not a term in it. They are cited, not claimed.
//!
//! ## Non-vacuity
//!
//! An implication between two hypotheses could be discharged by an ex-falso
//! route that never uses the hypothesis at all, which would make the map
//! decoration. Two things rule that out:
//!
//! 1. **The bounded forms are theorems, not hypotheses.**
//!    [`Nat.lnp_bounded_search`](super::NatPrelude::lnp_bounded_search) and
//!    [`Nat.lnp_decidable`](super::NatPrelude::lnp_decidable) already prove,
//!    axiom-free, that a *bounded* search over a `Bool`-valued predicate
//!    finds its least witness. So the search machinery is present and works;
//!    what LPO adds is exactly the unbounded decision.
//! 2. **Negative controls, mutation-verified.** Each theorem in this file has
//!    a control in `omniscience_tests.rs` that perturbs one small subterm and
//!    requires `add_declaration` to reject.
//!
//! ## Everything here is constructive
//!
//! The only eliminations used are `Or.elim` (two constructors), `Bool.rec`
//! (two constructors), `Exists.rec` and `False.rec`. No numeral larger than
//! `0` is ever formed, so nothing here goes near the unary-numeral cost
//! documented in `CLAUDE.md`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;

/// The six theorem names this module admits under `Nat.`.
///
/// Held as its own struct, the way `creal/lub_boundary.rs` holds
/// [`crate::LubBoundaryNames`], so that adding the reverse-mathematics map
/// costs [`NatPrelude`] exactly one field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OmniscienceNames {
    /// `Nat.em_implies_lpo : (∀ (P : Prop), Or P (Not P)) →
    /// ∀ (f : Nat → Bool), Or (∃ n, Eq Bool (f n) Bool.true)
    /// (∀ n, Eq Bool (f n) Bool.false)`.
    ///
    /// **EM → LPO.** Excluded middle at the single proposition
    /// `∃ n, f n = true`; the negative branch turns `¬∃ n, f n = true` into
    /// `∀ n, f n = false` by a `Bool.rec` case split on `f n`, which is a
    /// genuine elimination and not a second appeal to omniscience.
    pub em_implies_lpo: NameId,
    /// `Nat.lpo_implies_wlpo : (∀ f, Or (∃ n, Eq Bool (f n) Bool.true)
    /// (∀ n, Eq Bool (f n) Bool.false)) → ∀ f,
    /// Or (∀ n, Eq Bool (f n) Bool.false) (Not (∀ n, Eq Bool (f n) Bool.false))`.
    ///
    /// **LPO → WLPO.** The `Hits` branch refutes `Misses` pointwise at the
    /// witness, through `Bool.false_ne_true`.
    pub lpo_implies_wlpo: NameId,
    /// `Nat.lpo_implies_markov : (∀ f, Or (Hits f) (Misses f)) →
    /// ∀ f, Not (∀ n, Eq Bool (f n) Bool.false) → ∃ n, Eq Bool (f n) Bool.true`.
    ///
    /// **LPO → MP.** One `Or.elim`: the `Misses` branch contradicts the
    /// hypothesis outright.
    pub lpo_implies_markov: NameId,
    /// `Nat.lpo_implies_llpo : (∀ f, Or (Hits f) (Misses f)) →
    /// ∀ f g, Not (And (Hits f) (Hits g)) → Or (Misses f) (Misses g)`.
    ///
    /// **LPO → LLPO.** Two `Or.elim`s; the branch where both sequences fire
    /// builds the forbidden `And` and lands in `False.rec`.
    pub lpo_implies_llpo: NameId,
    /// `Nat.wlpo_and_markov_imply_lpo :
    /// (∀ f, Or (Misses f) (Not (Misses f))) →
    /// (∀ f, Not (Misses f) → Hits f) → ∀ f, Or (Hits f) (Misses f)`.
    ///
    /// **WLPO ∧ MP → LPO** — the converse half of the map, and the reason
    /// this is a picture rather than a chain: LPO factors *exactly* into a
    /// decision (WLPO) plus a witness-extraction (Markov).
    pub wlpo_and_markov_imply_lpo: NameId,
    /// `Nat.lnp_unrestricted_implies_lpo :
    /// (∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k)))
    /// → ∀ f, Or (Hits f) (Misses f)`.
    ///
    /// Joins the new map to `least_number.rs`'s existing calibration point:
    /// the unrestricted least-number principle is at least as strong as LPO,
    /// via [`Nat.lnp_unrestricted_implies_em`](super::NatPrelude::lnp_unrestricted_implies_em)
    /// and then [`em_implies_lpo`](Self::em_implies_lpo).
    pub lnp_unrestricted_implies_lpo: NameId,
}

impl OmniscienceNames {
    /// Intern the six names under the `Nat` namespace root.
    pub(super) fn intern(kernel: &mut Kernel, nat: NameId) -> Self {
        Self {
            em_implies_lpo: kernel.name_str(nat, "em_implies_lpo"),
            lpo_implies_wlpo: kernel.name_str(nat, "lpo_implies_wlpo"),
            lpo_implies_markov: kernel.name_str(nat, "lpo_implies_markov"),
            lpo_implies_llpo: kernel.name_str(nat, "lpo_implies_llpo"),
            wlpo_and_markov_imply_lpo: kernel.name_str(nat, "wlpo_and_markov_imply_lpo"),
            lnp_unrestricted_implies_lpo: kernel.name_str(nat, "lnp_unrestricted_implies_lpo"),
        }
    }
}

// --- small local builders ---------------------------------------------------

/// `False.rec (fun _ => target) false_proof : target` — the same six-line
/// private helper `least_number.rs`, `add_pos.rs` and `order_more.rs` each
/// carry.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Not a`.
fn not_(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.logic.not, &[a])
}

/// `Nat → Bool`, the type of every sequence quantified over here.
fn seq_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    d.arrow(nat, bool_ty)
}

/// `fun n => Eq Bool (f n) Bool.true` — the `Exists` predicate of `Hits`.
fn hits_pred(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_ = d.apply(f, &[n]);
    let true_v = d.bool_true();
    let body = d.bool_eq(fn_, true_v);
    d.lam_fv(n_fv, nat, body)
}

/// `Hits f := ∃ n, Eq Bool (f n) Bool.true` — "`f` fires somewhere".
fn hits(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = hits_pred(d, f);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.intro n h : Hits f`, from `h : Eq Bool (f n) Bool.true`.
fn hits_intro(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = hits_pred(d, f);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, n, h])
}

/// `Misses f := ∀ n, Eq Bool (f n) Bool.false` — "`f` never fires".
fn misses(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_ = d.apply(f, &[n]);
    let false_v = d.bool_false();
    let body = d.bool_eq(fn_, false_v);
    d.pi_fv(n_fv, nat, body)
}

/// `LPO := ∀ (f : Nat → Bool), Or (Hits f) (Misses f)`.
fn lpo(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let sty = seq_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, p, f);
    let m = misses(d, f);
    let body = d.const_app(p.logic.or, &[h, m]);
    d.pi_fv(f_fv, sty, body)
}

/// `WLPO := ∀ (f : Nat → Bool), Or (Misses f) (Not (Misses f))`.
fn wlpo(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let sty = seq_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m = misses(d, f);
    let nm = not_(d, p, m);
    let body = d.const_app(p.logic.or, &[m, nm]);
    d.pi_fv(f_fv, sty, body)
}

/// `MP := ∀ (f : Nat → Bool), Not (Misses f) → Hits f` — Markov's principle.
fn markov(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let sty = seq_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m = misses(d, f);
    let nm = not_(d, p, m);
    let h = hits(d, p, f);
    let body = d.arrow(nm, h);
    d.pi_fv(f_fv, sty, body)
}

/// `LLPO := ∀ (f g : Nat → Bool), Not (And (Hits f) (Hits g)) →
/// Or (Misses f) (Misses g)`.
fn llpo(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let sty = seq_ty(d);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let hf = hits(d, p, f);
    let hg = hits(d, p, g);
    let both = d.const_app(p.logic.and, &[hf, hg]);
    let nboth = not_(d, p, both);
    let mf = misses(d, f);
    let mg = misses(d, g);
    let concl = d.const_app(p.logic.or, &[mf, mg]);
    let inner = d.arrow(nboth, concl);
    let with_g = d.pi_fv(g_fv, sty, inner);
    d.pi_fv(f_fv, sty, with_g)
}

/// `∀ (P : Prop), Or P (Not P)` — excluded middle in the ambient logic,
/// built exactly as `least_number.rs` builds it so the two agree.
fn excluded_middle(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let prop = d.kernel().sort_zero();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let nx = not_(d, p, x);
    let body = d.const_app(p.logic.or, &[x, nx]);
    d.pi_fv(x_fv, prop, body)
}

// --- the unrestricted least-number principle, rebuilt --------------------
//
// `least_number.rs` keeps these four builders private. They are duplicated
// here rather than exported so that this file adds nothing to that one; the
// terms must agree up to definitional equality, which they do because they
// are built the same way, and
// `lnp_unrestricted_implies_lpo_applies_the_existing_lnp_theorem`
// (`omniscience_tests.rs`) is the check that they do.

/// `Nat → Prop`.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    d.arrow(nat, prop)
}

/// `∀ k, Lt k n → Not (Q k)`.
fn none_below(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let lt = d.lt(k, n);
    let qk = d.apply(q, &[k]);
    let nqk = not_(d, p, qk);
    let imp = d.arrow(lt, nqk);
    d.pi_fv(k_fv, nat, imp)
}

/// `∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`.
fn least_exists(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let qm = d.apply(q, &[m]);
        let nb = none_below(d, p, q, m);
        let body = d.const_app(p.logic.and, &[qm, nb]);
        d.lam_fv(m_fv, nat, body)
    };
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `∃ n, Q n`.
fn inhabited(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.apply(q, &[n]);
        d.lam_fv(n_fv, nat, body)
    };
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`
/// — the unrestricted least-number principle, spelled out inline.
fn unrestricted_lnp(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let pty = pred_ty(d);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hyp = inhabited(d, p, q);
    let concl = least_exists(d, p, q);
    let body = d.arrow(hyp, concl);
    d.pi_fv(q_fv, pty, body)
}

// --- the two `Bool` bridges -------------------------------------------------

/// From `no_hit : Not (Hits f)` and an index `n`, derive
/// `Eq Bool (f n) Bool.false`.
///
/// A `Bool.rec` case split on `f n` **remembering its identity**: the motive
/// is `fun c => Eq Bool (f n) c → Eq Bool (f n) Bool.false`, so the `false`
/// branch returns its own hypothesis and the `true` branch feeds
/// `Exists.intro n h` to `no_hit`. Two constructors, a genuine elimination —
/// this is not a second appeal to omniscience.
fn miss_at(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId, no_hit: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let fn_ = d.apply(f, &[n]);
    let false_v = d.bool_false();
    let true_v = d.bool_true();
    let target = d.bool_eq(fn_, false_v);

    let motive = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hyp = d.bool_eq(fn_, c);
        let body = d.arrow(hyp, target);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let at_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.bool_eq(fn_, false_v);
        d.lam_fv(h_fv, hyp, h)
    };
    let at_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.bool_eq(fn_, true_v);
        let witness = hits_intro(d, p, f, n, h);
        let bad = d.apply(no_hit, &[witness]);
        let body = ex_falso(d, p, target, bad);
        d.lam_fv(h_fv, hyp, body)
    };
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let applied = d.apply(rec, &[motive, at_false, at_true, fn_]);
    let refl = d.bool_refl(fn_);
    d.apply(applied, &[refl])
}

/// `fun (n : Nat) => miss_at …` — `Misses f`, from `Not (Hits f)`.
fn misses_of_no_hit(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, no_hit: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = miss_at(d, p, f, n, no_hit);
    d.lam_fv(n_fv, nat, body)
}

/// `False`, from `h_hits : Hits f` and `h_misses : Misses f`.
///
/// `Exists.rec` on the witness, then `Bool.false_ne_true` against
/// `Eq.trans (Eq.symm (h_misses n)) h`.
fn refute_hits_and_misses(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    h_hits: ExprId,
    h_misses: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let pred = hits_pred(d, f);

    let motive = {
        let dummy = d.fresh_fvar();
        let ex_ty = hits(d, p, f);
        d.lam_fv(dummy, ex_ty, false_ty)
    };
    let minor = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let true_v = d.bool_true();
        let false_v = d.bool_false();
        let hyp = d.bool_eq(fn_, true_v);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let at_n = d.apply(h_misses, &[n]);
        let flipped = d.bool_symm(fn_, false_v, at_n);
        let chain = d.bool_trans(false_v, fn_, true_v, flipped, h);
        let clash = d.kernel().const_(p.logic.bool_false_ne_true, vec![]);
        let bad = d.apply(clash, &[chain]);
        let with_h = d.lam_fv(h_fv, hyp, bad);
        d.lam_fv(n_fv, nat, with_h)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, h_hits])
}

// --- `Nat.em_implies_lpo` ---------------------------------------------------

/// `Nat.em_implies_lpo : (∀ (P : Prop), Or P (Not P)) → ∀ (f : Nat → Bool),
/// Or (∃ n, Eq Bool (f n) Bool.true) (∀ n, Eq Bool (f n) Bool.false)`
///
/// **EM → LPO**, the top edge of the map. Excluded middle is used exactly
/// once, at the single proposition `Hits f`; turning the negative branch into
/// `Misses f` is [`miss_at`]'s `Bool.rec`, not a second appeal.
fn declare_em_implies_lpo(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let em_ty = excluded_middle(d, &p);
    let em_fv = d.fresh_fvar();
    let em = d.kernel().fvar(em_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, &p, f);
    let m = misses(d, f);
    let target = d.const_app(p.logic.or, &[h, m]);

    let nh = not_(d, &p, h);
    let decision = d.apply(em, &[h]);

    let at_hit = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.const_app(p.logic.or_inl, &[h, m, x]);
        d.lam_fv(x_fv, h, body)
    };
    let at_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let all = misses_of_no_hit(d, &p, f, x);
        let body = d.const_app(p.logic.or_inr, &[h, m, all]);
        d.lam_fv(x_fv, nh, body)
    };
    let body = d.const_app(p.logic.or_elim, &[h, nh, target, decision, at_hit, at_miss]);

    let ty = {
        let with_f = d.pi_fv(f_fv, sty, target);
        d.arrow(em_ty, with_f)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, sty, body);
        d.lam_fv(em_fv, em_ty, with_f)
    };
    d.declare_theorem(p.omniscience.em_implies_lpo, ty, value)
}

// --- `Nat.lpo_implies_wlpo` -------------------------------------------------

/// `Nat.lpo_implies_wlpo : (∀ f, Or (Hits f) (Misses f)) →
/// ∀ f, Or (Misses f) (Not (Misses f))`
///
/// **LPO → WLPO.** The `Hits` branch refutes `Misses` at the witness through
/// [`refute_hits_and_misses`]; the `Misses` branch is `Or.inl` of its own
/// hypothesis.
fn declare_lpo_implies_wlpo(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let lpo_ty = lpo(d, &p);
    let lpo_fv = d.fresh_fvar();
    let hlpo = d.kernel().fvar(lpo_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, &p, f);
    let m = misses(d, f);
    let nm = not_(d, &p, m);
    let target = d.const_app(p.logic.or, &[m, nm]);

    let decision = d.apply(hlpo, &[f]);

    let at_hit = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let refutation = {
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let bad = refute_hits_and_misses(d, &p, f, x, hm);
            d.lam_fv(hm_fv, m, bad)
        };
        let body = d.const_app(p.logic.or_inr, &[m, nm, refutation]);
        d.lam_fv(x_fv, h, body)
    };
    let at_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.const_app(p.logic.or_inl, &[m, nm, x]);
        d.lam_fv(x_fv, m, body)
    };
    let body = d.const_app(p.logic.or_elim, &[h, m, target, decision, at_hit, at_miss]);

    let ty = {
        let with_f = d.pi_fv(f_fv, sty, target);
        d.arrow(lpo_ty, with_f)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, sty, body);
        d.lam_fv(lpo_fv, lpo_ty, with_f)
    };
    d.declare_theorem(p.omniscience.lpo_implies_wlpo, ty, value)
}

// --- `Nat.lpo_implies_markov` -----------------------------------------------

/// `Nat.lpo_implies_markov : (∀ f, Or (Hits f) (Misses f)) →
/// ∀ f, Not (Misses f) → Hits f`
///
/// **LPO → MP.** One `Or.elim`: the `Hits` branch *is* the conclusion, and
/// the `Misses` branch contradicts the standing hypothesis.
fn declare_lpo_implies_markov(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let lpo_ty = lpo(d, &p);
    let lpo_fv = d.fresh_fvar();
    let hlpo = d.kernel().fvar(lpo_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, &p, f);
    let m = misses(d, f);
    let nm = not_(d, &p, m);

    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let decision = d.apply(hlpo, &[f]);
    let at_hit = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        d.lam_fv(x_fv, h, x)
    };
    let at_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let bad = d.apply(hn, &[x]);
        let body = ex_falso(d, &p, h, bad);
        d.lam_fv(x_fv, m, body)
    };
    let body = d.const_app(p.logic.or_elim, &[h, m, h, decision, at_hit, at_miss]);

    let ty = {
        let inner = d.arrow(nm, h);
        let with_f = d.pi_fv(f_fv, sty, inner);
        d.arrow(lpo_ty, with_f)
    };
    let value = {
        let inner = d.lam_fv(hn_fv, nm, body);
        let with_f = d.lam_fv(f_fv, sty, inner);
        d.lam_fv(lpo_fv, lpo_ty, with_f)
    };
    d.declare_theorem(p.omniscience.lpo_implies_markov, ty, value)
}

// --- `Nat.lpo_implies_llpo` -------------------------------------------------

/// `Nat.lpo_implies_llpo : (∀ f, Or (Hits f) (Misses f)) →
/// ∀ f g, Not (And (Hits f) (Hits g)) → Or (Misses f) (Misses g)`
///
/// **LPO → LLPO.** Two nested `Or.elim`s. Only the branch where *both*
/// sequences fire is impossible, and it is refuted by building the forbidden
/// `And` — which is exactly why LLPO is weaker: it never has to say which of
/// the two misses.
fn declare_lpo_implies_llpo(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let lpo_ty = lpo(d, &p);
    let lpo_fv = d.fresh_fvar();
    let hlpo = d.kernel().fvar(lpo_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let hf = hits(d, &p, f);
    let hg = hits(d, &p, g);
    let mf = misses(d, f);
    let mg = misses(d, g);
    let both = d.const_app(p.logic.and, &[hf, hg]);
    let nboth = not_(d, &p, both);
    let target = d.const_app(p.logic.or, &[mf, mg]);

    let hno_fv = d.fresh_fvar();
    let hno = d.kernel().fvar(hno_fv);

    let outer = d.apply(hlpo, &[f]);
    let at_f_hit = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner_decision = d.apply(hlpo, &[g]);
        let at_g_hit = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let pair = d.const_app(p.logic.and_intro, &[hf, hg, x, y]);
            let bad = d.apply(hno, &[pair]);
            let body = ex_falso(d, &p, target, bad);
            d.lam_fv(y_fv, hg, body)
        };
        let at_g_miss = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.const_app(p.logic.or_inr, &[mf, mg, y]);
            d.lam_fv(y_fv, mg, body)
        };
        let body = d.const_app(
            p.logic.or_elim,
            &[hg, mg, target, inner_decision, at_g_hit, at_g_miss],
        );
        d.lam_fv(x_fv, hf, body)
    };
    let at_f_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.const_app(p.logic.or_inl, &[mf, mg, x]);
        d.lam_fv(x_fv, mf, body)
    };
    let body = d.const_app(
        p.logic.or_elim,
        &[hf, mf, target, outer, at_f_hit, at_f_miss],
    );

    // Built from the SHARED [`llpo`] builder rather than re-spelled here, so
    // the admitted conclusion is the same term the module doc calls LLPO.
    // `pi_fv` abstracts free variables into de Bruijn indices, so the
    // independently-built type and value are alpha-equal and the kernel
    // accepts the pairing — which is itself the check that they agree.
    let ty = {
        let concl = llpo(d, &p);
        d.arrow(lpo_ty, concl)
    };
    let value = {
        let inner = d.lam_fv(hno_fv, nboth, body);
        let with_g = d.lam_fv(g_fv, sty, inner);
        let with_f = d.lam_fv(f_fv, sty, with_g);
        d.lam_fv(lpo_fv, lpo_ty, with_f)
    };
    d.declare_theorem(p.omniscience.lpo_implies_llpo, ty, value)
}

// --- `Nat.wlpo_and_markov_imply_lpo` ----------------------------------------

/// `Nat.wlpo_and_markov_imply_lpo :
/// (∀ f, Or (Misses f) (Not (Misses f))) →
/// (∀ f, Not (Misses f) → Hits f) → ∀ f, Or (Hits f) (Misses f)`
///
/// **WLPO ∧ MP → LPO** — the converse half, and the edge that turns the
/// chain into a map: LPO is *exactly* WLPO's decision plus Markov's
/// witness-extraction, so a model separating LPO from WLPO must also
/// separate Markov's principle.
fn declare_wlpo_and_markov_imply_lpo(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let wlpo_ty = wlpo(d, &p);
    let wlpo_fv = d.fresh_fvar();
    let hwlpo = d.kernel().fvar(wlpo_fv);
    let mp_ty = markov(d, &p);
    let mp_fv = d.fresh_fvar();
    let hmp = d.kernel().fvar(mp_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, &p, f);
    let m = misses(d, f);
    let nm = not_(d, &p, m);
    let target = d.const_app(p.logic.or, &[h, m]);

    let decision = d.apply(hwlpo, &[f]);
    let at_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = d.const_app(p.logic.or_inr, &[h, m, x]);
        d.lam_fv(x_fv, m, body)
    };
    let at_not_miss = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let witness = d.apply(hmp, &[f, x]);
        let body = d.const_app(p.logic.or_inl, &[h, m, witness]);
        d.lam_fv(x_fv, nm, body)
    };
    let body = d.const_app(
        p.logic.or_elim,
        &[m, nm, target, decision, at_miss, at_not_miss],
    );

    let ty = {
        let with_f = d.pi_fv(f_fv, sty, target);
        let inner = d.arrow(mp_ty, with_f);
        d.arrow(wlpo_ty, inner)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, sty, body);
        let inner = d.lam_fv(mp_fv, mp_ty, with_f);
        d.lam_fv(wlpo_fv, wlpo_ty, inner)
    };
    d.declare_theorem(p.omniscience.wlpo_and_markov_imply_lpo, ty, value)
}

// --- `Nat.lnp_unrestricted_implies_lpo` -------------------------------------

/// `Nat.lnp_unrestricted_implies_lpo :
/// (∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k)))
/// → ∀ f, Or (Hits f) (Misses f)`
///
/// The join between this map and `least_number.rs`'s existing calibration
/// point, composed from
/// [`Nat.lnp_unrestricted_implies_em`](super::NatPrelude::lnp_unrestricted_implies_em)
/// and [`em_implies_lpo`](OmniscienceNames::em_implies_lpo). Its *admission*
/// is the check that the unrestricted-LNP term rebuilt in this file is
/// definitionally the one `least_number.rs` declared.
fn declare_lnp_unrestricted_implies_lpo(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let sty = seq_ty(d);

    let lnp_ty = unrestricted_lnp(d, &p);
    let lnp_fv = d.fresh_fvar();
    let hlnp = d.kernel().fvar(lnp_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h = hits(d, &p, f);
    let m = misses(d, f);
    let target = d.const_app(p.logic.or, &[h, m]);

    let em = d.lemma(p.lnp_unrestricted_implies_em, &[hlnp]);
    let body = d.lemma(p.omniscience.em_implies_lpo, &[em, f]);

    let ty = {
        let with_f = d.pi_fv(f_fv, sty, target);
        d.arrow(lnp_ty, with_f)
    };
    let value = {
        let with_f = d.lam_fv(f_fv, sty, body);
        d.lam_fv(lnp_fv, lnp_ty, with_f)
    };
    d.declare_theorem(p.omniscience.lnp_unrestricted_implies_lpo, ty, value)
}

/// Declare the whole family, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_omniscience_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_em_implies_lpo(d, p)?;
    declare_lpo_implies_wlpo(d, p)?;
    declare_lpo_implies_markov(d, p)?;
    declare_lpo_implies_llpo(d, p)?;
    declare_wlpo_and_markov_imply_lpo(d, p)?;
    declare_lnp_unrestricted_implies_lpo(d, p)?;
    Ok(())
}
