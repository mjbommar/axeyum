//! **The least-number principle's boundary certificate** (ADR-0603 row 2 for
//! the naturals) — a machine-checked reduction showing that the *unrestricted*
//! least-number principle over `Nat`, with no decidability hypothesis on the
//! predicate, is **equivalent to full excluded middle**, while the same
//! principle restricted to a decidable predicate is an ordinary constructive
//! theorem proved in this very file.
//!
//! ## Why this file exists at all
//!
//! ADR-0603 makes a classical theorem land as a graded statement family, and
//! row 2 — a proof that the classical form *implies* something
//! non-constructive — is the row a classical library has no counterpart for.
//! `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
//! (ADR-0716) measured that row 2 is **empty for ℕ, ℤ and ℚ**: the decision
//! principle every analysis row 2 extracts is `le_total`, and
//! `Nat.le_total` / `Int.le_total` / `Rat.le_total` are all already proved and
//! axiom-free here, while `CReal.le_total` is absent.
//! <!-- absent: CReal.le_total -->
//! So nothing stated over
//! ℕ can reduce to *that* obstruction.
//!
//! One boundary survives, and it is **strictly stronger** than the analysis
//! rows. `creal/ivt_boundary.rs` and `creal/extreme_value.rs` each reduce a
//! classical conclusion to deciding the sign of an arbitrary real, i.e. to a
//! lesser limited principle of omniscience (LLPO) — a *weak* omniscience
//! principle that does not give excluded middle for arbitrary propositions.
//! The unrestricted least-number principle gives excluded middle **for every
//! `P : Prop`**, with no restriction to arithmetic or `Σ⁰₁` statements. This
//! file proves that, and its converse.
//!
//! ## The four declarations
//!
//! Write, for a predicate `Q : Nat → Prop`,
//!
//! ```text
//! NoneBelow Q n  :=  ∀ k, Lt k n → Not (Q k)
//! Least Q m      :=  And (Q m) (NoneBelow Q m)
//! ```
//!
//! - [`Nat.lnp_bounded_search`](super::NatPrelude::lnp_bounded_search) —
//!   `∀ Q, (∀ n, Or (Q n) (Not (Q n))) → ∀ n, Or (NoneBelow Q n) (∃ m, And (Lt m n) (Least Q m))`.
//!   The engine: ordinary induction on the bound `n`. Either nothing below
//!   `n` satisfies `Q`, or there is a **least** witness strictly below `n`.
//! - [`Nat.lnp_of_pointwise_decision`](super::NatPrelude::lnp_of_pointwise_decision) —
//!   `∀ Q, (∀ n, Or (Q n) (Not (Q n))) → (∃ n, Q n) → ∃ m, Least Q m`.
//!   The least-number principle **for a pointwise-decided predicate**, run at
//!   the bound `succ n₀` supplied by the non-emptiness witness.
//! - [`Nat.lnp_decidable`](super::NatPrelude::lnp_decidable) —
//!   `∀ dec n, Eq Bool (dec n) true → ∃ m, And (Eq Bool (dec m) true) (∀ k, Lt k m → Eq Bool (dec k) false)`.
//!   The **non-vacuity anchor** (see below).
//! - [`Nat.lnp_unrestricted_implies_em`](super::NatPrelude::lnp_unrestricted_implies_em) —
//!   `(∀ Q, (∃ n, Q n) → ∃ m, Least Q m) → ∀ (P : Prop), Or P (Not P)`.
//!   The row-2 statement itself.
//! - [`Nat.em_implies_lnp`](super::NatPrelude::em_implies_lnp) —
//!   `(∀ (P : Prop), Or P (Not P)) → ∀ Q, (∃ n, Q n) → ∃ m, Least Q m`.
//!   The converse, one line from `lnp_of_pointwise_decision`, which upgrades
//!   the row from "costs *at least* EM" to "costs **exactly** EM".
//!
//! ## Non-vacuity: what makes this a boundary and not a gap
//!
//! A row-2 claim that could be read as *"we just have not proved LNP yet"*
//! would be worthless. Two things rule that reading out, and both are
//! mechanically checkable rather than asserted:
//!
//! 1. **The decidable form is a theorem in this file.**
//!    [`Nat.lnp_decidable`](super::NatPrelude::lnp_decidable) is the same
//!    statement with `Q n` replaced by `Eq Bool (dec n) true` — a `Bool`-valued
//!    predicate — and it is admitted with an empty axiom footprint. So the
//!    machinery to *find* a least element is present and works; what is
//!    unavailable is exactly the step from a `Prop`-valued predicate to a
//!    pointwise decision, and
//!    [`Nat.lnp_of_pointwise_decision`](super::NatPrelude::lnp_of_pointwise_decision)
//!    isolates that step as its own explicit hypothesis.
//! 2. **A bounded, predicate-specific least-number search already shipped.**
//!    [`Nat.least_divisor_search`](super::NatPrelude::least_divisor_search)
//!    (`min_fac.rs`) is
//!    `∀ k m, Or (∃ x, Le 2 x ∧ dvd x m ∧ ∀ e, Le 2 e → Lt e x → Not (dvd e m)) (∀ c, Le 2 c → Le c k → Not (dvd c m))`
//!    — literally
//!    [`lnp_bounded_search`](super::NatPrelude::lnp_bounded_search)'s shape,
//!    specialised to divisibility, landed long before this file. `minFac`'s
//!    whole minimality argument runs on it.
//!
//! The gap between the two is *only* the decidability hypothesis, and
//! [`Nat.em_implies_lnp`](super::NatPrelude::em_implies_lnp) prices that gap
//! exactly: removing the hypothesis is not merely inconvenient, it is
//! interderivable with excluded middle.
//!
//! ## The argument
//!
//! Given an arbitrary `P : Prop`, form
//!
//! ```text
//! Qₚ n  :=  Or (Eq Nat n 1) (And (Eq Nat n 0) P)
//! ```
//!
//! `Qₚ` is inhabited unconditionally — `Qₚ 1` holds by `Or.inl (Eq.refl 1)`,
//! with **no** appeal to `P` — so the unrestricted LNP applies and returns a
//! least `m`. Case on `m` (`Nat.rec` exposing the shape; no induction
//! hypothesis is used):
//!
//! - `m = 0`. Then `Qₚ 0` holds. Its left disjunct `Eq Nat 0 1` is refuted by
//!   [`Nat.succ_ne_zero`](super::NatPrelude::succ_ne_zero), so the right
//!   disjunct holds and its second component **is** `P`. Answer `Or.inl`.
//! - `m = succ j`. Then `0 < m`, so minimality gives `Not (Qₚ 0)`. Any proof
//!   of `P` would build `Qₚ 0` as `Or.inr (And.intro (Eq.refl 0) hp)`, so
//!   `P → False`. Answer `Or.inr`.
//!
//! The whole content is that **the position of the least element answers a
//! question about `P`** — the same shape `creal/extreme_value.rs` uses (there:
//! *which endpoint* attains the maximum answers a question about the sign of
//! `v`), one carrier over, and with `Prop` in place of `CReal`. Only `0` and
//! `1` are ever formed, so nothing here goes near the unary-numeral cost
//! documented in `CLAUDE.md`.
//!
//! ## Why the statement is `∀ P : Prop, Or P (Not P)` and NOT routed through
//! ## `ipc_soundness.rs`
//!
//! `ipc_soundness.rs` proves `ipc_excluded_middle_not_provable`, closing
//! `F:excluded-middle-not-intuitionistic`: the *encoded* formula
//! `or_ (var 0) (imp (var 0) bot)` has no `Provable` derivation from the empty
//! context. That is a statement about a syntactic object language and its
//! 3-element Heyting-chain semantics.
//!
//! This file deliberately does **not** route through it, and the reason is not
//! convenience. Row 2 must say what a *hypothesis of the kernel's own logic*
//! buys you in the kernel's own logic. Stating LNP over `Formula` and deriving
//! the encoded EM would prove something about the encoding — and the encoded
//! LNP is not the principle any theorem in this prelude is stated with, so the
//! reduction would not touch the real thing. The conclusion here is the
//! ambient `∀ (P : Prop), Or P (Not P)`, quantified over every proposition the
//! kernel can form, including every statement in every prelude.
//!
//! The two results are complementary and the pairing is the point:
//! `ipc_soundness.rs` establishes that excluded middle is **not free** in an
//! intuitionistic setting; this file establishes that the unrestricted LNP
//! **buys it**. Neither is evidence for the other's subject, and together they
//! say the price is real and exactly what it looks like.
//!
//! ## Everything here is constructive
//!
//! No declaration in this file assumes excluded middle, and none needs it.
//! The two case splits used are `Nat.rec` (two constructors) and `Bool.rec`
//! (two constructors) — genuine eliminations, not omniscience — exactly the
//! discipline `cantor.rs` documents for its own `Bool` split. Every
//! declaration admits with an empty `axiom_footprint`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// --- small local builders ---------------------------------------------------

/// `False.rec (fun _ => target) false_proof : target`, the same six-line
/// private helper `add_pos.rs` and `order_more.rs` each carry.
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

/// `Prop`, i.e. `Sort 0`.
fn prop_sort(d: &mut NatDev<'_>) -> ExprId {
    d.kernel().sort_zero()
}

/// `Nat → Prop`, the type of the predicates every statement here quantifies
/// over. Non-dependent, so its own sort is `Sort (imax 1 1) = Sort 1` and it
/// is an ordinary `Type` — nothing universe-exotic happens in this file.
fn pred_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let prop = prop_sort(d);
    d.arrow(nat, prop)
}

/// `∀ k, Lt k n → Not (Q k)` — "nothing strictly below `n` satisfies `Q`".
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

/// `And (Q m) (NoneBelow Q m)` — "`m` is a least element of `Q`".
fn least_at(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, m: ExprId) -> ExprId {
    let qm = d.apply(q, &[m]);
    let nb = none_below(d, p, q, m);
    d.const_app(p.logic.and, &[qm, nb])
}

/// `fun m => And (Q m) (NoneBelow Q m)` — the `Exists` predicate of the
/// least-number principle's conclusion.
fn least_pred(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let body = least_at(d, p, q, m);
    d.lam_fv(m_fv, nat, body)
}

/// `∃ m, And (Q m) (NoneBelow Q m)`.
fn least_exists(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = least_pred(d, p, q);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `fun n => Q n` — the eta-expanded non-emptiness predicate, written this way
/// (rather than as `Q` itself) so the rendered statement reads `∃ n, Q n`.
fn inhabited_pred(d: &mut NatDev<'_>, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let body = d.apply(q, &[n]);
    d.lam_fv(n_fv, nat, body)
}

/// `∃ n, Q n`.
fn inhabited(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = inhabited_pred(d, q);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `fun m => And (Lt m n) (And (Q m) (NoneBelow Q m))` — the bounded search's
/// `Exists` predicate.
fn bounded_pred(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let lt = d.lt(m, n);
    let core = least_at(d, p, q, m);
    let body = d.const_app(p.logic.and, &[lt, core]);
    d.lam_fv(m_fv, nat, body)
}

/// `∃ m, And (Lt m n) (And (Q m) (NoneBelow Q m))`.
fn found_below(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let pred = bounded_pred(d, p, q, n);
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Or (NoneBelow Q n) (∃ m, And (Lt m n) (Least Q m))` — the bounded search's
/// conclusion at bound `n`.
fn search_result(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let none = none_below(d, p, q, n);
    let found = found_below(d, p, q, n);
    d.const_app(p.logic.or, &[none, found])
}

/// `∀ n, Or (Q n) (Not (Q n))` — the pointwise-decision hypothesis. This is
/// the ONLY thing separating the theorem from the excluded middle it implies.
fn pointwise_decision(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let qn = d.apply(q, &[n]);
    let nqn = not_(d, p, qn);
    let body = d.const_app(p.logic.or, &[qn, nqn]);
    d.pi_fv(n_fv, nat, body)
}

/// `∀ (P : Prop), Or P (Not P)` — excluded middle, in the ambient logic.
fn excluded_middle(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let prop = prop_sort(d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let nx = not_(d, p, x);
    let body = d.const_app(p.logic.or, &[x, nx]);
    d.pi_fv(x_fv, prop, body)
}

/// The unrestricted least-number principle, spelled out inline:
/// `∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`.
///
/// Deliberately NOT wrapped in a `Definition`: a reader of
/// [`declare_lnp_unrestricted_implies_em`]'s rendered type must see the whole
/// hypothesis, so that nothing about the conclusion can be smuggled into an
/// abbreviation.
fn unrestricted_lnp(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let pty = pred_ty(d);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hyp = inhabited(d, p, q);
    let concl = least_exists(d, p, q);
    let body = d.arrow(hyp, concl);
    d.pi_fv(q_fv, pty, body)
}

// --- `Nat.lnp_bounded_search` -----------------------------------------------

/// `Nat.lnp_bounded_search : ∀ (Q : Nat → Prop), (∀ n, Or (Q n) (Not (Q n))) →
/// ∀ n, Or (∀ k, Lt k n → Not (Q k)) (∃ m, And (Lt m n) (And (Q m) (∀ k, Lt k m → Not (Q k))))`
///
/// Ordinary induction on the bound `n`, no well-founded recursion:
///
/// - `n = 0`: the left disjunct, vacuously, via
///   [`NatPrelude::not_lt_zero`](super::NatPrelude::not_lt_zero).
/// - `n = succ j`: case on the induction hypothesis. If it already found a
///   least witness below `j`, widen its bound with
///   [`lt_of_lt_of_le`](super::NatPrelude::lt_of_lt_of_le) against
///   [`le_succ`](super::NatPrelude::le_succ). Otherwise nothing below `j`
///   satisfies `Q`, and the decision at `j` splits: `Q j` makes `j` itself the
///   least witness (its minimality clause IS the induction hypothesis), while
///   `Not (Q j)` extends the left disjunct one step, using
///   [`le_of_lt_succ`](super::NatPrelude::le_of_lt_succ) +
///   [`lt_or_eq_of_le`](super::NatPrelude::lt_or_eq_of_le) to reduce
///   `Lt k (succ j)` to `Lt k j` or `Eq k j`, the latter transporting
///   `Not (Q j)` to `Not (Q k)`.
///
/// The decision hypothesis is used in exactly ONE place — the successor step's
/// split at `j` — which is why removing it is precisely as strong as excluded
/// middle and not weaker.
pub(super) fn declare_lnp_bounded_search(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hdec_ty = pointwise_decision(d, &p, q);
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let proof_at_n = d.induct(
        &|d, x| search_result(d, &p, q, x),
        &|d| search_base(d, &p, q),
        &|d, j, ih| search_step(d, &p, q, hdec, j, ih),
        n,
    );

    let concl = search_result(d, &p, q, n);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, concl);
        let with_dec = d.arrow(hdec_ty, inner);
        d.pi_fv(q_fv, pty, with_dec)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof_at_n);
        let with_dec = d.lam_fv(hdec_fv, hdec_ty, inner);
        d.lam_fv(q_fv, pty, with_dec)
    };

    d.declare_theorem(p.lnp_bounded_search, ty, value)
}

/// The `n = 0` base case: `Or.inl` of the vacuous `∀ k, Lt k 0 → Not (Q k)`.
fn search_base(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let zero = d.zero();
    let none = none_below(d, p, q, zero);
    let found = found_below(d, p, q, zero);

    let vacuous = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let lt_ty = d.lt(k, zero);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let qk = d.apply(q, &[k]);
        let nqk = not_(d, p, qk);
        let absurd = d.lemma(p.not_lt_zero, &[k, hk]);
        let body = ex_falso(d, p, nqk, absurd);
        let with_hk = d.lam_fv(hk_fv, lt_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };

    d.const_app(p.logic.or_inl, &[none, found, vacuous])
}

/// The `n = succ j` step, given `ih : Or (NoneBelow Q j) (Found Q j)`.
fn search_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    q: ExprId,
    hdec: ExprId,
    j: ExprId,
    ih: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let succ_j = d.succ(j);

    let none_j = none_below(d, p, q, j);
    let found_j = found_below(d, p, q, j);
    let none_s = none_below(d, p, q, succ_j);
    let found_s = found_below(d, p, q, succ_j);
    let target = search_result(d, p, q, succ_j);

    // --- ih = Or.inl hnone: nothing below `j` satisfies `Q`. Split at `j`.
    let minor_none = {
        let hnone_fv = d.fresh_fvar();
        let hnone = d.kernel().fvar(hnone_fv);
        let qj = d.apply(q, &[j]);
        let nqj = not_(d, p, qj);
        let dec_j = d.apply(hdec, &[j]);

        // `Q j` holds: `j` is the least witness below `succ j`.
        let at_qj = {
            let hq_fv = d.fresh_fvar();
            let hq = d.kernel().fvar(hq_fv);
            let core_ty = least_at(d, p, q, j);
            let core = d.const_app(p.logic.and_intro, &[qj, none_j, hq, hnone]);
            let lt_ty = d.lt(j, succ_j);
            let lt_proof = d.lemma(p.lt_succ_self, &[j]);
            let pair = d.const_app(p.logic.and_intro, &[lt_ty, core_ty, lt_proof, core]);
            let bp = bounded_pred(d, p, q, succ_j);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let witness = d.apply(intro, &[nat, bp, j, pair]);
            let res = d.const_app(p.logic.or_inr, &[none_s, found_s, witness]);
            d.lam_fv(hq_fv, qj, res)
        };

        // `Not (Q j)`: the left disjunct extends one step.
        let at_nqj = {
            let hnq_fv = d.fresh_fvar();
            let hnq = d.kernel().fvar(hnq_fv);
            let extended = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let lt_ks_ty = d.lt(k, succ_j);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let qk = d.apply(q, &[k]);
                let nqk = not_(d, p, qk);
                let hle = d.lemma(p.le_of_lt_succ, &[k, j, hk]);
                let hsplit = d.lemma(p.lt_or_eq_of_le, &[k, j, hle]);
                let lt_kj = d.lt(k, j);
                let eq_kj = d.eq(k, j);
                let at_lt = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let res = d.apply(hnone, &[k, h]);
                    d.lam_fv(h_fv, lt_kj, res)
                };
                let at_eq = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_jk = d.symm(k, j, h);
                    let motive = d.eq_motive(j, &|d, x| {
                        let qx = d.apply(q, &[x]);
                        not_(d, p, qx)
                    });
                    let res = d.transport(j, motive, hnq, k, h_jk);
                    d.lam_fv(h_fv, eq_kj, res)
                };
                let sel = d.const_app(p.logic.or_elim, &[lt_kj, eq_kj, nqk, hsplit, at_lt, at_eq]);
                let with_hk = d.lam_fv(hk_fv, lt_ks_ty, sel);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let res = d.const_app(p.logic.or_inl, &[none_s, found_s, extended]);
            d.lam_fv(hnq_fv, nqj, res)
        };

        let sel = d.const_app(p.logic.or_elim, &[qj, nqj, target, dec_j, at_qj, at_nqj]);
        d.lam_fv(hnone_fv, none_j, sel)
    };

    // --- ih = Or.inr hfound: widen the found witness's bound to `succ j`.
    let minor_found = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let bp_j = bounded_pred(d, p, q, j);
        let motive = {
            let dummy = d.fresh_fvar();
            d.lam_fv(dummy, found_j, target)
        };
        let minor = {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let lt_mj = d.lt(m, j);
            let core_ty = least_at(d, p, q, m);
            let hm_ty = d.const_app(p.logic.and, &[lt_mj, core_ty]);
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let h_lt = d.const_app(p.logic.and_left, &[lt_mj, core_ty, hm]);
            let h_core = d.const_app(p.logic.and_right, &[lt_mj, core_ty, hm]);
            let le_j = d.lemma(p.le_succ, &[j]);
            let lt_ms = d.lemma(p.lt_of_lt_of_le, &[m, j, succ_j, h_lt, le_j]);
            let lt_ms_ty = d.lt(m, succ_j);
            let pair = d.const_app(p.logic.and_intro, &[lt_ms_ty, core_ty, lt_ms, h_core]);
            let bp_s = bounded_pred(d, p, q, succ_j);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let witness = d.apply(intro, &[nat, bp_s, m, pair]);
            let res = d.const_app(p.logic.or_inr, &[none_s, found_s, witness]);
            let with_hm = d.lam_fv(hm_fv, hm_ty, res);
            d.lam_fv(m_fv, nat, with_hm)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let res = d.apply(rec, &[nat, bp_j, motive, minor, hf]);
        d.lam_fv(hf_fv, found_j, res)
    };

    d.const_app(
        p.logic.or_elim,
        &[none_j, found_j, target, ih, minor_none, minor_found],
    )
}

// --- `Nat.lnp_of_pointwise_decision` ----------------------------------------

/// `Nat.lnp_of_pointwise_decision : ∀ (Q : Nat → Prop),
/// (∀ n, Or (Q n) (Not (Q n))) → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`
///
/// The least-number principle for a pointwise-decided predicate. Eliminate the
/// non-emptiness witness `n₀`, run
/// [`lnp_bounded_search`](super::NatPrelude::lnp_bounded_search) at the bound
/// `succ n₀`, and discard its left disjunct: it would say `Not (Q n₀)`
/// (`n₀ < succ n₀` by [`lt_succ_self`](super::NatPrelude::lt_succ_self)),
/// contradicting the witness. The right disjunct's bound `Lt m (succ n₀)` is
/// simply dropped.
pub(super) fn declare_lnp_of_pointwise_decision(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let pty = pred_ty(d);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hdec_ty = pointwise_decision(d, &p, q);
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hex_ty = inhabited(d, &p, q);
    let hex_fv = d.fresh_fvar();
    let hex = d.kernel().fvar(hex_fv);
    let concl = least_exists(d, &p, q);

    let inh_pred = inhabited_pred(d, q);
    let motive = {
        let dummy = d.fresh_fvar();
        d.lam_fv(dummy, hex_ty, concl)
    };

    let minor = {
        let n0_fv = d.fresh_fvar();
        let n0 = d.kernel().fvar(n0_fv);
        let qn0 = d.apply(q, &[n0]);
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);
        let succ_n0 = d.succ(n0);

        let none_s = none_below(d, &p, q, succ_n0);
        let found_s = found_below(d, &p, q, succ_n0);
        let search = d.lemma(p.lnp_bounded_search, &[q, hdec, succ_n0]);

        // Left disjunct is impossible: it refutes `Q n0`.
        let at_none = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let lt = d.lemma(p.lt_succ_self, &[n0]);
            let nq = d.apply(h, &[n0, lt]);
            let contradiction = d.apply(nq, &[hq]);
            let body = ex_falso(d, &p, concl, contradiction);
            d.lam_fv(h_fv, none_s, body)
        };

        // Right disjunct: drop the bound `Lt m (succ n0)`.
        let at_found = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let bp_s = bounded_pred(d, &p, q, succ_n0);
            let motive_inner = {
                let dummy = d.fresh_fvar();
                d.lam_fv(dummy, found_s, concl)
            };
            let minor_inner = {
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let lt_ms = d.lt(m, succ_n0);
                let core_ty = least_at(d, &p, q, m);
                let hm_ty = d.const_app(p.logic.and, &[lt_ms, core_ty]);
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv);
                let h_core = d.const_app(p.logic.and_right, &[lt_ms, core_ty, hm]);
                let lp = least_pred(d, &p, q);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let witness = d.apply(intro, &[nat, lp, m, h_core]);
                let with_hm = d.lam_fv(hm_fv, hm_ty, witness);
                d.lam_fv(m_fv, nat, with_hm)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let res = d.apply(rec, &[nat, bp_s, motive_inner, minor_inner, h]);
            d.lam_fv(h_fv, found_s, res)
        };

        let sel = d.const_app(
            p.logic.or_elim,
            &[none_s, found_s, concl, search, at_none, at_found],
        );
        let with_hq = d.lam_fv(hq_fv, qn0, sel);
        d.lam_fv(n0_fv, nat, with_hq)
    };

    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let body = d.apply(rec, &[nat, inh_pred, motive, minor, hex]);

    let ty = {
        let inner = d.arrow(hex_ty, concl);
        let with_dec = d.arrow(hdec_ty, inner);
        d.pi_fv(q_fv, pty, with_dec)
    };
    let value = {
        let inner = d.lam_fv(hex_fv, hex_ty, body);
        let with_dec = d.lam_fv(hdec_fv, hdec_ty, inner);
        d.lam_fv(q_fv, pty, with_dec)
    };

    d.declare_theorem(p.lnp_of_pointwise_decision, ty, value)
}

// --- `Nat.lnp_decidable` — the non-vacuity anchor ---------------------------

/// `Or (Eq Bool b true) (Not (Eq Bool b true))` at an arbitrary `b : Bool`, by
/// `Bool.rec` — a two-constructor case split, not excluded middle. The
/// `false` branch is `Or.inr` of
/// [`LogicPrelude::bool_false_ne_true`](crate::LogicPrelude::bool_false_ne_true)
/// verbatim, which IS `Not (Eq Bool false true)`.
fn bool_decides(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let t = d.bool_true();
        let is_true = d.bool_eq(x, t);
        let not_true = not_(d, p, is_true);
        let body = d.const_app(p.logic.or, &[is_true, not_true]);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let not_true = not_(d, p, is_true);
        let refl = d.bool_refl(true_);
        d.const_app(p.logic.or_inl, &[is_true, not_true, refl])
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let not_true = not_(d, p, is_true);
        let ne = d.kernel().const_(p.logic.bool_false_ne_true, vec![]);
        d.const_app(p.logic.or_inr, &[is_true, not_true, ne])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Not (Eq Bool b true) → Eq Bool b false`, by `Bool.rec`. Upgrades
/// [`lnp_of_pointwise_decision`](super::NatPrelude::lnp_of_pointwise_decision)'s
/// `Not`-shaped minimality clause into the computational `= false` form, so
/// [`lnp_decidable`](super::NatPrelude::lnp_decidable) is genuinely stronger
/// than a bare instantiation of the general theorem.
fn bool_false_of_not_true(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let t = d.bool_true();
        let f = d.bool_false();
        let is_true = d.bool_eq(x, t);
        let not_true = not_(d, p, is_true);
        let is_false = d.bool_eq(x, f);
        let body = d.arrow(not_true, is_false);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let not_true = not_(d, p, is_true);
        let refl = d.bool_refl(false_);
        let h_fv = d.fresh_fvar();
        d.lam_fv(h_fv, not_true, refl)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let not_true = not_(d, p, is_true);
        let is_false = d.bool_eq(true_, false_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let refl = d.bool_refl(true_);
        let contradiction = d.apply(h, &[refl]);
        let body = ex_falso(d, p, is_false, contradiction);
        d.lam_fv(h_fv, not_true, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Nat.lnp_decidable : ∀ (dec : Nat → Bool) (n : Nat), Eq Bool (dec n) true →
/// ∃ m, And (Eq Bool (dec m) true) (∀ k, Lt k m → Eq Bool (dec k) false)`
///
/// **The non-vacuity anchor for
/// [`lnp_unrestricted_implies_em`](super::NatPrelude::lnp_unrestricted_implies_em).**
/// The same statement as the unrestricted principle with `Q n` replaced by the
/// decidable `Eq Bool (dec n) true`, admitted axiom-free — so the boundary
/// this file certifies is the *decidability hypothesis*, not a missing proof.
///
/// [`lnp_of_pointwise_decision`](super::NatPrelude::lnp_of_pointwise_decision)
/// at `Q := fun i => Eq Bool (dec i) true`, whose decision is
/// [`bool_decides`] (a `Bool.rec` split), then [`bool_false_of_not_true`] under
/// the minimality binder to reach the computational `= false` conclusion.
pub(super) fn declare_lnp_decidable(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let bool_ty = d.bool_ty();
    let dec_ty = d.arrow(nat, bool_ty);

    let dec_fv = d.fresh_fvar();
    let dec = d.kernel().fvar(dec_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let dn = d.apply(dec, &[n]);
    let t = d.bool_true();
    let hyp_ty = d.bool_eq(dn, t);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // `Q := fun i => Eq Bool (dec i) true`.
    let q = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let di = d.apply(dec, &[i]);
        let tt = d.bool_true();
        let body = d.bool_eq(di, tt);
        d.lam_fv(i_fv, nat, body)
    };

    // The stated conclusion: `∃ m, And (dec m = true) (∀ k, Lt k m → dec k = false)`.
    let target_pred = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let dm = d.apply(dec, &[m]);
        let tt = d.bool_true();
        let head = d.bool_eq(dm, tt);
        let min_ty = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lt = d.lt(k, m);
            let dk = d.apply(dec, &[k]);
            let ff = d.bool_false();
            let is_false = d.bool_eq(dk, ff);
            let imp = d.arrow(lt, is_false);
            d.pi_fv(k_fv, nat, imp)
        };
        let body = d.const_app(p.logic.and, &[head, min_ty]);
        d.lam_fv(m_fv, nat, body)
    };
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
    let target = d.apply(exists_c, &[nat, target_pred]);

    // Pointwise decision: `fun i => bool_decides (dec i)`.
    let hdec = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let di = d.apply(dec, &[i]);
        let body = bool_decides(d, &p, di);
        d.lam_fv(i_fv, nat, body)
    };

    // Non-emptiness: `Exists.intro Nat (fun i => Q i) n h`.
    let inh_pred = inhabited_pred(d, q);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    let hex = d.apply(intro, &[nat, inh_pred, n, h]);

    let general = d.lemma(p.lnp_of_pointwise_decision, &[q, hdec, hex]);

    // Convert `Not (dec k = true)` to `dec k = false` under the binder.
    let least_p = least_pred(d, &p, q);
    let motive = {
        let dummy = d.fresh_fvar();
        let ex_ty = least_exists(d, &p, q);
        d.lam_fv(dummy, ex_ty, target)
    };
    let minor = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let qm = d.apply(q, &[m]);
        let nb = none_below(d, &p, q, m);
        let hm_ty = d.const_app(p.logic.and, &[qm, nb]);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_head = d.const_app(p.logic.and_left, &[qm, nb, hm]);
        let h_min = d.const_app(p.logic.and_right, &[qm, nb, hm]);

        let dm = d.apply(dec, &[m]);
        let tt = d.bool_true();
        let head_ty = d.bool_eq(dm, tt);

        let new_min = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lt_ty = d.lt(k, m);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let nq = d.apply(h_min, &[k, hk]);
            let dk = d.apply(dec, &[k]);
            let conv = bool_false_of_not_true(d, &p, dk);
            let res = d.apply(conv, &[nq]);
            let with_hk = d.lam_fv(hk_fv, lt_ty, res);
            d.lam_fv(k_fv, nat, with_hk)
        };
        let new_min_ty = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lt = d.lt(k, m);
            let dk = d.apply(dec, &[k]);
            let ff = d.bool_false();
            let is_false = d.bool_eq(dk, ff);
            let imp = d.arrow(lt, is_false);
            d.pi_fv(k_fv, nat, imp)
        };
        let pair = d.const_app(p.logic.and_intro, &[head_ty, new_min_ty, h_head, new_min]);
        let intro2 = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let witness = d.apply(intro2, &[nat, target_pred, m, pair]);
        let with_hm = d.lam_fv(hm_fv, hm_ty, witness);
        d.lam_fv(m_fv, nat, with_hm)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let body = d.apply(rec, &[nat, least_p, motive, minor, general]);

    let ty = {
        let inner = d.arrow(hyp_ty, target);
        let with_n = d.pi_fv(n_fv, nat, inner);
        d.pi_fv(dec_fv, dec_ty, with_n)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, body);
        let with_n = d.lam_fv(n_fv, nat, inner);
        d.lam_fv(dec_fv, dec_ty, with_n)
    };

    d.declare_theorem(p.lnp_decidable, ty, value)
}

// --- `Nat.em_implies_lnp` ---------------------------------------------------

/// `Nat.em_implies_lnp : (∀ (P : Prop), Or P (Not P)) →
/// ∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))`
///
/// The converse of
/// [`lnp_unrestricted_implies_em`](super::NatPrelude::lnp_unrestricted_implies_em),
/// and the reason this row says the price is **exactly** excluded middle
/// rather than *at least* excluded middle: excluded middle supplies
/// [`lnp_of_pointwise_decision`](super::NatPrelude::lnp_of_pointwise_decision)'s
/// hypothesis at `fun n => em (Q n)`, and the theorem does the rest. Nothing
/// else is needed, so the two principles are interderivable over this prelude.
pub(super) fn declare_em_implies_lnp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pty = pred_ty(d);

    let em_ty = excluded_middle(d, &p);
    let em_fv = d.fresh_fvar();
    let em = d.kernel().fvar(em_fv);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hex_ty = inhabited(d, &p, q);
    let hex_fv = d.fresh_fvar();
    let hex = d.kernel().fvar(hex_fv);
    let concl = least_exists(d, &p, q);

    let hdec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let qn = d.apply(q, &[n]);
        let body = d.apply(em, &[qn]);
        d.lam_fv(n_fv, nat, body)
    };
    let body = d.lemma(p.lnp_of_pointwise_decision, &[q, hdec, hex]);

    let ty = {
        let inner = d.arrow(hex_ty, concl);
        let with_q = d.pi_fv(q_fv, pty, inner);
        d.arrow(em_ty, with_q)
    };
    let value = {
        let inner = d.lam_fv(hex_fv, hex_ty, body);
        let with_q = d.lam_fv(q_fv, pty, inner);
        d.lam_fv(em_fv, em_ty, with_q)
    };

    d.declare_theorem(p.em_implies_lnp, ty, value)
}

// --- `Nat.lnp_unrestricted_implies_em` — the row-2 statement ----------------

/// `Nat.lnp_unrestricted_implies_em :
/// (∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k)))
/// → ∀ (P : Prop), Or P (Not P)`
///
/// **ADR-0603 row 2 for the least-number principle over `Nat`.** The
/// hypothesis is spelled out inline rather than behind a `Definition`, so the
/// rendered type is the whole claim and nothing about the conclusion can hide
/// in an abbreviation.
///
/// See the module doc for the argument. The predicate is
/// `Qₚ n := Or (Eq Nat n 1) (And (Eq Nat n 0) P)`; only the numerals `0` and
/// `1` are ever formed.
pub(super) fn declare_lnp_unrestricted_implies_em(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let prop = prop_sort(d);

    let hlnp_ty = unrestricted_lnp(d, &p);
    let hlnp_fv = d.fresh_fvar();
    let hlnp = d.kernel().fvar(hlnp_fv);

    let prop_fv = d.fresh_fvar();
    let prop_var = d.kernel().fvar(prop_fv);
    let not_prop = not_(d, &p, prop_var);
    let target = d.const_app(p.logic.or, &[prop_var, not_prop]);

    let zero = d.zero();
    let one_nat = d.num(1);

    // `Qp := fun n => Or (Eq Nat n 1) (And (Eq Nat n 0) P)`.
    let qp = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let z = d.zero();
        let o = d.num(1);
        let is_one = d.eq(n, o);
        let is_zero = d.eq(n, z);
        let right = d.const_app(p.logic.and, &[is_zero, prop_var]);
        let body = d.const_app(p.logic.or, &[is_one, right]);
        d.lam_fv(n_fv, nat, body)
    };

    // Non-emptiness at `n := 1`, with NO appeal to `P`.
    let hex = {
        let inh_pred = inhabited_pred(d, qp);
        let one_is_one = d.eq(one_nat, one_nat);
        let one_is_zero = d.eq(one_nat, zero);
        let right = d.const_app(p.logic.and, &[one_is_zero, prop_var]);
        let refl_one = d.refl(one_nat);
        let disj = d.const_app(p.logic.or_inl, &[one_is_one, right, refl_one]);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
        d.apply(intro, &[nat, inh_pred, one_nat, disj])
    };

    let least = d.apply(hlnp, &[qp, hex]);

    let least_p = least_pred(d, &p, qp);
    let motive = {
        let dummy = d.fresh_fvar();
        let ex_ty = least_exists(d, &p, qp);
        d.lam_fv(dummy, ex_ty, target)
    };

    let minor = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let qm = d.apply(qp, &[m]);
        let nb = none_below(d, &p, qp, m);
        let hm_ty = d.const_app(p.logic.and, &[qm, nb]);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let h_head = d.const_app(p.logic.and_left, &[qm, nb, hm]);
        let h_min = d.const_app(p.logic.and_right, &[qm, nb, hm]);

        // motive: `fun x => Qp x → (∀ k, Lt k x → Not (Qp k)) → Or P (Not P)`.
        let split_motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let qx = d.apply(qp, &[x]);
            let nbx = none_below(d, &p, qp, x);
            let inner = d.arrow(nbx, target);
            d.arrow(qx, inner)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let z = d.zero();
            let o = d.num(1);
            let q0 = d.apply(qp, &[z]);
            let nb0 = none_below(d, &p, qp, z);
            let hq_fv = d.fresh_fvar();
            let hq = d.kernel().fvar(hq_fv);
            let hmin_fv = d.fresh_fvar();

            let zero_is_one = d.eq(z, o);
            let zero_is_zero = d.eq(z, z);
            let right_ty = d.const_app(p.logic.and, &[zero_is_zero, prop_var]);

            // `0 = 1` is absurd: `succ_ne_zero 0` after `Eq.symm`.
            let at_left = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let h_sym = d.symm(z, o, h);
                let absurd = d.lemma(p.succ_ne_zero, &[z, h_sym]);
                let body = ex_falso(d, &p, target, absurd);
                d.lam_fv(h_fv, zero_is_one, body)
            };
            // The right disjunct's second component IS `P`.
            let at_right = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let hp = d.const_app(p.logic.and_right, &[zero_is_zero, prop_var, h]);
                let np = not_(d, &p, prop_var);
                let body = d.const_app(p.logic.or_inl, &[prop_var, np, hp]);
                d.lam_fv(h_fv, right_ty, body)
            };
            let sel = d.const_app(
                p.logic.or_elim,
                &[zero_is_one, right_ty, target, hq, at_left, at_right],
            );
            let with_min = d.lam_fv(hmin_fv, nb0, sel);
            d.lam_fv(hq_fv, q0, with_min)
        };

        let at_succ = |d: &mut NatDev<'_>, j: ExprId| -> ExprId {
            let succ_j = d.succ(j);
            let z = d.zero();
            let qs = d.apply(qp, &[succ_j]);
            let nbs = none_below(d, &p, qp, succ_j);
            let hq_fv = d.fresh_fvar();
            let hmin_fv = d.fresh_fvar();
            let hmin = d.kernel().fvar(hmin_fv);

            // `0 < succ j`, so minimality refutes `Qp 0`.
            let lt = d.zero_lt_succ(j);
            let not_q0 = d.apply(hmin, &[z, lt]);

            let np = not_(d, &p, prop_var);
            let refutation = {
                let hp_fv = d.fresh_fvar();
                let hp = d.kernel().fvar(hp_fv);
                let o = d.num(1);
                let zero_is_one = d.eq(z, o);
                let zero_is_zero = d.eq(z, z);
                let right_ty = d.const_app(p.logic.and, &[zero_is_zero, prop_var]);
                let refl_zero = d.refl(z);
                let pair = d.const_app(p.logic.and_intro, &[zero_is_zero, prop_var, refl_zero, hp]);
                let q0_proof = d.const_app(p.logic.or_inr, &[zero_is_one, right_ty, pair]);
                let contradiction = d.apply(not_q0, &[q0_proof]);
                d.lam_fv(hp_fv, prop_var, contradiction)
            };
            let res = d.const_app(p.logic.or_inr, &[prop_var, np, refutation]);
            let with_min = d.lam_fv(hmin_fv, nbs, res);
            d.lam_fv(hq_fv, qs, with_min)
        };

        let split = cases_zero_succ(d, m, &split_motive, &at_zero, &at_succ);
        let applied = d.apply(split, &[h_head, h_min]);
        let with_hm = d.lam_fv(hm_fv, hm_ty, applied);
        d.lam_fv(m_fv, nat, with_hm)
    };

    let rec = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    let body = d.apply(rec, &[nat, least_p, motive, minor, least]);

    let ty = {
        let with_prop = d.pi_fv(prop_fv, prop, target);
        d.arrow(hlnp_ty, with_prop)
    };
    let value = {
        let with_prop = d.lam_fv(prop_fv, prop, body);
        d.lam_fv(hlnp_fv, hlnp_ty, with_prop)
    };

    d.declare_theorem(p.lnp_unrestricted_implies_em, ty, value)
}

/// Declare the whole family, in dependency order.
pub(super) fn declare_least_number_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_lnp_bounded_search(d, p)?;
    declare_lnp_of_pointwise_decision(d, p)?;
    declare_lnp_decidable(d, p)?;
    declare_em_implies_lnp(d, p)?;
    declare_lnp_unrestricted_implies_em(d, p)?;
    Ok(())
}
