//! `Nat.permInverse` — an explicit, computable inverse for an injective
//! self-map on `[0,n)` — and the two-sided-inverse theorems it exists for.
//!
//! ## Why this file, and the representation question it answers
//!
//! The brief for this slice was the symmetric group: permutations of `[0,n)`
//! under composition, as a second worked instance of `Nat.IsGroupOn`
//! (`group.rs`). `IsGroupOn op e inv n` is stated over `op : Nat → Nat →
//! Nat`, `e : Nat`, `inv : Nat → Nat` — its carrier elements are bare `Nat`s
//! bounded by `n`. A permutation is not a `Nat`, it is a *function*
//! `Nat → Nat`, so `IsGroupOn` as written cannot be instantiated at the
//! symmetric group directly: there is no encoding of "a permutation" as a
//! natural number anywhere in this kernel (no `List`, no `Finset`, no
//! dependent pair). Two of the three options the brief posed were:
//!
//!  (a) generalise `IsGroupOn` cheaply to a version over function-valued
//!      elements, carrier membership `BijectiveOn f n` in place of `a < n`;
//!  (b) index permutations by naturals below `n!` — explicitly ruled out by
//!      the brief as unreachable in one slice, and this file does not attempt
//!      it.
//!
//! **(a) is what this file does relative to `group.rs`'s own machinery**:
//! `Nat.comp` (`relation.rs`) is already the right operation, `Nat.id`
//! (declared below) is the right identity, and `Nat.BijectiveOn`
//! (`relation.rs`) is the right carrier predicate. What was *missing* before
//! this file — and the actual blocker the previous lane hit — was the
//! **inverse**: `IsGroupOn`/any function-valued analogue needs an *explicit*
//! `inv : (Nat→Nat) → (Nat→Nat)`, not merely a proof that one exists.
//! `Nat.bijective_of_injective_on` (`relation.rs`) proves `∃`-shaped
//! surjectivity, and `Exists.rec` eliminates only into `Prop` (this kernel's
//! standing rule) — so no term of a *function* type can be extracted from it.
//! [`Nat.permInverse`](declare_perm_inverse) is that missing explicit
//! construction, built the same way `finite.rs`'s pigeonhole `compact` is:
//! total over every input via `Bool`-selected `Nat.rec`, correct only under
//! the hypotheses that make the search meaningful, proved via the
//! "generalize the selector, then instantiate at `bool_refl(condition)`"
//! trick `finite.rs::compact_eq_of_gt` and `transposition.rs`'s
//! `bool_select_nat_lt` already established (a local copy of the latter's
//! shape lives here, since `transposition.rs` may not be edited by this
//! slice).
//!
//! This file lands the inverse construction and its two-sided-inverse
//! theorems — the brief's explicit "IF ONLY STEPS 1–2 LAND, THAT IS A GOOD
//! OUTCOME" target — plus the cheap half of the group generalisation itself:
//! `Nat.id` and `Nat.comp_assoc`, the operation and identity `IsGroupOnFn`
//! would need, with associativity proved by *pure delta/beta/iota reduction*
//! (`Nat.comp` unfolds to the same normal-form lambda on both sides — no
//! `funext`, no axiom, nothing beyond what `Eq.refl` already checks). The
//! full symmetric-group `IsGroupOnFn` *instance* (closure/identity/inverse
//! laws bundled the way `group.rs::declare_mod_add_is_group` bundles ℤ/n) is
//! the natural next slice, built on exactly the four pieces landed here:
//! `Nat.comp`, `Nat.id`, `Nat.comp_assoc`, `Nat.permInverse` with its two
//! correctness theorems.
//!
//! ## What's declared
//!
//! - `Nat.permInverse (f : Nat → Nat) (n k : Nat) : Nat` — a bounded
//!   downward search: `Nat.rec` on `n` with base `0` (an arbitrary default,
//!   never reached under this file's hypotheses) and step `fun j ih =>
//!   if Nat.beq (f j) k then j else ih`. Computes the least index actually
//!   found scanning `n-1, n-2, …, 0`; **which** index among possibly-several
//!   in a non-injective `f` is unspecified by the correctness theorems below
//!   (they only ever need *some* preimage), so nothing here claims it is
//!   "the least" beyond what the recursion happens to produce.
//! - `Nat.permInverse_right : ∀ f n, SurjectiveOn f n → ∀ k, k < n →
//!   f (permInverse f n k) = k` — `f` composed with `permInverse f n` is
//!   the identity on `[0,n)`: a genuine RIGHT inverse (`f ∘ g = id`). Proved
//!   by induction on the search bound, generalizing nothing (the target `k`
//!   is fixed throughout the recursion): the base case is vacuous
//!   (`Lt i 0` is impossible), the step case-splits the witness index
//!   `i < succ j` into `i < j` (carried by the induction hypothesis, closed
//!   regardless of which way `Nat.beq (f j) k` falls via the generalize/
//!   `bool_refl` trick) or `i = j` (closed directly: `f j = k` makes
//!   `Nat.beq (f j) k` compute to `true`, selecting `j` on the nose).
//! - `Nat.permInverse_left : ∀ f n, MapsInto f n → InjectiveOn f n →
//!   ∀ i, i < n → permInverse f n (f i) = i` — `permInverse f n` composed
//!   with `f` is the identity on `[0,n)`: a genuine LEFT inverse
//!   (`g ∘ f = id`). Does **not** need `SurjectiveOn`: `i` itself is already
//!   a witness that `f i` has a preimage below `n`, so the induction above
//!   applies directly at `k := f i` with `i` as the existence witness: the
//!   search is guaranteed to land on *some* index `i₀` with `f i₀ = f i`,
//!   and `f`'s injectivity (plus `Nat.permInverse`'s own boundedness, see
//!   below) then forces `i₀ = i`.
//! - `Nat.id : Nat → Nat := fun x => x` — the identity self-map;
//!   `IsGroupOnFn`'s `e`.
//! - `Nat.comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)` — the
//!   associativity conjunct `IsGroupOnFn` (over `Nat.comp`) would need,
//!   proved by `Eq.refl`: both sides delta/beta-reduce to the literal term
//!   `fun x => f (g (h x))`, so the kernel's own conversion check *is* the
//!   proof.
//!
//! Internal to the induction (never given a kernel-level name, matching how
//! `finite.rs`'s `compact_eq_of_le`/`_of_gt`/`compact_injective` stay plain
//! Rust functions rather than declared theorems): the boundedness fact
//! `permInverse f n k < n` for `0 < n`, and the raw existence-hypothesis
//! correctness lemma both public theorems specialize.
//!
//! ## Status
//!
//! All of the above are declared here and axiom-free. No classical logic:
//! every case split is on `Nat`'s decidable order/equality (`Nat.beq`,
//! `trichotomy`-free — only `lt_or_eq_of_le`/`le_of_lt_succ`, already proved)
//! or on a concrete `Bool` value via `Bool.rec`, never on an assumed
//! excluded middle.

use super::NatPrelude;
use super::finite::ex_falso;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.permInverse`: it calls `Nat.beq` (height 1) inside
/// a `Bool.rec` selection, so `2` is strictly above what it unfolds through.
const INVERSE_INDEX_HEIGHT: u16 = 2;

/// Delta height for `Nat.id`: it calls nothing, so `1` is sound (matches
/// `Nat.comp`'s own height in `relation.rs`).
const ID_HEIGHT: u16 = 1;

/// Delta height for `Nat.IsGroupOnFn`: a plain bounded `Prop` predicate over
/// caller-supplied `op`/`inv` and `Nat.bijectiveOn` (height 1), the same
/// height `group.rs::GROUP_HEIGHT` uses for `Nat.IsGroupOn`.
const GROUP_FN_HEIGHT: u16 = 1;

/// `Nat.permInverse f m k`, built directly (no lambda redex), for a
/// caller-supplied bound `m` (usually the induction variable, not always the
/// final `n`).
fn perm_inverse_at(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, m: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.perm_inverse, &[f, m, k])
}

/// The predicate `fun i => And (Lt i m) (Eq Nat (f i) k)`, the existential
/// body `permInverse`'s correctness lemma both destructures (as a
/// hypothesis) and builds (as a witness) against.
fn exists_predicate(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, k: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let logic = p.logic;
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let bound = d.lt(i, m);
    let fi = d.apply(f, &[i]);
    let eqk = d.eq(fi, k);
    let body = d.const_app(logic.and, &[bound, eqk]);
    d.lam_fv(i_fv, nat, body)
}

/// `Exists (fun i => And (Lt i m) (Eq Nat (f i) k))`, from an
/// already-built predicate (see [`exists_predicate`]) — kept as a separate
/// step so a caller needing both the `Exists` type and the raw predicate
/// (for `Exists.rec`) shares one interned predicate term.
fn exists_of_predicate(d: &mut NatDev<'_>, pred: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let logic = d.prelude().logic;
    let e = d.kernel().const_(logic.exists_, vec![one]);
    d.apply(e, &[nat, pred])
}

/// `ha : Lt a n, hb : Lt b n ⊢ Lt (bool_select_nat cond a b) n`, for an
/// arbitrary `cond : Bool` — direct `Bool.rec` on `cond`, needing no fact
/// about which branch it actually selects. A local copy of
/// `transposition.rs::bool_select_nat_lt` (private there, and
/// `transposition.rs` is off-limits to this slice).
#[allow(clippy::too_many_arguments)]
fn bool_select_nat_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    ha: ExprId,
    hb: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let sv = d.bool_select_nat(sel, a, b);
        let body = d.lt(sv, n);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, hb, ha, cond])
}

/// `Or (Eq Nat m 0) (Lt (permInverse f m k) m)`, by induction on `m`
/// (`f`, `k` fixed throughout, captured from the enclosing scope). Base
/// `m = 0` takes the left disjunct (`Eq.refl`). Step `m = succ j`: reduce
/// the prior bound `Or (Eq j 0) (Lt (permInverse f j k) j)` to
/// `Lt (permInverse f j k) (succ j)` either way (via `zero_lt_succ`
/// transported along `j = 0`, or `lt_of_lt_of_le` through `le_succ`), then
/// [`bool_select_nat_lt`] with `a := j` (`lt_succ_self`) closes the right
/// disjunct unconditionally in the selector.
fn perm_inverse_bounded(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    m: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;

    d.induct(
        &|d, x| {
            let idx = perm_inverse_at(d, &p, f, x, k);
            let zero = d.zero();
            let eq0 = d.eq(x, zero);
            let ltx = d.lt(idx, x);
            d.const_app(logic.or, &[eq0, ltx])
        },
        &|d| {
            let zero = d.zero();
            let idx0 = perm_inverse_at(d, &p, f, zero, k);
            let eq0 = d.eq(zero, zero);
            let lt0 = d.lt(idx0, zero);
            let refl0 = d.refl(zero);
            d.const_app(logic.or_inl, &[eq0, lt0, refl0])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let zero = d.zero();
            let eq_sj0 = d.eq(sj, zero);
            let idx_j = perm_inverse_at(d, &p, f, j, k);
            let idx_sj = perm_inverse_at(d, &p, f, sj, k);
            let lt_sj = d.lt(idx_sj, sj);

            let eq_j0 = d.eq(j, zero);
            let lt_j_j = d.lt(idx_j, j);
            let idx_j_lt_sj_ty = d.lt(idx_j, sj);

            let on_eq = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let h_rev = d.symm(j, zero, h);
                let idx0 = perm_inverse_at(d, &p, f, zero, k);
                let motive = d.eq_motive(zero, &|d, x| {
                    let idxx = perm_inverse_at(d, &p, f, x, k);
                    let sx = d.succ(x);
                    d.lt(idxx, sx)
                });
                let s_zero = d.succ(zero);
                let body_at_zero = d.lemma(p.zero_lt_succ, &[zero]);
                let _ = idx0;
                let _ = s_zero;
                let result = d.transport(zero, motive, body_at_zero, j, h_rev);
                d.lam_fv(h_fv, eq_j0, result)
            };
            let on_lt = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let le_j_sj = d.lemma(p.le_succ, &[j]);
                let result = d.lemma(p.lt_of_lt_of_le, &[idx_j, j, sj, h, le_j_sj]);
                d.lam_fv(h_fv, lt_j_j, result)
            };
            let idx_j_lt_sj = d.const_app(
                logic.or_elim,
                &[eq_j0, lt_j_j, idx_j_lt_sj_ty, ih, on_eq, on_lt],
            );

            let j_lt_sj = d.lemma(p.lt_succ_self, &[j]);
            let fj = d.apply(f, &[j]);
            let cond = d.beq(fj, k);
            let sel_lt = bool_select_nat_lt(d, &p, cond, j, idx_j, sj, j_lt_sj, idx_j_lt_sj);
            d.const_app(logic.or_inr, &[eq_sj0, lt_sj, sel_lt])
        },
        m,
    )
}

/// `pos_n : Lt 0 n ⊢ Lt (permInverse f n k) n`, by eliminating
/// [`perm_inverse_bounded`]'s left disjunct (`n = 0` contradicts `pos_n`
/// via `lt_irrefl`, transported).
fn perm_inverse_lt_proof(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    n: ExprId,
    pos_n: ExprId,
) -> ExprId {
    let p = *p;
    let bounded = perm_inverse_bounded(d, &p, f, k, n);
    let zero = d.zero();
    let eq_n0 = d.eq(n, zero);
    let idx = perm_inverse_at(d, &p, f, n, k);
    let lt_n = d.lt(idx, n);

    let on_eq = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = d.eq_motive(n, &|d, x| {
            let zero = d.zero();
            d.lt(zero, x)
        });
        let z_lt_z = d.transport(n, motive, pos_n, zero, h);
        let false_pf = d.lemma(p.lt_irrefl, &[zero, z_lt_z]);
        let result = ex_falso(d, &p, lt_n, false_pf);
        d.lam_fv(h_fv, eq_n0, result)
    };
    let on_lt = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        d.lam_fv(h_fv, lt_n, h)
    };
    d.const_app(p.logic.or_elim, &[eq_n0, lt_n, lt_n, bounded, on_eq, on_lt])
}

/// `cond : Bool` (arbitrary), `ih_correct : Eq Nat (f idx_j) k` ⊢
/// `Eq Nat (f (bool_select_nat cond j idx_j)) k` — the "generalize the
/// selector, then instantiate at `bool_refl(condition)`" trick
/// (`finite.rs::compact_eq_of_gt`'s shape): the `false` branch is exactly
/// `ih_correct` (selection reduces to `idx_j`); the `true` branch derives
/// `f j = k` straight from the `Nat.beq` evidence via `eq_of_beq_eq_true`,
/// independent of `ih_correct`.
#[allow(clippy::too_many_arguments)]
fn select_correct_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    cond: ExprId,
    j: ExprId,
    idx_j: ExprId,
    ih_correct: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let true_val = d.bool_true();
    let bool_ty = d.bool_ty();

    let branch_for = |d: &mut NatDev<'_>, sel: ExprId| -> ExprId {
        let eq_cond_sel = d.bool_eq(cond, sel);
        let sel_val = d.bool_select_nat(sel, j, idx_j);
        let fsel = d.apply(f, &[sel_val]);
        let concl = d.eq(fsel, k);
        d.arrow(eq_cond_sel, concl)
    };
    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        d.lam_fv(heq_fv, heq_ty, ih_correct)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, true_val);
        let fj = d.apply(f, &[j]);
        let fj_eq_k = d.lemma(p.eq_of_beq_eq_true, &[fj, k, heq]);
        d.lam_fv(heq_fv, heq_ty, fj_eq_k)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let body = branch_for(d, sel);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

/// `Exists (fun i => And (Lt i m) (Eq Nat (f i) k)) → Eq Nat (f (permInverse
/// f m k)) k`, by induction on `m` (`f`, `k` fixed throughout). Base `m = 0`:
/// the hypothesis is vacuous (`Lt i 0` impossible), closed by `Exists.rec`
/// into `not_lt_zero`/`ex_falso`. Step `m = succ j`: destructure the witness
/// `i`, `i < succ j`, `f i = k` via `Exists.rec`; `le_of_lt_succ` +
/// `lt_or_eq_of_le` split `i` against `j`. `i < j` reuses the witness for the
/// bound-`j` existential and closes via the induction hypothesis, then
/// [`select_correct_step`] (the search step doesn't care which way
/// `Nat.beq (f j) k` falls). `i = j` transports `f i = k` to `f j = k`
/// directly, which forces `Nat.beq (f j) k = true` (`beq_eq_true_of_eq`) and
/// so `permInverse f (succ j) k` selects `j` on the nose
/// (`finite.rs::select_nat_true`).
fn perm_inverse_correct(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();

    d.induct(
        &|d, m| {
            let pred = exists_predicate(d, &p, f, k, m);
            let ex_ty = exists_of_predicate(d, pred);
            let idx = perm_inverse_at(d, &p, f, m, k);
            let fidx = d.apply(f, &[idx]);
            let concl = d.eq(fidx, k);
            d.arrow(ex_ty, concl)
        },
        &|d| {
            let zero = d.zero();
            let pred0 = exists_predicate(d, &p, f, k, zero);
            let ex0 = exists_of_predicate(d, pred0);
            let idx0 = perm_inverse_at(d, &p, f, zero, k);
            let fidx0 = d.apply(f, &[idx0]);
            let concl = d.eq(fidx0, k);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let bound_ty = d.lt(i, zero);
            let fi_ = d.apply(f, &[i]);
            let eqk_ty = d.eq(fi_, k);
            let hand_ty = d.const_app(logic.and, &[bound_ty, eqk_ty]);
            let hi = and_left(d, bound_ty, eqk_ty, hand);
            let false_pf = d.lemma(p.not_lt_zero, &[i, hi]);
            let inner_result = ex_falso(d, &p, concl, false_pf);
            let minor = {
                let with_hand = d.lam_fv(hand_fv, hand_ty, inner_result);
                d.lam_fv(i_fv, nat, with_hand)
            };

            let motive = d.kernel().lam(anon, ex0, concl, BinderInfo::Default);
            let rec = d.kernel().const_(logic.exists_rec, vec![one]);
            let applied = d.apply(rec, &[nat, pred0, motive, minor, h]);
            d.lam_fv(h_fv, ex0, applied)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let pred_sj = exists_predicate(d, &p, f, k, sj);
            let ex_sj = exists_of_predicate(d, pred_sj);
            let idx_j = perm_inverse_at(d, &p, f, j, k);
            let idx_sj = perm_inverse_at(d, &p, f, sj, k);
            let fidx_sj = d.apply(f, &[idx_sj]);
            let concl = d.eq(fidx_sj, k);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let bound_ty = d.lt(i, sj);
            let fi_ = d.apply(f, &[i]);
            let eqk_ty = d.eq(fi_, k);
            let hand_ty = d.const_app(logic.and, &[bound_ty, eqk_ty]);
            let hi = and_left(d, bound_ty, eqk_ty, hand);
            let heq_fi = and_right(d, bound_ty, eqk_ty, hand);

            let i_le_j = d.lemma(p.le_of_lt_succ, &[i, j, hi]);
            let disj = d.lemma(p.lt_or_eq_of_le, &[i, j, i_le_j]);
            let lt_ij = d.lt(i, j);
            let eq_ij = d.eq(i, j);

            let fj = d.apply(f, &[j]);
            let cond = d.beq(fj, k);
            let bsn = d.bool_select_nat(cond, j, idx_j);
            let f_bsn_ = d.apply(f, &[bsn]);
            let target_ty = d.eq(f_bsn_, k);

            let on_lt = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let and_proof = d.const_app(logic.and_intro, &[lt_ij, eqk_ty, h2, heq_fi]);
                let pred_j = exists_predicate(d, &p, f, k, j);
                let ex_j = exists_of_predicate(d, pred_j);
                let _ = ex_j;
                let intro = d.kernel().const_(logic.exists_intro, vec![one]);
                let ex_j_witness = d.apply(intro, &[nat, pred_j, i, and_proof]);
                let ih_applied = d.apply(ih, &[ex_j_witness]);
                let result = select_correct_step(d, &p, f, k, cond, j, idx_j, ih_applied);
                d.lam_fv(h2_fv, lt_ij, result)
            };
            let on_eq = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let motive2 = d.eq_motive(i, &|d, x| {
                    let fx = d.apply(f, &[x]);
                    d.eq(fx, k)
                });
                let fj_eq_k = d.transport(i, motive2, heq_fi, j, h2);
                let fj = d.apply(f, &[j]);
                let cond_true = d.lemma(p.beq_eq_true_of_eq, &[fj, k, fj_eq_k]);
                let sel_eq_j = super::finite::select_nat_true(d, cond, j, idx_j, cond_true);
                let congr_step = d.congr(bsn, j, sel_eq_j, &|d, v| d.apply(f, &[v]));
                let f_bsn = d.apply(f, &[bsn]);
                let result = d.trans(f_bsn, fj, k, congr_step, fj_eq_k);
                d.lam_fv(h2_fv, eq_ij, result)
            };
            let inner_result = d.const_app(
                logic.or_elim,
                &[lt_ij, eq_ij, target_ty, disj, on_lt, on_eq],
            );

            let minor = {
                let with_hand = d.lam_fv(hand_fv, hand_ty, inner_result);
                d.lam_fv(i_fv, nat, with_hand)
            };
            let motive = d.kernel().lam(anon, ex_sj, concl, BinderInfo::Default);
            let rec = d.kernel().const_(logic.exists_rec, vec![one]);
            let applied = d.apply(rec, &[nat, pred_sj, motive, minor, h]);
            d.lam_fv(h_fv, ex_sj, applied)
        },
        n,
    )
}

/// Admit `Nat.permInverse : (Nat → Nat) → Nat → Nat → Nat`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_perm_inverse(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let anon = d.anon_name();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let zero = d.zero();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let cond = d.beq(fj, k);
        let body = d.bool_select_nat(cond, j, ih);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let one = d.level_one();
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    let body = d.apply(rec, &[motive, zero, minor_succ, n]);

    // Curried argument order must be `f, n, k` (matching this file's
    // `perm_inverse_at` calling convention `[f, m, k]`), so `k` is the
    // OUTERMOST-but-one binder built INNERMOST here (wrapping `body`
    // directly), then `n`, then `f` — nested `lam_fv` builds outermost-last.
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        let over_n = d.arrow(nat, over_k);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.perm_inverse,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(INVERSE_INDEX_HEIGHT),
    })
}

/// Admit `Nat.permInverse_right : ∀ f n, SurjectiveOn f n → ∀ k, k < n →
/// f (permInverse f n k) = k`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_perm_inverse_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let surj_ty = d.const_app(p.surjective_on, &[f, n]);
    let surj_fv = d.fresh_fvar();
    let surj = d.kernel().fvar(surj_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_ty = d.lt(k, n);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);

    let ex = d.apply(surj, &[k, hk]);
    let correct = perm_inverse_correct(d, &p, f, k, n);
    let result = d.apply(correct, &[ex]);

    let idx = perm_inverse_at(d, &p, f, n, k);
    let fidx = d.apply(f, &[idx]);
    let concl = d.eq(fidx, k);

    let value = {
        let with_hk = d.lam_fv(hk_fv, hk_ty, result);
        let with_k = d.lam_fv(k_fv, nat, with_hk);
        let with_surj = d.lam_fv(surj_fv, surj_ty, with_k);
        let with_n = d.lam_fv(n_fv, nat, with_surj);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let with_hk = d.arrow(hk_ty, concl);
        let with_k = d.pi_fv(k_fv, nat, with_hk);
        let with_surj = d.arrow(surj_ty, with_k);
        let with_n = d.pi_fv(n_fv, nat, with_surj);
        d.pi_fv(f_fv, fn_ty, with_n)
    };
    d.declare_theorem(p.perm_inverse_right, ty, value)
}

/// Admit `Nat.permInverse_left : ∀ f n, MapsInto f n → InjectiveOn f n →
/// ∀ i, i < n → permInverse f n (f i) = i`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_perm_inverse_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let logic = p.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let maps_ty = d.const_app(p.maps_into, &[f, n]);
    // `MapsInto f n` is not needed by this proof (the existence witness for
    // `k := f i` is `i` itself, which needs only `i < n`), but is kept as a
    // hypothesis so the theorem states the natural "inverse of a self-map"
    // shape rather than the more general "inverse of any function" one.
    let maps_fv = d.fresh_fvar();
    let inj_ty = d.const_app(p.injective_on, &[f, n]);
    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    let fi = d.apply(f, &[i]);

    // Existence witness for `perm_inverse_correct` at k := f i: i itself,
    // with `Eq Nat (f i) (f i)` by `Eq.refl`.
    let pred = exists_predicate(d, &p, f, fi, n);
    let ex_ty = exists_of_predicate(d, pred);
    let refl_fi = d.refl(fi);
    let and_ty_r = d.eq(fi, fi);
    let and_proof = d.const_app(logic.and_intro, &[hi_ty, and_ty_r, hi, refl_fi]);
    let one = d.level_one();
    let intro = d.kernel().const_(logic.exists_intro, vec![one]);
    let ex_witness = d.apply(intro, &[nat, pred, i, and_proof]);
    let _ = ex_ty;

    let correct = perm_inverse_correct(d, &p, f, fi, n);
    let correct_at_i = d.apply(correct, &[ex_witness]); // Eq Nat (f (permInverse f n fi)) fi

    // `0 < n` from `i < n` via `zero_le i` and transitivity.
    let zero = d.zero();
    let zero_le_i = d.lemma(p.zero_le, &[i]);
    let pos_n = d.lemma(p.lt_of_le_of_lt, &[zero, i, n, zero_le_i, hi]);

    let idx = perm_inverse_at(d, &p, f, n, fi);
    let idx_lt_n = perm_inverse_lt_proof(d, &p, f, fi, n, pos_n);

    // `InjectiveOn f n` at (idx, i): `f idx = f i` (= `correct_at_i`), both
    // bounded by `n`, gives `idx = i`.
    let idx_eq_i = d.apply(inj, &[idx, i, idx_lt_n, hi, correct_at_i]);

    let concl = d.eq(idx, i);

    let value = {
        let with_hi = d.lam_fv(hi_fv, hi_ty, idx_eq_i);
        let with_i = d.lam_fv(i_fv, nat, with_hi);
        let with_inj = d.lam_fv(inj_fv, inj_ty, with_i);
        let with_maps = d.lam_fv(maps_fv, maps_ty, with_inj);
        let with_n = d.lam_fv(n_fv, nat, with_maps);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let with_hi = d.arrow(hi_ty, concl);
        let with_i = d.pi_fv(i_fv, nat, with_hi);
        let with_inj = d.arrow(inj_ty, with_i);
        let with_maps = d.arrow(maps_ty, with_inj);
        let with_n = d.pi_fv(n_fv, nat, with_maps);
        d.pi_fv(f_fv, fn_ty, with_n)
    };
    d.declare_theorem(p.perm_inverse_left, ty, value)
}

/// Admit `Nat.id : Nat → Nat := fun x => x`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_id(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let value = d.lam_fv(x_fv, nat, x);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.id,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ID_HEIGHT),
    })
}

/// Admit `Nat.comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)`
/// — the associativity conjunct an `IsGroupOnFn` predicate over `Nat.comp`
/// would need. Both sides delta/beta-reduce to the literal term
/// `fun x => f (g (h x))`, so `Eq.refl` of that common normal form is
/// accepted by the kernel's own conversion check — no `funext`, no axiom.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
fn declare_comp_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let one = d.level_one();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let comp_fg = d.const_app(p.comp, &[f, g]);
    let lhs = d.const_app(p.comp, &[comp_fg, h]);
    let comp_gh = d.const_app(p.comp, &[g, h]);
    let rhs = d.const_app(p.comp, &[f, comp_gh]);

    // `d.eq`/`d.refl` are hardcoded to `Eq Nat`; `lhs`/`rhs` are `Nat → Nat`,
    // so `Eq`/`Eq.refl` are built directly at the function carrier here (the
    // same pattern `helpers.rs::apply_nat_function_equality` uses).
    let eq_const = d.kernel().const_(p.logic.eq, vec![one]);
    let concl = d.apply(eq_const, &[fn_ty, lhs, rhs]);
    let refl_const = d.kernel().const_(p.logic.eq_refl, vec![one]);
    let proof = d.apply(refl_const, &[fn_ty, lhs]);

    let value = {
        let with_h = d.lam_fv(h_fv, fn_ty, proof);
        let with_g = d.lam_fv(g_fv, fn_ty, with_h);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let with_h = d.pi_fv(h_fv, fn_ty, concl);
        let with_g = d.pi_fv(g_fv, fn_ty, with_h);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    d.declare_theorem(p.comp_assoc, ty, value)
}

/// `Eq.{1} fn_ty x y`, for `fn_ty` the `Nat → Nat` carrier — `d.eq` is
/// hardcoded to `Eq Nat`, so every function-valued equality in
/// `Nat.IsGroupOnFn` is built directly this way (the same pattern
/// [`declare_comp_assoc`] and `helpers.rs::apply_nat_function_equality` use).
fn fn_eq(d: &mut NatDev<'_>, fn_ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = d.prelude().logic;
    let eq_const = d.kernel().const_(logic.eq, vec![one]);
    d.apply(eq_const, &[fn_ty, x, y])
}

/// `closure op n := ∀ a b, BijectiveOn a n → BijectiveOn b n →
/// BijectiveOn (op a b) n` — `Nat.IsGroupOnFn`'s closure conjunct, the
/// function-valued analogue of `group.rs::closure_prop`'s `a<n → b<n →
/// op a b<n` with `BijectiveOn · n` standing in for `· < n` as carrier
/// membership.
fn closure_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let ab = d.apply(op, &[a, b]);
    let concl = d.const_app(p.bijective_on, &[ab, n]);
    let bij_b = d.const_app(p.bijective_on, &[b, n]);
    let step_b = d.arrow(bij_b, concl);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, step_b);
    let with_b = d.pi_fv(b_fv, fn_ty, inner);
    d.pi_fv(a_fv, fn_ty, with_b)
}

/// `assoc op n := ∀ a b c, BijectiveOn a n → BijectiveOn b n →
/// BijectiveOn c n → op (op a b) c = op a (op b c)`.
fn assoc_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let ab = d.apply(op, &[a, b]);
    let ab_c = d.apply(op, &[ab, c]);
    let bc = d.apply(op, &[b, c]);
    let a_bc = d.apply(op, &[a, bc]);
    let concl = fn_eq(d, fn_ty, ab_c, a_bc);
    let bij_c = d.const_app(p.bijective_on, &[c, n]);
    let step_c = d.arrow(bij_c, concl);
    let bij_b = d.const_app(p.bijective_on, &[b, n]);
    let step_b = d.arrow(bij_b, step_c);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, step_b);
    let with_c = d.pi_fv(c_fv, fn_ty, inner);
    let with_b = d.pi_fv(b_fv, fn_ty, with_c);
    d.pi_fv(a_fv, fn_ty, with_b)
}

/// `BijectiveOn e n`, the bound half of `identity`.
fn identity_bound_prop_fn(d: &mut NatDev<'_>, p: &NatPrelude, e: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.bijective_on, &[e, n])
}

/// `∀ a, BijectiveOn a n → (op a e = a ∧ op e a = a)`, the quantified half
/// of `identity`.
fn identity_forall_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ae = d.apply(op, &[a, e]);
    let ea = d.apply(op, &[e, a]);
    let left_eq = fn_eq(d, fn_ty, ae, a);
    let right_eq = fn_eq(d, fn_ty, ea, a);
    let both = d.const_app(logic.and, &[left_eq, right_eq]);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, both);
    d.pi_fv(a_fv, fn_ty, inner)
}

/// `identity op e n := BijectiveOn e n ∧ (∀ a, BijectiveOn a n → op a e=a
/// ∧ op e a=a)`.
fn identity_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    n: ExprId,
) -> ExprId {
    let logic = p.logic;
    let bound = identity_bound_prop_fn(d, p, e, n);
    let forall_part = identity_forall_prop_fn(d, p, fn_ty, op, e, n);
    d.const_app(logic.and, &[bound, forall_part])
}

/// `inverse op e inv n := ∀ a, BijectiveOn a n → BijectiveOn (inv a) n ∧
/// (op a (inv a)=e ∧ op (inv a) a=e)`.
fn inverse_prop_fn(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fn_ty: ExprId,
    op: ExprId,
    e: ExprId,
    inv: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let logic = p.logic;
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let ia = d.apply(inv, &[a]);
    let ia_bij = d.const_app(p.bijective_on, &[ia, n]);
    let a_ia = d.apply(op, &[a, ia]);
    let ia_a = d.apply(op, &[ia, a]);
    let left_eq = fn_eq(d, fn_ty, a_ia, e);
    let right_eq = fn_eq(d, fn_ty, ia_a, e);
    let eqs = d.const_app(logic.and, &[left_eq, right_eq]);
    let bundle = d.const_app(logic.and, &[ia_bij, eqs]);
    let bij_a = d.const_app(p.bijective_on, &[a, n]);
    let inner = d.arrow(bij_a, bundle);
    d.pi_fv(a_fv, fn_ty, inner)
}

/// Admit `Nat.IsGroupOnFn (op : (Nat→Nat)→(Nat→Nat)→(Nat→Nat)) (e : Nat→Nat)
/// (inv : (Nat→Nat)→(Nat→Nat)) (n : Nat) : Prop := closure ∧ (associativity
/// ∧ (identity ∧ inverse))` — the representation-(a) generalisation of
/// `group.rs::IsGroupOn` this file's module doc argues for: the same four
/// conjuncts, `Nat → Nat`-valued elements in place of bare `Nat`s, and
/// `BijectiveOn · n` in place of `· < n` as carrier membership (the natural
/// "is a permutation of `[0,n)`" predicate, already proved equivalent to
/// `InjectiveOn ∧ MapsInto` by `relation.rs::bijective_of_injective_on`).
///
/// Not yet instantiated at the symmetric group here (that is the natural
/// next slice: `Nat.comp`/`Nat.id`/[`declare_comp_assoc`]'s
/// `Nat.comp_assoc` are exactly the operation, identity, and associativity
/// conjunct; the inverse conjunct needs `Nat.permInverse_left`/`_right`
/// plus a `BijectiveOn`-preservation lemma for `Nat.comp` this slice does
/// not build) — landing the predicate itself, with `Nat.comp_assoc` already
/// proved satisfying its associativity shape, is this slice's target.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_group_on_fn(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();
    let unop_ty = d.arrow(fn_ty, fn_ty);
    let binop_ty = d.arrow(fn_ty, unop_ty);

    let op_fv = d.fresh_fvar();
    let op = d.kernel().fvar(op_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let closure = closure_prop_fn(d, &p, fn_ty, op, n);
    let assoc = assoc_prop_fn(d, &p, fn_ty, op, n);
    let identity = identity_prop_fn(d, &p, fn_ty, op, e, n);
    let inverse = inverse_prop_fn(d, &p, fn_ty, op, e, inv, n);

    let logic = p.logic;
    let id_inv = d.const_app(logic.and, &[identity, inverse]);
    let assoc_rest = d.const_app(logic.and, &[assoc, id_inv]);
    let body = d.const_app(logic.and, &[closure, assoc_rest]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_inv = d.lam_fv(inv_fv, unop_ty, with_n);
        let with_e = d.lam_fv(e_fv, fn_ty, with_inv);
        d.lam_fv(op_fv, binop_ty, with_e)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        let over_inv = d.arrow(unop_ty, over_n);
        let over_e = d.arrow(fn_ty, over_inv);
        d.arrow(binop_ty, over_e)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_group_on_fn,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GROUP_FN_HEIGHT),
    })
}

/// Admit `Nat.permInverse`, its two two-sided-inverse theorems, `Nat.id`,
/// `Nat.comp_assoc`, and `Nat.IsGroupOnFn`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_permutation_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_perm_inverse(d, p)?;
    declare_perm_inverse_right(d, p)?;
    declare_perm_inverse_left(d, p)?;
    declare_id(d, p)?;
    declare_comp_assoc(d, p)?;
    declare_is_group_on_fn(d, p)?;
    Ok(())
}
