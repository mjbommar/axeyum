//! `Nat.injective_on_or_duplicate` — a self-map of `[0,n)` is either injective
//! there or has an explicit duplicate pair, CONSTRUCTIVELY.
//!
//! ## Why this is needed
//!
//! ADR-1470 reduced determinant multiplicativity's second obligation to two
//! halves: the free one (`Rat.det_row_selection_of_duplicate`, when `g`
//! collides somewhere) and the injective one
//! (`Rat.det_row_selection_injective`). Joining them into a selection lemma
//! with NO injectivity hypothesis needs exactly this disjunction, and the ADR
//! recorded it as absent and as "genuinely new, general-purpose
//! infrastructure".
//!
//! It is new, but far less than the ADR budgeted, because the search engine
//! already existed under a name nothing about injectivity would find:
//! **`Nat.lnp_bounded_search`** (`least_number.rs`) is
//!
//! ```text
//! ∀ Q, (∀ n, Or (Q n) (Not (Q n))) → ∀ n,
//!   Or (∀ k, Lt k n → Not (Q k)) (∃ m, And (Lt m n) (And (Q m) (∀ k, Lt k m → Not (Q k))))
//! ```
//!
//! — a bounded search for a pointwise-decided predicate, which is the whole
//! content of "search `[0,n)` for a collision". The ADR grepped for
//! `pigeonhole` / `exists_dup` / `not_injective`; the thing it needed is filed
//! under the least-number principle.
//!
//! ## The construction
//!
//! Two nested searches, both instances of that one theorem.
//!
//! - **Inner**, at a fixed `i`: `Q_i j := g j = g i`, searched over `[0,i)`.
//!   Pointwise decidable because `Nat.beq` decides equality
//!   (`bool_true_or_false` then `eq_of_beq_eq_true` / `ne_of_beq_eq_false`).
//!   Searching only BELOW `i` is what makes the found pair automatically
//!   distinct — no `Not (Eq i j)` obligation is ever discharged, it is
//!   `Lt m i`.
//! - **Outer**: `R i := ∃ m, And (Lt m i) (Eq Nat (g m) (g i))`, searched over
//!   `[0,n)`. Its pointwise decision IS the inner search: the inner "nothing
//!   below" branch refutes `R i` (any witness would be a `k < i` the branch
//!   already excluded), and the inner "found" branch supplies it — after
//!   dropping the leastness clause, which `R` deliberately does not carry so
//!   that the injectivity branch can build an `R` from an arbitrary witness.
//!
//! The outer "nothing below" branch gives injectivity: for `a, b < n` with
//! `g a = g b`, `Nat.trichotomy` splits `a` against `b`, and each strict side
//! builds an `R` at the LARGER index whose witness is the smaller one,
//! contradicting the branch. The outer "found" branch unpacks to `m < i < n`
//! with `g m = g i`, which is the duplicate.
//!
//! The conclusion states the pair as `Lt a b` rather than `Not (Eq a b)`:
//! strictly stronger, free from the construction, and what a caller wanting
//! `Nat.beq a b = false` (via `beq_eq_false_of_ne`) or an ordering can use.

use super::NatPrelude;
use super::finite::trichotomy;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Not P`.
fn not_(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.logic.not, &[x])
}

/// `False.rec` into `goal` from a proof of `False`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, goal: ExprId, contradiction: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// `Exists Nat pred`.
fn exists_ty(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let e = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(e, &[nat, pred])
}

/// `Exists.intro Nat pred w proof`.
fn exists_intro_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, w, proof])
}

/// Eliminate `witness : Exists Nat pred` into `target` with
/// `minor : ∀ x, pred x → target`.
fn exists_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let ex_ty = exists_ty(d, p, pred);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, ex_ty, target)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, witness])
}

/// `Or (Eq Nat x y) (Not (Eq Nat x y))` — `Nat.beq` decides equality.
fn decide_eq(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, y: ExprId) -> ExprId {
    let b = d.beq(x, y);
    let split = bool_true_or_false(d, p, b);
    let bool_true = d.bool_true();
    let bool_false = d.bool_false();
    let is_true = d.bool_eq(b, bool_true);
    let is_false = d.bool_eq(b, bool_false);
    let eq_ty = d.eq(x, y);
    let ne_ty = not_(d, p, eq_ty);
    let target = d.const_app(p.logic.or, &[eq_ty, ne_ty]);

    let on_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub = d.lemma(p.eq_of_beq_eq_true, &[x, y, h]);
        let body = d.const_app(p.logic.or_inl, &[eq_ty, ne_ty, sub]);
        d.lam_fv(h_fv, is_true, body)
    };
    let on_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let sub = d.lemma(p.ne_of_beq_eq_false, &[x, y, h]);
        let body = d.const_app(p.logic.or_inr, &[eq_ty, ne_ty, sub]);
        d.lam_fv(h_fv, is_false, body)
    };
    d.const_app(
        p.logic.or_elim,
        &[is_true, is_false, target, split, on_true, on_false],
    )
}

/// `fun j => Eq Nat (g j) (g i)` — the inner search's predicate at a fixed `i`.
fn collision_pred(d: &mut NatDev<'_>, g: ExprId, i: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let gj = d.apply(g, &[j]);
    let gi = d.apply(g, &[i]);
    let body = d.eq(gj, gi);
    d.lam_fv(j_fv, nat, body)
}

/// `∀ k, Lt k n → Not (Q k)` — `least_number.rs`'s `NoneBelow`, rebuilt here
/// because it is a private helper there.
fn none_below(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hyp = d.lt(k, n);
    let qk = d.apply(q, &[k]);
    let nqk = not_(d, p, qk);
    let body = d.arrow(hyp, nqk);
    d.pi_fv(k_fv, nat, body)
}

/// `fun m => And (Lt m n) (And (Q m) (NoneBelow Q m))` — the bounded search's
/// `Exists` predicate, matching `least_number.rs` term for term.
fn bounded_pred(d: &mut NatDev<'_>, p: &NatPrelude, q: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let lt = d.lt(m, n);
    let qm = d.apply(q, &[m]);
    let nb = none_below(d, p, q, m);
    let core = d.const_app(p.logic.and, &[qm, nb]);
    let body = d.const_app(p.logic.and, &[lt, core]);
    d.lam_fv(m_fv, nat, body)
}

/// `fun m => And (Lt m i) (Eq Nat (g m) (g i))` — `R i`'s witness predicate,
/// deliberately WITHOUT the leastness clause the search returns, so that the
/// injectivity branch can build an `R` from an arbitrary witness.
fn dup_pred(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, i: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let lt = d.lt(m, i);
    let gm = d.apply(g, &[m]);
    let gi = d.apply(g, &[i]);
    let eqn = d.eq(gm, gi);
    let body = d.const_app(p.logic.and, &[lt, eqn]);
    d.lam_fv(m_fv, nat, body)
}

/// `R := fun i => ∃ m, And (Lt m i) (Eq Nat (g m) (g i))`.
fn r_fn(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pred = dup_pred(d, p, g, i);
    let body = exists_ty(d, p, pred);
    d.lam_fv(i_fv, nat, body)
}

/// `fun b => And (Lt a n) (And (Lt b n) (And (Lt a b) (Eq Nat (g a) (g b))))`.
fn inner_result_pred(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    n: ExprId,
    a: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let lt_a_n = d.lt(a, n);
    let lt_b_n = d.lt(b, n);
    let lt_a_b = d.lt(a, b);
    let ga = d.apply(g, &[a]);
    let gb = d.apply(g, &[b]);
    let eqn = d.eq(ga, gb);
    let level3 = d.const_app(p.logic.and, &[lt_a_b, eqn]);
    let level2 = d.const_app(p.logic.and, &[lt_b_n, level3]);
    let body = d.const_app(p.logic.and, &[lt_a_n, level2]);
    d.lam_fv(b_fv, nat, body)
}

/// `fun a => ∃ b, …` — the duplicate half of the conclusion, as a predicate.
fn outer_result_pred(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = inner_result_pred(d, p, g, n, a);
    let body = exists_ty(d, p, inner);
    d.lam_fv(a_fv, nat, body)
}

/// Admit `Nat.injective_on_or_duplicate : ∀ g n, Or (InjectiveOn g n)
/// (∃ a b, Lt a n ∧ Lt b n ∧ Lt a b ∧ g a = g b)` — see the module doc.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_injective_on_or_duplicate(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inj_ty = d.const_app(p.injective_on, &[g, n]);
    let dup_outer = outer_result_pred(d, &p, g, n);
    let dup_ty = exists_ty(d, &p, dup_outer);
    let goal = d.const_app(logic.or, &[inj_ty, dup_ty]);

    let r = r_fn(d, &p, g);

    // `∀ i, Or (R i) (Not (R i))` — the inner search, read as a decision.
    let dec_r = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let q_i = collision_pred(d, g, i);
        let dec_i = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let gj = d.apply(g, &[j]);
            let gi = d.apply(g, &[i]);
            let body = decide_eq(d, &p, gj, gi);
            d.lam_fv(j_fv, nat, body)
        };
        let search = d.lemma(p.lnp_bounded_search, &[q_i, dec_i, i]);

        let none_ty = none_below(d, &p, q_i, i);
        let bpred = bounded_pred(d, &p, q_i, i);
        let found_ty = exists_ty(d, &p, bpred);

        let r_i = d.apply(r, &[i]);
        let not_r_i = not_(d, &p, r_i);
        let target = d.const_app(logic.or, &[r_i, not_r_i]);
        let simple_pred = dup_pred(d, &p, g, i);

        let on_none = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let refute = {
                let hr_fv = d.fresh_fvar();
                let hr = d.kernel().fvar(hr_fv);
                let false_ty = d.kernel().const_(logic.false_, vec![]);
                let minor = {
                    let m_fv = d.fresh_fvar();
                    let m = d.kernel().fvar(m_fv);
                    let lt_m_i = d.lt(m, i);
                    let gm = d.apply(g, &[m]);
                    let gi = d.apply(g, &[i]);
                    let eq_m = d.eq(gm, gi);
                    let hm_ty = d.const_app(logic.and, &[lt_m_i, eq_m]);
                    let hm_fv = d.fresh_fvar();
                    let hm = d.kernel().fvar(hm_fv);
                    let hlt = d.const_app(logic.and_left, &[lt_m_i, eq_m, hm]);
                    let heq = d.const_app(logic.and_right, &[lt_m_i, eq_m, hm]);
                    let bad = d.apply(h, &[m, hlt]);
                    let body = d.apply(bad, &[heq]);
                    let with_hm = d.lam_fv(hm_fv, hm_ty, body);
                    d.lam_fv(m_fv, nat, with_hm)
                };
                let body = exists_elim(d, &p, simple_pred, false_ty, hr, minor);
                d.lam_fv(hr_fv, r_i, body)
            };
            let body = d.const_app(logic.or_inr, &[r_i, not_r_i, refute]);
            d.lam_fv(h_fv, none_ty, body)
        };
        let on_found = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let minor = {
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let lt_m_i = d.lt(m, i);
                let gm = d.apply(g, &[m]);
                let gi = d.apply(g, &[i]);
                let eq_m = d.eq(gm, gi);
                let nb_m = none_below(d, &p, q_i, m);
                let core = d.const_app(logic.and, &[eq_m, nb_m]);
                let hm_ty = d.const_app(logic.and, &[lt_m_i, core]);
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv);
                let hlt = d.const_app(logic.and_left, &[lt_m_i, core, hm]);
                let rest = d.const_app(logic.and_right, &[lt_m_i, core, hm]);
                let heq = d.const_app(logic.and_left, &[eq_m, nb_m, rest]);
                let paired = d.const_app(logic.and_intro, &[lt_m_i, eq_m, hlt, heq]);
                let witness = exists_intro_at(d, &p, simple_pred, m, paired);
                let body = d.const_app(logic.or_inl, &[r_i, not_r_i, witness]);
                let with_hm = d.lam_fv(hm_fv, hm_ty, body);
                d.lam_fv(m_fv, nat, with_hm)
            };
            let body = exists_elim(d, &p, bpred, target, h, minor);
            d.lam_fv(h_fv, found_ty, body)
        };

        let body = d.const_app(
            logic.or_elim,
            &[none_ty, found_ty, target, search, on_none, on_found],
        );
        d.lam_fv(i_fv, nat, body)
    };

    let outer = d.lemma(p.lnp_bounded_search, &[r, dec_r, n]);
    let outer_none_ty = none_below(d, &p, r, n);
    let outer_bpred = bounded_pred(d, &p, r, n);
    let outer_found_ty = exists_ty(d, &p, outer_bpred);

    // --- no index collides with a smaller one: `g` is injective on `[0,n)` --
    let branch_inj = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hla_ty = d.lt(a, n);
        let hla_fv = d.fresh_fvar();
        let hla = d.kernel().fvar(hla_fv);
        let hlb_ty = d.lt(b, n);
        let hlb_fv = d.fresh_fvar();
        let hlb = d.kernel().fvar(hlb_fv);
        let ga = d.apply(g, &[a]);
        let gb = d.apply(g, &[b]);
        let heq_ty = d.eq(ga, gb);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let concl = d.eq(a, b);

        let lt_a_b = d.lt(a, b);
        let eq_a_b = d.eq(a, b);
        let lt_b_a = d.lt(b, a);

        // `a < b`: `a` is a witness that `b` collides below itself.
        let case_lt = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let pred_b = dup_pred(d, &p, g, b);
            let paired = d.const_app(logic.and_intro, &[lt_a_b, heq_ty, h2, heq]);
            let witness = exists_intro_at(d, &p, pred_b, a, paired);
            let bad = d.apply(h, &[b, hlb]);
            let contradiction = d.apply(bad, &[witness]);
            let body = ex_falso(d, &p, concl, contradiction);
            d.lam_fv(h2_fv, lt_a_b, body)
        };
        // `b < a`: symmetric, with the equation reversed.
        let case_gt = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let pred_a = dup_pred(d, &p, g, a);
            let flipped = d.symm(ga, gb, heq);
            let eq_ba = d.eq(gb, ga);
            let paired = d.const_app(logic.and_intro, &[lt_b_a, eq_ba, h2, flipped]);
            let witness = exists_intro_at(d, &p, pred_a, b, paired);
            let bad = d.apply(h, &[a, hla]);
            let contradiction = d.apply(bad, &[witness]);
            let body = ex_falso(d, &p, concl, contradiction);
            d.lam_fv(h2_fv, lt_b_a, body)
        };
        let case_eq = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            d.lam_fv(h2_fv, eq_a_b, h2)
        };

        let rest_ty = d.const_app(logic.or, &[eq_a_b, lt_b_a]);
        let rest = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = d.const_app(
                logic.or_elim,
                &[eq_a_b, lt_b_a, concl, h2, case_eq, case_gt],
            );
            d.lam_fv(h2_fv, rest_ty, body)
        };
        let tri = trichotomy(d, &p, b, a);
        let core = d.const_app(logic.or_elim, &[lt_a_b, rest_ty, concl, tri, case_lt, rest]);

        let with_eq = d.lam_fv(heq_fv, heq_ty, core);
        let with_lb = d.lam_fv(hlb_fv, hlb_ty, with_eq);
        let with_la = d.lam_fv(hla_fv, hla_ty, with_lb);
        let with_b = d.lam_fv(b_fv, nat, with_la);
        let inj_proof = d.lam_fv(a_fv, nat, with_b);

        let body = d.const_app(logic.or_inl, &[inj_ty, dup_ty, inj_proof]);
        d.lam_fv(h_fv, outer_none_ty, body)
    };

    // --- some index collides with a smaller one: that pair is the duplicate -
    let branch_dup = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let minor = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_i_n = d.lt(i, n);
            let r_i = d.apply(r, &[i]);
            let nb_i = none_below(d, &p, r, i);
            let core = d.const_app(logic.and, &[r_i, nb_i]);
            let hi_ty = d.const_app(logic.and, &[lt_i_n, core]);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let hlt = d.const_app(logic.and_left, &[lt_i_n, core, hi]);
            let rest = d.const_app(logic.and_right, &[lt_i_n, core, hi]);
            let hr = d.const_app(logic.and_left, &[r_i, nb_i, rest]);

            let pred_i = dup_pred(d, &p, g, i);
            let inner_minor = {
                let m_fv = d.fresh_fvar();
                let m = d.kernel().fvar(m_fv);
                let lt_m_i = d.lt(m, i);
                let gm = d.apply(g, &[m]);
                let gi = d.apply(g, &[i]);
                let eq_m = d.eq(gm, gi);
                let hm_ty = d.const_app(logic.and, &[lt_m_i, eq_m]);
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv);
                let h_lt_mi = d.const_app(logic.and_left, &[lt_m_i, eq_m, hm]);
                let h_eq = d.const_app(logic.and_right, &[lt_m_i, eq_m, hm]);

                // `m < i < n`, so `m < n`.
                let si = d.succ(i);
                let le_i_si = d.lemma(p.le_succ, &[i]);
                let le_i_n = d.lemma(p.le_trans, &[i, si, n, le_i_si, hlt]);
                let lt_m_n = d.lemma(p.lt_of_lt_of_le, &[m, i, n, h_lt_mi, le_i_n]);

                let level3 = d.const_app(logic.and, &[lt_m_i, eq_m]);
                let and3 = d.const_app(logic.and_intro, &[lt_m_i, eq_m, h_lt_mi, h_eq]);
                let level2 = d.const_app(logic.and, &[lt_i_n, level3]);
                let and2 = d.const_app(logic.and_intro, &[lt_i_n, level3, hlt, and3]);
                let lt_m_n_ty = d.lt(m, n);
                let and1 = d.const_app(logic.and_intro, &[lt_m_n_ty, level2, lt_m_n, and2]);

                let pred_at_m = inner_result_pred(d, &p, g, n, m);
                let inner_ex = exists_intro_at(d, &p, pred_at_m, i, and1);
                let witness = exists_intro_at(d, &p, dup_outer, m, inner_ex);
                let body = d.const_app(logic.or_inr, &[inj_ty, dup_ty, witness]);
                let with_hm = d.lam_fv(hm_fv, hm_ty, body);
                d.lam_fv(m_fv, nat, with_hm)
            };
            let body = exists_elim(d, &p, pred_i, goal, hr, inner_minor);
            let with_hi = d.lam_fv(hi_fv, hi_ty, body);
            d.lam_fv(i_fv, nat, with_hi)
        };
        let body = exists_elim(d, &p, outer_bpred, goal, h, minor);
        d.lam_fv(h_fv, outer_found_ty, body)
    };

    let proof_body = d.const_app(
        logic.or_elim,
        &[
            outer_none_ty,
            outer_found_ty,
            goal,
            outer,
            branch_inj,
            branch_dup,
        ],
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, goal);
        d.pi_fv(g_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof_body);
        d.lam_fv(g_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.injective_on_or_duplicate, ty, value)
}
