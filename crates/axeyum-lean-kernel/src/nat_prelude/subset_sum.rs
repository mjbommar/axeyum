//! `Nat.sumRangeIf` — the ADDITIVE half of `Nat.prodRangeIf`'s pattern: a
//! fold restricted to a *predicate-defined subset* of `[0,n)`.
//!
//! ## Why this exists, and why it did not exist
//!
//! ADR-1540 and ADR-1544 both stopped at the same wall. Eisenstein's residue
//! 2 — reconciling `Nat.leastResidue` with `Nat.gaussFold` — is
//!
//! ```text
//! Σ_{j<m} leastResidue = Σ_{j<m} gaussFold + pp·N − 2·Σ_{j : sign j} gaussFold
//! ```
//!
//! and that last term is a CONDITIONAL sum. Both prior lanes measured the
//! absence rather than guessing at it: `examples/shape_search --name-like
//! sumRangeIf` returns `ABSENT` against a `prodRangeIf` positive control
//! returning 12 declarations. This lane re-ran that measurement on a freshly
//! built binary (`declarations=2092`, so not a stale artifact reporting a
//! false absence) and got the same two verdicts.
//!
//! So the sum/count/product triangle was missing exactly one corner:
//! `Nat.countRange p n` counts a predicate subset (`totient.rs`),
//! `Nat.prodRangeIf p f n` multiplies over one (`subset_product.rs`), and
//! nothing summed over one. `Nat.sumRange f n` (`defs.rs`) sums the FULL
//! range only.
//!
//! ## The construction, copied from `subset_product.rs` with one change
//!
//! `Nat.sumRangeIf p f n := Nat.sumRange (fun i => bool_select_nat (p i)
//! (f i) 0) n`. Two conventions are inherited verbatim from
//! `Nat.prodRangeIf` and `Nat.countRange`:
//!
//! - **The predicate is `Bool`-valued**, never `Prop`-valued, and selection
//!   goes through [`NatOps::bool_select_nat`] (`Bool.rec` at `Nat`, the
//!   computational if/then/else).
//! - **Delegate to the already-declared fold**, do not re-derive `Nat.rec`.
//!   That is what keeps the two defining equations pure `Eq.refl`.
//!
//! The ONE change from the product side is the "not selected" value: `0`
//! here, the additive identity, where `prodRangeIf` uses `1`. Everything
//! else — the argument order, the bounded (`Lt i n`) congruence, the
//! `Regular` delta height one above the fold it calls — is the same.
//!
//! ## What's declared
//!
//! - `Nat.sumRangeIf`, the definition above.
//! - `Nat.sumRangeIf_zero` / `Nat.sumRangeIf_succ`, the defining equations,
//!   both `Eq.refl`. Note the `succ` equation puts the new term on the
//!   RIGHT (`sumRangeIf p f (succ n) = sumRangeIf p f n + sel (p n) (f n)`),
//!   because `Nat.sumRange`'s own step is `add ih (f j)` and `Nat.add`
//!   recurses on its RIGHT argument.
//! - `Nat.sumRangeIf_congr_lt`, the bounded congruence: `p`/`f` agreeing
//!   pointwise with `q`/`g` on every index `< n` gives equal sums. Bounded
//!   rather than unconditional, matching `sumRange_congr_lt` and
//!   `prodRangeIf_congr_lt`.
//! - `Nat.sumRangeIf_compl`, **the split**: `sumRangeIf p f n + sumRangeIf
//!   (setCompl p) f n = sumRange f n`. This is the theorem a reconciliation
//!   consumes, and it is stated with `Nat.setCompl` (`finite_set.rs`) rather
//!   than with a second predicate plus a complementarity hypothesis, for one
//!   reason: this kernel has no `Bool.not` (measured — `shape_search
//!   --name-like bnot` returns `ABSENT`), and `setCompl p := fun k => if p k
//!   then false else true` IS that missing function, already declared and
//!   already carrying its own involutivity and De Morgan laws. So the split
//!   needs no hypothesis at all, and it is the exact additive twin of
//!   `Nat.countRange_compl` (`finite_set.rs`), whose proof shape it copies:
//!   induction on `n`, one four-term regroup, one pointwise `Bool.rec`.
//!
//! `Nat.countRange p n = sumRangeIf p (fun _ => 1) n` is TRUE but is not
//! declared here — `Nat.countRange_eq_sumRange` (`totient.rs`) already
//! states the same content in the form its consumers use.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::{BinderInfo, ExprId};

// ============================================================================
// Shared local shapes.
//
// `bool_select_bool` and `add_regroup_four` are per-file-private copies of
// `finite_set.rs`'s helpers of the same names -- this prelude's own stated
// convention for a shape a sibling module needs but does not own (see
// `subset_product.rs`'s `bool_congr_nat`, and `fibonacci.rs`'s own
// `add_regroup_four`, and `finite_set.rs`'s note that "this prelude has no
// `add_add_add_comm`").
// ============================================================================

/// `Bool.rec (fun _ => Bool) on_false on_true condition : Bool` — the
/// computational if/then/else at `Bool` itself, which is what `Nat.setCompl`
/// delta-unfolds to at a point.
fn bool_select_bool(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `(a+b)+(c+e) = (a+c)+(b+e)`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`binomial.rs`, `div_mod_lemmas.rs`,
/// `finite_set.rs`, `fibonacci.rs`, `rec_agreement.rs`,
/// `count_range_reversal.rs`, `eisenstein_lemma.rs`).
fn add_regroup_four(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
) -> ExprId {
    // Generic-then-apply (`prove_eq_at`): a caller may pass compound
    // arguments outside the ring fragment; `prove_eq` on the literal terms
    // would (correctly) decline `NonRing` on those.
    crate::ring::nat::prove_eq_at(d, p, &[a, b, c, e], &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let ce = d.add(c, e);
        let lhs = d.add(ab, ce);
        let ac = d.add(a, c);
        let be = d.add(b, e);
        let rhs = d.add(ac, be);
        (lhs, rhs)
    })
    .unwrap_or_else(|err| panic!("ring declined add_regroup_four: {err:?}"))
}

// ============================================================================
// `Nat.sumRangeIf`.
// ============================================================================

/// `fun i => bool_select_nat (pred i) (f i) 0`, the selector
/// `Nat.sumRangeIf` folds `Nat.sumRange` over.
fn selector(d: &mut NatDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let zero = d.zero();
    let sel = d.bool_select_nat(pi, fi, zero);
    d.lam_fv(i_fv, nat, sel)
}

/// `sumRangeIf(d, pred, f, n)`, i.e. `Nat.sumRange (selector pred f) n`.
fn sum_range_if(d: &mut NatDev<'_>, pred: ExprId, f: ExprId, n: ExprId) -> ExprId {
    let sel = selector(d, pred, f);
    d.sum_range(sel, n)
}

/// `Nat.sumRangeIf : (Nat → Bool) → (Nat → Nat) → Nat → Nat := fun pred f n
/// => Nat.sumRange (fun i => bool_select_nat (pred i) (f i) 0) n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_sum_range_if(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = sum_range_if(d, pred, f, n);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_f = d.lam_fv(f_fv, fn_ty, with_n);
        d.lam_fv(pred_fv, pred_ty, with_f)
    };
    let ty = {
        let over_n = d.arrow(nat, nat);
        let over_f = d.arrow(fn_ty, over_n);
        d.arrow(pred_ty, over_f)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_range_if,
        uparams: vec![],
        ty,
        value,
        // Strictly greater than `sum_range`'s own height (`Regular(2)`,
        // `defs.rs`), the definition this one calls.
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// `Nat.sumRangeIf_zero`/`Nat.sumRangeIf_succ`: both hold by `Eq.refl`,
/// delta-unfolding into `Nat.sumRange`'s own `Nat.rec` reduction.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_sum_range_if_defining_equations(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = sum_range_if(d, pred, f, zero);
        let zero_v = d.zero();
        let stmt = d.eq(lhs, zero_v);
        let proof = d.refl(zero_v);
        let ty = {
            let with_f = d.pi_fv(f_fv, fn_ty, stmt);
            d.pi_fv(pred_fv, pred_ty, with_f)
        };
        let value = {
            let with_f = d.lam_fv(f_fv, fn_ty, proof);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        d.declare_theorem(p.sum_range_if_zero, ty, value)?;
    }
    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = sum_range_if(d, pred, f, sn);
        let prior = sum_range_if(d, pred, f, n);
        let pn = d.apply(pred, &[n]);
        let fn_at_n = d.apply(f, &[n]);
        let zero = d.zero();
        let sel = d.bool_select_nat(pn, fn_at_n, zero);
        let rhs = d.add(prior, sel);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            let with_f = d.pi_fv(f_fv, fn_ty, with_n);
            d.pi_fv(pred_fv, pred_ty, with_f)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            let with_f = d.lam_fv(f_fv, fn_ty, with_n);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        d.declare_theorem(p.sum_range_if_succ, ty, value)?;
    }
    Ok(())
}

// ============================================================================
// `Nat.sumRangeIf_congr_lt`.
// ============================================================================

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)`, via [`NatOps::bool_transport`] —
/// the `Bool`-hypothesis analogue of [`NatOps::congr`]. A local copy of
/// `subset_product.rs`'s private helper of the same name and shape.
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h_pq : Eq Bool p_i q_i`, `h_fg : Eq Nat f_i g_i` ⊢ `Eq Nat
/// (bool_select_nat p_i f_i 0) (bool_select_nat q_i g_i 0)`.
fn bool_select_congr(
    d: &mut NatDev<'_>,
    p_i: ExprId,
    q_i: ExprId,
    h_pq: ExprId,
    f_i: ExprId,
    g_i: ExprId,
    h_fg: ExprId,
) -> ExprId {
    let zero = d.zero();
    let start = d.bool_select_nat(p_i, f_i, zero);
    let mid = d.bool_select_nat(q_i, f_i, zero);
    let end_ = d.bool_select_nat(q_i, g_i, zero);

    let step1 = bool_congr_nat(d, p_i, q_i, h_pq, &|d, x| d.bool_select_nat(x, f_i, zero));
    let step2 = d.congr(f_i, g_i, h_fg, &|d, t| d.bool_select_nat(q_i, t, zero));

    d.trans(start, mid, end_, step1, step2)
}

/// `∀ i, Lt i bound → Eq Bool (a i) (b i)`.
fn bounded_pointwise_bool(d: &mut NatDev<'_>, a: ExprId, b: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let ai = d.apply(a, &[i]);
    let bi = d.apply(b, &[i]);
    let eqn = d.bool_eq(ai, bi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `∀ i, Lt i bound → Eq Nat (a i) (b i)`.
fn bounded_pointwise_nat(d: &mut NatDev<'_>, a: ExprId, b: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp = d.lt(i, bound);
    let ai = d.apply(a, &[i]);
    let bi = d.apply(b, &[i]);
    let eqn = d.eq(ai, bi);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(i_fv, nat, body)
}

/// `Nat.sumRangeIf_congr_lt : ∀ p q f g n, (∀ i, Lt i n → Eq Bool (p i)
/// (q i)) → (∀ i, Lt i n → Eq Nat (f i) (g i)) → Eq Nat (sumRangeIf p f n)
/// (sumRangeIf q g n)`.
///
/// Induction on `n` with `p, q, f, g` fixed, exactly
/// `prodRangeIf_congr_lt`'s shape: the motive threads BOTH bounded-pointwise
/// hypotheses, weakened from `Lt i (succ j)` to `Lt i j` for the recursive
/// call and applied at `i = j` itself to rewrite the new top selector.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
fn declare_sum_range_if_congr_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let qq_fv = d.fresh_fvar();
    let qq = d.kernel().fvar(qq_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let hyp_p = bounded_pointwise_bool(d, pp, qq, x);
        let hyp_f = bounded_pointwise_nat(d, f, g, x);
        let lhs = sum_range_if(d, pp, f, x);
        let rhs = sum_range_if(d, qq, g, x);
        let eqn = d.eq(lhs, rhs);
        let inner = d.arrow(hyp_f, eqn);
        d.arrow(hyp_p, inner)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_p_ty = bounded_pointwise_bool(d, pp, qq, zero);
            let hyp_f_ty = bounded_pointwise_nat(d, f, g, zero);
            let hp_fv = d.fresh_fvar();
            let hf_fv = d.fresh_fvar();
            let zero_v = d.zero();
            let body = d.refl(zero_v);
            let with_hf = d.lam_fv(hf_fv, hyp_f_ty, body);
            d.lam_fv(hp_fv, hyp_p_ty, with_hf)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_p_ty = bounded_pointwise_bool(d, pp, qq, sj);
            let hyp_f_ty = bounded_pointwise_nat(d, f, g, sj);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let hf_fv = d.fresh_fvar();
            let hf = d.kernel().fvar(hf_fv);

            let lt_j_sj = d.lemma(p.lt_succ_self, &[j]);

            // Weaken `hp`/`hf` from bound `succ j` to bound `j`, for the IH.
            let hp_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(p.le_succ, &[j]);
                let lifted = d.lemma(p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(hp, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let hf_lt_j = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hi_ty = d.lt(i, j);
                let hi_fv = d.fresh_fvar();
                let hi = d.kernel().fvar(hi_fv);
                let le_succ_j = d.lemma(p.le_succ, &[j]);
                let lifted = d.lemma(p.lt_of_lt_of_le, &[i, j, sj, hi, le_succ_j]);
                let applied = d.apply(hf, &[i, lifted]);
                let with_hi = d.lam_fv(hi_fv, hi_ty, applied);
                d.lam_fv(i_fv, nat, with_hi)
            };
            let sub_ih = d.apply(ih, &[hp_lt_j, hf_lt_j]);

            let hp_j = d.apply(hp, &[j, lt_j_sj]);
            let hf_j = d.apply(hf, &[j, lt_j_sj]);

            let f_prior = sum_range_if(d, pp, f, j);
            let g_prior = sum_range_if(d, qq, g, j);
            let pj = d.apply(pp, &[j]);
            let qj = d.apply(qq, &[j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let zero = d.zero();
            let f_sel = d.bool_select_nat(pj, fj, zero);
            let g_sel = d.bool_select_nat(qj, gj, zero);

            let start = d.add(f_prior, f_sel);
            let mid = d.add(g_prior, f_sel);
            let h1 = d.congr(f_prior, g_prior, sub_ih, &|d, t| d.add(t, f_sel));

            let h_sel = bool_select_congr(d, pj, qj, hp_j, fj, gj, hf_j);
            let end_ = d.add(g_prior, g_sel);
            let h2 = d.congr(f_sel, g_sel, h_sel, &|d, t| d.add(g_prior, t));

            let (_e, body) = d.chain(start, &[(mid, h1), (end_, h2)]);

            let with_hf = d.lam_fv(hf_fv, hyp_f_ty, body);
            d.lam_fv(hp_fv, hyp_p_ty, with_hf)
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_g = d.pi_fv(g_fv, fn_ty, with_n);
        let with_f = d.pi_fv(f_fv, fn_ty, with_g);
        let with_qq = d.pi_fv(qq_fv, pred_ty, with_f);
        d.pi_fv(pp_fv, pred_ty, with_qq)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_g = d.lam_fv(g_fv, fn_ty, with_n);
        let with_f = d.lam_fv(f_fv, fn_ty, with_g);
        let with_qq = d.lam_fv(qq_fv, pred_ty, with_f);
        d.lam_fv(pp_fv, pred_ty, with_qq)
    };
    d.declare_theorem(p.sum_range_if_congr_lt, ty, value)
}

// ============================================================================
// `Nat.sumRangeIf_compl` — the split.
// ============================================================================

/// `b : Bool`, `v : Nat ⊢ Eq Nat (add (bool_select_nat b v 0)
/// (bool_select_nat (compl b) v 0)) v`, where `compl b := if b then false
/// else true` — the per-index fact the split's step needs.
///
/// A single `Bool.rec` on `b`, with `v` staying free:
///
/// - `b = true`: `compl true ≡ false`, so the sum is `v + 0`, and `Nat.add`
///   recurses on its RIGHT argument, so that IS `v` — `Eq.refl`.
/// - `b = false`: `compl false ≡ true`, so the sum is `0 + v`, which does
///   NOT reduce (`add zero v` is stuck on a free `v`) — closed by
///   `Nat.zero_add`.
///
/// The asymmetry is the whole reason `finite_set.rs`'s `compl_sum_eq` gets
/// two bare `Eq.refl`s and this one does not: there both branches select
/// between the CLOSED numerals `1`/`0`, so both sides collapse to `1`; here
/// one branch selects the free `v`.
fn compl_select_sum_eq(d: &mut NatDev<'_>, p: &NatPrelude, b: ExprId, v: ExprId) -> ExprId {
    let p_ = *p;
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let compl_x = bool_select_bool(d, &p_, x, false_, true_);
        let zero_x = d.zero();
        let sel_x = d.bool_select_nat(x, v, zero_x);
        let zero_c = d.zero();
        let sel_compl = d.bool_select_nat(compl_x, v, zero_c);
        let lhs = d.add(sel_x, sel_compl);
        let stmt = d.eq(lhs, v);
        d.lam_fv(x_fv, bool_ty, stmt)
    };
    let case_false = d.lemma(p_.zero_add, &[v]);
    let case_true = d.refl(v);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p_.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Nat.sumRangeIf_compl : ∀ p f n, Eq Nat (add (sumRangeIf p f n)
/// (sumRangeIf (setCompl p) f n)) (sumRange f n)`.
///
/// The additive twin of `Nat.countRange_compl` (`finite_set.rs`), and its
/// proof is that proof with `1`/`0` selection replaced by `f j`/`0`:
/// induction on `n`; at the step, [`add_regroup_four`] moves the two new top
/// terms together, the IH rewrites the two folds, and
/// [`compl_select_sum_eq`] collapses the pair of new terms to `f j`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
fn declare_sum_range_if_compl(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let compl_pred = d.const_app(p.set_compl, &[pred]);

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let a_ = sum_range_if(d, pred, f, x);
        let b_ = sum_range_if(d, compl_pred, f, x);
        let lhs = d.add(a_, b_);
        let rhs = d.sum_range(f, x);
        d.eq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            d.refl(zero)
        },
        &|d, j, ih| {
            let a_ = sum_range_if(d, pred, f, j);
            let b_ = sum_range_if(d, compl_pred, f, j);
            let pj = d.apply(pred, &[j]);
            let fj = d.apply(f, &[j]);
            let zero = d.zero();
            let sel_p = d.bool_select_nat(pj, fj, zero);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let compl_pj = bool_select_bool(d, &p, pj, false_, true_);
            let zero_c = d.zero();
            let sel_c = d.bool_select_nat(compl_pj, fj, zero_c);

            let start = {
                let l = d.add(a_, sel_p);
                let r = d.add(b_, sel_c);
                d.add(l, r)
            };
            let ab = d.add(a_, b_);
            let sel_pair = d.add(sel_p, sel_c);
            let mid1 = d.add(ab, sel_pair);
            let h_a = add_regroup_four(d, &p, a_, sel_p, b_, sel_c);

            let sum_j = d.sum_range(f, j);
            let mid2 = d.add(sum_j, sel_pair);
            let h_b = d.congr(ab, sum_j, ih, &|d, t| d.add(t, sel_pair));

            let sel_eq = compl_select_sum_eq(d, &p, pj, fj);
            let target = d.add(sum_j, fj);
            let h_c = d.congr(sel_pair, fj, sel_eq, &|d, t| d.add(sum_j, t));

            let (_end, proof) = d.chain(start, &[(mid1, h_a), (mid2, h_b), (target, h_c)]);
            proof
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_f = d.pi_fv(f_fv, fn_ty, with_n);
        d.pi_fv(pred_fv, pred_ty, with_f)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        let with_f = d.lam_fv(f_fv, fn_ty, with_n);
        d.lam_fv(pred_fv, pred_ty, with_f)
    };
    d.declare_theorem(p.sum_range_if_compl, ty, value)
}

/// Declare `Nat.sumRangeIf`, its two defining equations, its bounded
/// congruence, and the complement split.
///
/// Must run after `Nat.sumRange` (`defs.rs`), `Nat.setCompl`
/// (`finite_set.rs`), and the `Nat.add` order/associativity lemmas.
///
/// # Errors
///
/// Returns the trusted gate's rejection for the first declaration that does
/// not type-check.
pub(super) fn declare_subset_sum_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_if(d, p)?;
    declare_sum_range_if_defining_equations(d, p)?;
    declare_sum_range_if_congr_lt(d, p)?;
    declare_sum_range_if_compl(d, p)?;
    Ok(())
}
