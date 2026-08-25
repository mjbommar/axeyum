//! `Nat.prodRangeIf` — the product side of `Nat.countRange`'s pattern: a
//! fold restricted to a *predicate-defined subset* of `[0,n)`, rather than
//! the full contiguous range `Nat.prodRange` already folds over.
//!
//! ## Why this exists
//!
//! Seven independent lanes stopped at the same absence: the standard proofs
//! of Euler's totient theorem, uniqueness of prime factorization, general-`n`
//! CRT, and permutations-as-group-elements all need a product over the
//! *subset* of `[0,n)` satisfying some `Bool`-valued predicate (residues
//! coprime to `n`, prime factors, …), not a product over every index. This
//! kernel already has `Nat.prodRange f n` (product over the full range,
//! `factorization.rs`) and `Nat.countRange p n` (COUNT over a predicate
//! subset, `totient.rs`) — the sum/count side of this pattern already
//! exists, the product side did not.
//!
//! ## The predicate convention, copied verbatim from `Nat.countRange`
//!
//! `totient.rs`'s `Nat.countRange` fixes the convention this file must match
//! to compose with it: **the predicate is `Bool`-valued** (`p : Nat → Bool`),
//! never `Prop`-valued, decided by whatever computation produced it (e.g.
//! `Nat.beq (Nat.gcd k n) 1` for "coprime to `n`"). Selection between the two
//! outcomes goes through [`NatOps::bool_select_nat`] — `Bool.rec` at `Nat`,
//! the *computational* if/then/else — never through a `Prop`-level case
//! split. This module reuses `bool_select_nat` at the SAME two branches
//! `countRange` does (`1`/`0` there for the count; `f i`/`1` here for the
//! product, `1` being the multiplicative identity in the "not in the subset"
//! case, exactly as `0` is the additive identity there).
//!
//! ## Definition: reuse `Nat.prodRange`, don't re-derive `Nat.rec`
//!
//! `Nat.prodRangeIf p f n := Nat.prodRange (fun i => bool_select_nat (p i)
//! (f i) 1) n` — i.e. **not** a fresh structural recursion, but the same
//! device `Nat.totient` already uses over `Nat.countRange` (`totient.rs`):
//! delegate to the already-declared fold with a selector function absorbing
//! the predicate. This keeps [`declare_prod_range_if_defining_equations`]'s
//! two equations pure `Eq.refl` (delta into `prodRangeIf`, then delta+iota
//! into `prodRange`'s own `Nat.rec`, exactly as `prodRange_zero`/`_succ`
//! themselves close) with no separate recursor and no risk of the two folds
//! disagreeing on the selection convention.
//!
//! ## What's declared
//!
//! - [`declare_prod_range_if`][]: `Nat.prodRangeIf`, the definition above.
//! - [`declare_prod_range_if_defining_equations`][]: `Nat.prodRangeIf_zero`
//!   (`prodRangeIf p f 0 = 1`) and `Nat.prodRangeIf_succ` (`prodRangeIf p f
//!   (succ n) = mul (prodRangeIf p f n) (bool_select_nat (p n) (f n) 1)`).
//! - [`declare_prod_range_if_congr_lt`][]: `Nat.prodRangeIf_congr_lt` — `p`/`f`
//!   agreeing pointwise with `q`/`g` on every index `< n` gives equal
//!   products. **Bounded** (`Lt i n`), matching `sum_range_congr_lt`'s
//!   convention (`binomial.rs`) rather than `countRange_congr`'s
//!   unconditional one: a predicate or function built from a partial
//!   operator (e.g. truncated subtraction, as several downstream subset
//!   constructions need) typically only agrees pointwise *within* the range,
//!   not everywhere.
//!
//! Concrete computation is checked directly in `nat_prelude_tests.rs`
//! (`prod_range_if_computes_on_small_numerals`): `prodRangeIf 6 (fun i => i
//! is odd) id` reduces to `15` (`1·3·5`), `prodRangeIf 6 (fun _ => true)
//! succ` reduces to `720` (`1·2·3·4·5·6`).
//!
//! ## What does NOT land here — permutation invariance
//!
//! The actual blocker (Euler's theorem: multiplication by a unit permutes
//! the coprime-residue subset, so the product is unchanged) needs `σ`
//! bijective on `[0,n)` and `p`-preserving to give `prodRangeIf n p (f∘σ) =
//! prodRangeIf n p f`. That reduces cleanly to a *predicate-free* statement:
//! writing `h i := bool_select_nat (p i) (f i) 1`, `p`-preservation makes the
//! selector for `f∘σ` equal `h∘σ` pointwise, so the whole question is
//! whether `Nat.prodRange (h∘σ) n = Nat.prodRange h n` for `σ` injective and
//! maps-into on `[0,n)` — i.e. **full-range permutation invariance of
//! `Nat.prodRange` itself**, independent of any predicate.
//!
//! That lemma does not exist for `Nat.prodRange`. It DOES exist for
//! `Int.prodRange` (`Int.prodRange_permute`, `int_prelude/prod.rs`), and
//! reading that proof (read-only; `int_prelude/` is out of scope for this
//! slice) is what makes the size of the remaining gap precise rather than
//! guessed. Two things are true at once:
//!
//! - `Nat.restrict_injective`/`Nat.restrict_maps_into`
//!   (`nat_prelude/finite.rs`) — the "pigeonhole gives an index `i0` with `σ
//!   i0 = n`; if `i0 < n`, override `σ` at `i0` with `σ n` and the result is
//!   still injective/maps-into on `[0,n)`" step this kernel's own doc
//!   comments call "remove one element and re-index" — is **already built**,
//!   axiom-free, in this prelude. So is `Nat.injective_on_imp_surjective_on`
//!   (the pigeonhole itself, `finite.rs`). That half of step 3 is NOT the
//!   obstruction, and IS expressible.
//! - The genuinely missing piece is different from what the brief
//!   anticipated: the pigeonhole witness `i0` need not equal `n`, so
//!   `Nat.prodRange (f∘σ) (succ n)`'s `succ`-equation peels off `(f∘σ) n`
//!   from the TOP of the fold, but the value that actually needs to move
//!   there — `(f∘σ) i0 = f (σ i0) = f n` — sits at position `i0`, potentially
//!   deep inside the range. Reconciling the two requires knowing that
//!   swapping the values at TWO arbitrary positions inside a strict
//!   left-to-right `Nat.rec` fold doesn't change the product — a lemma in
//!   its own right (`Int.prodRange_swap`/`Nat.point_swap` in
//!   `int_prelude/prod.rs`/`wilson.rs`, built via an explicit
//!   adjacent-transposition induction, independent of `point_override` and
//!   the restriction lemmas above). **No `Nat`-native counterpart of that
//!   swap lemma exists**, and the `Int` one — by its own doc comment —
//!   "took three drafts to close". Porting it is a same-order-of-magnitude
//!   undertaking to this file's own step 1–2 (`int_prelude/prod.rs`'s swap +
//!   permute machinery spans roughly 650 lines), not a small addition on top
//!   of what's declared here, and it is genuinely EXPRESSIBLE (the `Int`
//!   version is the existence proof) — this is a sizing finding, not a
//!   kernel-limitation finding.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ============================================================================
// `Nat.prodRangeIf`.
// ============================================================================

/// `fun i => bool_select_nat (pred i) (f i) 1`, the selector `Nat.prodRangeIf`
/// folds `Nat.prodRange` over.
fn selector(d: &mut NatDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let one = d.num(1);
    let sel = d.bool_select_nat(pi, fi, one);
    d.lam_fv(i_fv, nat, sel)
}

/// `prodRangeIf(d, p, pred, f, n)`, i.e. `Nat.prodRange (selector pred f) n`.
fn prod_range_if(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId, f: ExprId, n: ExprId) -> ExprId {
    let sel = selector(d, pred, f);
    d.const_app(p.prod_range, &[sel, n])
}

/// `Nat.prodRangeIf : (Nat → Bool) → (Nat → Nat) → Nat → Nat := fun pred f n
///   => Nat.prodRange (fun i => bool_select_nat (pred i) (f i) 1) n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
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

    let body = prod_range_if(d, &p, pred, f, n);

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
        name: p.prod_range_if,
        uparams: vec![],
        ty,
        value,
        // Strictly greater than `prod_range`'s own height (`Regular(2)`,
        // `factorization.rs`), the definition this one calls.
        hint: ReducibilityHint::Regular(3),
    })?;
    Ok(())
}

/// `Nat.prodRangeIf_zero`/`Nat.prodRangeIf_succ`: both hold by `Eq.refl`,
/// delta-unfolding into `Nat.prodRange`'s own `Nat.rec` reduction — mirrors
/// `Nat.prodRange_zero`/`_succ` (`factorization.rs`) one level up.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if_defining_equations(
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
        let lhs = prod_range_if(d, &p, pred, f, zero);
        let one_v = d.num(1);
        let stmt = d.eq(lhs, one_v);
        let proof = d.refl(one_v);
        let ty = {
            let with_f = d.pi_fv(f_fv, fn_ty, stmt);
            d.pi_fv(pred_fv, pred_ty, with_f)
        };
        let value = {
            let with_f = d.lam_fv(f_fv, fn_ty, proof);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        d.declare_theorem(p.prod_range_if_zero, ty, value)?;
    }
    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = prod_range_if(d, &p, pred, f, sn);
        let prior = prod_range_if(d, &p, pred, f, n);
        let pn = d.apply(pred, &[n]);
        let fn_at_n = d.apply(f, &[n]);
        let one = d.num(1);
        let sel = d.bool_select_nat(pn, fn_at_n, one);
        let rhs = d.mul(prior, sel);
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
        d.declare_theorem(p.prod_range_if_succ, ty, value)?;
    }
    Ok(())
}

// ============================================================================
// `Nat.prodRangeIf_congr_lt`.
// ============================================================================

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)` — the `Bool`-hypothesis analogue of
/// [`NatOps::congr`], via [`NatOps::bool_transport`]. A local copy of
/// `totient.rs`'s private helper of the same name and shape (that module may
/// not be edited by this slice — same convention `permutation.rs` already
/// uses for helpers it needs from `transposition.rs`).
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
/// (bool_select_nat p_i f_i 1) (bool_select_nat q_i g_i 1)` — rewrite the
/// selector's `Bool` condition first (via [`bool_congr_nat`]), then its `Nat`
/// payload (via the generic [`NatOps::congr`]), and chain the two.
fn bool_select_congr(
    d: &mut NatDev<'_>,
    p_i: ExprId,
    q_i: ExprId,
    h_pq: ExprId,
    f_i: ExprId,
    g_i: ExprId,
    h_fg: ExprId,
) -> ExprId {
    let one = d.num(1);
    let start = d.bool_select_nat(p_i, f_i, one);
    let mid = d.bool_select_nat(q_i, f_i, one);
    let end_ = d.bool_select_nat(q_i, g_i, one);

    let step1 = bool_congr_nat(d, p_i, q_i, h_pq, &|d, x| d.bool_select_nat(x, f_i, one));
    let step2 = d.congr(f_i, g_i, h_fg, &|d, t| d.bool_select_nat(q_i, t, one));

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

/// `Nat.prodRangeIf_congr_lt : ∀ p q f g n, (∀ i, Lt i n → Eq Bool (p i)
/// (q i)) → (∀ i, Lt i n → Eq Nat (f i) (g i)) → Eq Nat (prodRangeIf p f n)
/// (prodRangeIf q g n)`.
///
/// Induction on `n` with `p, q, f, g` fixed (generalized only over the bound,
/// exactly `sum_range_congr_lt`'s shape, `binomial.rs`): the motive threads
/// BOTH bounded-pointwise hypotheses as hypotheses of the statement at each
/// step, weakened from `Lt i (succ j)` to `Lt i j` via `le_succ` +
/// `lt_of_lt_of_le` for the recursive call, and applied at `i = j` itself
/// (via `lt_succ_self`) to rewrite the new top selector through
/// [`bool_select_congr`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_if_congr_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
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
        let lhs = prod_range_if(d, &p, pp, f, x);
        let rhs = prod_range_if(d, &p, qq, g, x);
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
            let one_v = d.num(1);
            let body = d.refl(one_v);
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

            let f_prior = prod_range_if(d, &p, pp, f, j);
            let g_prior = prod_range_if(d, &p, qq, g, j);
            let pj = d.apply(pp, &[j]);
            let qj = d.apply(qq, &[j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let one = d.num(1);
            let f_sel = d.bool_select_nat(pj, fj, one);
            let g_sel = d.bool_select_nat(qj, gj, one);

            let start = d.mul(f_prior, f_sel);
            let mid = d.mul(g_prior, f_sel);
            let h1 = d.congr(f_prior, g_prior, sub_ih, &|d, t| d.mul(t, f_sel));

            let h_sel = bool_select_congr(d, pj, qj, hp_j, fj, gj, hf_j);
            let end_ = d.mul(g_prior, g_sel);
            let h2 = d.congr(f_sel, g_sel, h_sel, &|d, t| d.mul(g_prior, t));

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
    d.declare_theorem(p.prod_range_if_congr_lt, ty, value)
}

/// Declare `Nat.prodRangeIf`, its two defining equations, and its bounded
/// congruence lemma — everything this slice lands (see the module doc for
/// what does NOT land here, and why).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_prod_range_if(d, p)?;
    declare_prod_range_if_defining_equations(d, p)?;
    declare_prod_range_if_congr_lt(d, p)?;
    Ok(())
}
