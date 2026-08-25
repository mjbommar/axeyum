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
use super::finite::{ex_falso, select_nat_false, select_nat_true};
use super::helpers::{and_left, and_right};
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

// ============================================================================
// The predicate-scoped pigeonhole: `Nat.injectiveOnP` / `Nat.mapsIntoP` /
// `Nat.surjectiveOnP` / `Nat.injective_on_p_imp_surjective_on_p`.
// ============================================================================
//
// `finite.rs`'s `InjectiveOn`/`MapsInto`/`SurjectiveOn` are self-maps of the
// WHOLE contiguous range `[0,n)`. The predicate-scoped forms below restrict
// every quantifier to the `p`-subset `S := {i < n : p i = true}`, matching
// `Nat.prodRangeIf`'s and `Nat.countRange`'s own convention (`p : Nat →
// Bool`, selection via `bool_select_nat`, never a `Prop`-level predicate):
//
// - `Nat.injectiveOnP p f n := ∀ i j, i<n → j<n → p i=true → p j=true →
//   f i=f j → i=j`.
// - `Nat.mapsIntoP p f n := ∀ i, i<n → p i=true → f i<n ∧ p (f i)=true` —
//   the SELF-map hypothesis: `f` sends `S` into `S`, not merely into
//   `[0,n)`.
// - `Nat.surjectiveOnP p f n := ∀ k, k<n → p k=true → ∃ i, i<n ∧ p i=true
//   ∧ f i=k`.
//
// ## The route: reduce to the full-range pigeonhole, don't re-derive it
//
// `Nat.injective_on_p_imp_surjective_on_p` does NOT induct on `n` again —
// unlike [`super::finite::declare_pigeonhole`], which inducts because it has
// no smaller self-map to fall back on. Here one already exists: extend `f`
// to a full self-map of `[0,n)` by fixing every point outside `S`,
//
//     f' i := bool_select_nat (p i) (f i) i,
//
// and hand `f'` directly to [`NatPrelude::injective_on_imp_surjective_on`]
// (`finite.rs`), UNMODIFIED. `f'` is injective on the whole range (two
// points both outside `S` are fixed, hence distinguished by themselves; a
// point in `S` and a point outside `S` can never collide, because
// `MapsIntoP` keeps every `S`-image inside `S` and a point outside `S` is
// (by definition of `S`) not there) and maps `[0,n)` into itself outright
// (an `S`-point's image stays `< n` by `MapsIntoP`; every other point is
// fixed). So the EXISTING pigeonhole applies with no new induction.
//
// Reading an `S`-witness back out of `f'`'s full-range surjectivity is the
// only place `p` needs to be consulted again: the pigeonhole witness `i0`
// with `f' i0 = k` might, in principle, be a point `f'` merely FIXED
// (`i0 = k`, `i0 ∉ S`) rather than a genuine `f`-image. That case is ruled
// out because the target `k` is itself `p`-true — if `i0 = k` then
// `p i0 = p k = true`, contradicting `i0 ∉ S` — so the witness `f'` hands
// back is always the real thing.
//
// This sidesteps the diary's recorded obstruction for
// `Nat.prodRangeIf_permute` (the pigeonhole witness need not land at the TOP
// of the range, forcing an arbitrary-position swap lemma) entirely: there is
// no re-indexing step here, because `f'` is already a full self-map and the
// unmodified full-range pigeonhole is applied to it directly, not
// re-derived by peeling one element off the top of a fold.

/// Case-split on `cond : Bool` for a `goal` that does not depend on which
/// branch is taken, with `heq : Eq Bool cond true`/`Eq Bool cond false`
/// available inside the matching branch — the "generalize the selector, then
/// instantiate at `bool_refl(condition)`" trick `finite.rs::compact_eq_of_gt`
/// already uses (three other files import it under the same name), narrowed
/// to a directly reusable two-branch form: every call site below needs BOTH
/// cases and needs the resulting `Bool` equation itself, not just the
/// reduced value `compact_eq_of_gt` produces for its one fixed goal.
fn bool_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    goal: ExprId,
    case_true: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    case_false: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let bool_ty = d.bool_ty();
    let true_val = d.bool_true();
    let false_val = d.bool_false();

    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        let heq = d.kernel().fvar(heq_fv);
        let body = case_false(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, true_val);
        let heq = d.kernel().fvar(heq_fv);
        let body = case_true(d, heq);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let eq_cond_sel = d.bool_eq(cond, sel);
        let body = d.arrow(eq_cond_sel, goal);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)` — [`NatOps::congr`]'s conclusion
/// specialized to a `Bool`-valued `f`. [`NatOps::congr`] itself always
/// closes into `Eq Nat`, hardcoded internally (it calls the Nat-only
/// [`NatOps::eq`]/[`NatOps::refl`] to BUILD the conclusion, even though the
/// hypothesis-side machinery it shares with this — [`NatOps::eq_motive`] and
/// [`NatOps::transport`], both keyed to the Nat-typed HYPOTHESIS `h`, not the
/// conclusion's sort — is not), so it cannot be reused directly for a
/// `Nat → Bool` function like `pred`; this mirrors its definition with the
/// conclusion built through `bool_eq`/`bool_refl` instead.
fn congr_to_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// `f' := fun i => bool_select_nat (p i) (f i) i` — the identity-outside-`S`
/// extension of `f` (restricted to the `p`-subset `S`) to a full self-map of
/// `[0,n)`. See the module doc above.
fn extend_id(d: &mut NatDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let sel = d.bool_select_nat(pi, fi, i);
    d.lam_fv(i_fv, nat, sel)
}

/// Declare `Nat.injectiveOnP`, `Nat.mapsIntoP`, `Nat.surjectiveOnP` — the
/// `p`-subset-scoped analogues of `finite.rs`'s
/// `InjectiveOn`/`MapsInto`/`SurjectiveOn` (see the module doc above for the
/// statements).
///
/// # Errors
///
/// Returns the kernel's rejection if any generated definition does not
/// type-check or a name is already taken.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_injective_surjective_p(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();
    let true_v = d.bool_true();

    // injectiveOnP pred f n := ∀ i j, i<n → j<n → pred i=true → pred j=true
    //   → f i=f j → i=j.
    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let pi = d.apply(pred, &[i]);
        let pj = d.apply(pred, &[j]);
        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);

        let concl = d.eq(i, j);
        let hyp_feq = d.eq(fi, fj);
        let step_feq = d.arrow(hyp_feq, concl);
        let hyp_pj = d.bool_eq(pj, true_v);
        let step_pj = d.arrow(hyp_pj, step_feq);
        let hyp_pi = d.bool_eq(pi, true_v);
        let step_pi = d.arrow(hyp_pi, step_pj);
        let hyp_j = d.lt(j, n);
        let step_j = d.arrow(hyp_j, step_pi);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_j);
        let body = {
            let with_j = d.pi_fv(j_fv, nat, inner);
            d.pi_fv(i_fv, nat, with_j)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_f = d.lam_fv(f_fv, fn_ty, with_n);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            let over_f = d.arrow(fn_ty, over_n);
            d.arrow(pred_ty, over_f)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.injective_on_p,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // mapsIntoP pred f n := ∀ i, i<n → pred i=true → f i<n ∧ pred (f i)=true.
    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);

        let pi = d.apply(pred, &[i]);
        let fi = d.apply(f, &[i]);
        let pfi = d.apply(pred, &[fi]);

        let in_range = d.lt(fi, n);
        let stays_p = d.bool_eq(pfi, true_v);
        let concl = d.const_app(logic.and, &[in_range, stays_p]);
        let hyp_pi = d.bool_eq(pi, true_v);
        let step_pi = d.arrow(hyp_pi, concl);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_pi);
        let body = d.pi_fv(i_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_f = d.lam_fv(f_fv, fn_ty, with_n);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            let over_f = d.arrow(fn_ty, over_n);
            d.arrow(pred_ty, over_f)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.maps_into_p,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // surjectiveOnP pred f n := ∀ k, k<n → pred k=true →
    //   ∃ i, i<n ∧ pred i=true ∧ f i=k.
    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let one = d.level_one();
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.lt(i, n);
            let pi = d.apply(pred, &[i]);
            let stays_p = d.bool_eq(pi, true_v);
            let fi = d.apply(f, &[i]);
            let eqk = d.eq(fi, k);
            let inner_and = d.const_app(logic.and, &[stays_p, eqk]);
            let body = d.const_app(logic.and, &[bound, inner_and]);
            d.lam_fv(i_fv, nat, body)
        };
        let exists_ty = {
            let e = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(e, &[nat, predicate])
        };
        let pk = d.apply(pred, &[k]);
        let hyp_pk = d.bool_eq(pk, true_v);
        let step_pk = d.arrow(hyp_pk, exists_ty);
        let hyp_k = d.lt(k, n);
        let inner = d.arrow(hyp_k, step_pk);
        let body = d.pi_fv(k_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            let with_f = d.lam_fv(f_fv, fn_ty, with_n);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            let over_f = d.arrow(fn_ty, over_n);
            d.arrow(pred_ty, over_f)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.surjective_on_p,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

/// Declare `Nat.injective_on_p_imp_surjective_on_p` — the predicate-scoped
/// pigeonhole. See the module doc above for the route (reduce to the
/// full-range pigeonhole via the identity-outside-`S` extension; no new
/// induction).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_pigeonhole_p(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, nat);
    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let one = d.level_one();

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inj_p_ty = d.const_app(p.injective_on_p, &[pred, f, n]);
    let maps_p_ty = d.const_app(p.maps_into_p, &[pred, f, n]);
    let surj_p_ty = d.const_app(p.surjective_on_p, &[pred, f, n]);

    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);

    let fprime = extend_id(d, pred, f);

    // --- InjectiveOn f' n, from InjectiveOnP + MapsIntoP -------------------
    let inj_full = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);

        let pi = d.apply(pred, &[i]);
        let pj = d.apply(pred, &[j]);
        let fi = d.apply(f, &[i]);
        let fj = d.apply(f, &[j]);
        let sel_i = d.bool_select_nat(pi, fi, i);
        let sel_j = d.bool_select_nat(pj, fj, j);
        let heq_ty = d.eq(sel_i, sel_j);
        let target = d.eq(i, j);

        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let body = bool_case(
            d,
            &p,
            pi,
            target,
            &|d: &mut NatDev<'_>, hpi: ExprId| -> ExprId {
                let st_i = select_nat_true(d, pi, fi, i, hpi);
                bool_case(
                    d,
                    &p,
                    pj,
                    target,
                    &|d: &mut NatDev<'_>, hpj: ExprId| -> ExprId {
                        // p i = true, p j = true: fi = sel_i = sel_j = fj.
                        let st_j = select_nat_true(d, pj, fj, j, hpj);
                        let fi_eq_sel_i = d.symm(sel_i, fi, st_i);
                        let (_e, fi_eq_fj) =
                            d.chain(fi, &[(sel_i, fi_eq_sel_i), (sel_j, heq), (fj, st_j)]);
                        d.apply(inj, &[i, j, hi, hj, hpi, hpj, fi_eq_fj])
                    },
                    &|d: &mut NatDev<'_>, hpj: ExprId| -> ExprId {
                        // p i = true, p j = false: fi = sel_i = sel_j = j,
                        // so p j = p (f i) = true (MapsIntoP at i),
                        // contradicting hpj.
                        let sf_j = select_nat_false(d, pj, fj, j, hpj);
                        let fi_eq_sel_i = d.symm(sel_i, fi, st_i);
                        let (_e, fi_eq_j) =
                            d.chain(fi, &[(sel_i, fi_eq_sel_i), (sel_j, heq), (j, sf_j)]);
                        let maps_at_i = d.apply(maps, &[i, hi, hpi]);
                        let fi_lt_n = d.lt(fi, n);
                        let pred_fi = d.apply(pred, &[fi]);
                        let pfi_true_ty = d.bool_eq(pred_fi, true_v);
                        let pfi_true = and_right(d, fi_lt_n, pfi_true_ty, maps_at_i);
                        let congr_pred =
                            congr_to_bool(d, fi, j, fi_eq_j, &|d, x| d.apply(pred, &[x]));
                        let pj_true = {
                            let pj_eq_pfi = d.bool_symm(pred_fi, pj, congr_pred);
                            d.bool_trans(pj, pred_fi, true_v, pj_eq_pfi, pfi_true)
                        };
                        let combined = {
                            let true_eq_pj = d.bool_symm(pj, true_v, pj_true);
                            d.bool_trans(true_v, pj, false_v, true_eq_pj, hpj)
                        };
                        let bool_true_ne_false =
                            d.kernel().const_(logic.bool_true_ne_false, vec![]);
                        let false_pf = d.apply(bool_true_ne_false, &[combined]);
                        ex_falso(d, &p, target, false_pf)
                    },
                )
            },
            &|d: &mut NatDev<'_>, hpi: ExprId| -> ExprId {
                let sf_i = select_nat_false(d, pi, fi, i, hpi);
                bool_case(
                    d,
                    &p,
                    pj,
                    target,
                    &|d: &mut NatDev<'_>, hpj: ExprId| -> ExprId {
                        // p i = false, p j = true: i = sel_i = sel_j = fj,
                        // so p i = p (f j) = true (MapsIntoP at j),
                        // contradicting hpi.
                        let st_j = select_nat_true(d, pj, fj, j, hpj);
                        let i_eq_sel_i = d.symm(sel_i, i, sf_i);
                        let (_e, i_eq_fj) =
                            d.chain(i, &[(sel_i, i_eq_sel_i), (sel_j, heq), (fj, st_j)]);
                        let maps_at_j = d.apply(maps, &[j, hj, hpj]);
                        let fj_lt_n = d.lt(fj, n);
                        let pred_fj = d.apply(pred, &[fj]);
                        let pfj_true_ty = d.bool_eq(pred_fj, true_v);
                        let pfj_true = and_right(d, fj_lt_n, pfj_true_ty, maps_at_j);
                        let congr_pred =
                            congr_to_bool(d, i, fj, i_eq_fj, &|d, x| d.apply(pred, &[x]));
                        let pi_true = d.bool_trans(pi, pred_fj, true_v, congr_pred, pfj_true);
                        let combined = {
                            let true_eq_pi = d.bool_symm(pi, true_v, pi_true);
                            d.bool_trans(true_v, pi, false_v, true_eq_pi, hpi)
                        };
                        let bool_true_ne_false =
                            d.kernel().const_(logic.bool_true_ne_false, vec![]);
                        let false_pf = d.apply(bool_true_ne_false, &[combined]);
                        ex_falso(d, &p, target, false_pf)
                    },
                    &|d: &mut NatDev<'_>, hpj: ExprId| -> ExprId {
                        // p i = false, p j = false: i = sel_i = sel_j = j.
                        let sf_j = select_nat_false(d, pj, fj, j, hpj);
                        let i_eq_sel_i = d.symm(sel_i, i, sf_i);
                        let (_e, i_eq_j) =
                            d.chain(i, &[(sel_i, i_eq_sel_i), (sel_j, heq), (j, sf_j)]);
                        i_eq_j
                    },
                )
            },
        );

        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let lt_j_n = d.lt(j, n);
        let with_hj = d.lam_fv(hj_fv, lt_j_n, with_heq);
        let lt_i_n = d.lt(i, n);
        let with_hi = d.lam_fv(hi_fv, lt_i_n, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // --- MapsInto f' n, from MapsIntoP --------------------------------------
    let maps_full = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        let pi = d.apply(pred, &[i]);
        let fi = d.apply(f, &[i]);
        let sel_i = d.bool_select_nat(pi, fi, i);
        let target = d.lt(sel_i, n);

        let body = bool_case(
            d,
            &p,
            pi,
            target,
            &|d: &mut NatDev<'_>, hpi: ExprId| -> ExprId {
                let st_i = select_nat_true(d, pi, fi, i, hpi);
                let maps_at_i = d.apply(maps, &[i, hi, hpi]);
                let fi_lt_n_ty = d.lt(fi, n);
                let pred_fi = d.apply(pred, &[fi]);
                let pfi_true_ty = d.bool_eq(pred_fi, true_v);
                let fi_lt_n = and_left(d, fi_lt_n_ty, pfi_true_ty, maps_at_i);
                let motive = d.eq_motive(fi, &|d, x| d.lt(x, n));
                let fi_eq_sel_i = d.symm(sel_i, fi, st_i);
                d.transport(fi, motive, fi_lt_n, sel_i, fi_eq_sel_i)
            },
            &|d: &mut NatDev<'_>, hpi: ExprId| -> ExprId {
                let sf_i = select_nat_false(d, pi, fi, i, hpi);
                let motive = d.eq_motive(i, &|d, x| d.lt(x, n));
                let i_eq_sel_i = d.symm(sel_i, i, sf_i);
                d.transport(i, motive, hi, sel_i, i_eq_sel_i)
            },
        );
        let lt_i_n = d.lt(i, n);
        let with_hi = d.lam_fv(hi_fv, lt_i_n, body);
        d.lam_fv(i_fv, nat, with_hi)
    };

    // --- Apply the (unmodified) full-range pigeonhole to f' ----------------
    // `Nat.injective_on_imp_surjective_on : ∀ n f, InjectiveOn f n →
    // MapsInto f n → SurjectiveOn f n` — `n` is quantified OUTSIDE `f`
    // (`finite.rs::declare_pigeonhole` builds it via `d.theorem(name, 1,
    // ...)`, so the single `Nat`-typed top argument is `n`, and `f` is
    // quantified inside `pigeonhole_motive`), so `n` comes first here.
    let surj_full = d.lemma(
        p.injective_on_imp_surjective_on,
        &[n, fprime, inj_full, maps_full],
    );

    // --- Read a genuine `S`-witness back out ---------------------------
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hk_fv = d.fresh_fvar();
    let hk = d.kernel().fvar(hk_fv);
    let hpk_fv = d.fresh_fvar();
    let hpk = d.kernel().fvar(hpk_fv);

    let pk = d.apply(pred, &[k]);

    // SurjectiveOnP's own witness type for this `k`.
    let target_predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, n);
        let pi = d.apply(pred, &[i]);
        let stays_p = d.bool_eq(pi, true_v);
        let fi = d.apply(f, &[i]);
        let eqk = d.eq(fi, k);
        let inner_and = d.const_app(logic.and, &[stays_p, eqk]);
        let body = d.const_app(logic.and, &[bound, inner_and]);
        d.lam_fv(i_fv, nat, body)
    };
    let target = {
        let e = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(e, &[nat, target_predicate])
    };

    // The full-range `SurjectiveOn f' n`'s own witness predicate at `k`.
    let full_predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, n);
        let fpi = d.apply(fprime, &[i]);
        let eqk = d.eq(fpi, k);
        let body = d.const_app(logic.and, &[bound, eqk]);
        d.lam_fv(i_fv, nat, body)
    };
    let full_exists_ty = {
        let e = d.kernel().const_(logic.exists_, vec![one]);
        d.apply(e, &[nat, full_predicate])
    };

    let witness = d.apply(surj_full, &[k, hk]);

    let minor = {
        let i0_fv = d.fresh_fvar();
        let i0 = d.kernel().fvar(i0_fv);
        let hand_fv = d.fresh_fvar();
        let hand = d.kernel().fvar(hand_fv);

        let pi0 = d.apply(pred, &[i0]);
        let fi0 = d.apply(f, &[i0]);
        let sel_i0 = d.bool_select_nat(pi0, fi0, i0);

        let hi0_ty = d.lt(i0, n);
        let heq0_ty = d.eq(sel_i0, k);
        let hand_ty = d.const_app(logic.and, &[hi0_ty, heq0_ty]);

        let hi0 = and_left(d, hi0_ty, heq0_ty, hand);
        let heq0 = and_right(d, hi0_ty, heq0_ty, hand);

        let body = bool_case(
            d,
            &p,
            pi0,
            target,
            &|d: &mut NatDev<'_>, hpi0: ExprId| -> ExprId {
                // Genuine witness: p i0 = true.
                let st_i0 = select_nat_true(d, pi0, fi0, i0, hpi0);
                let sel_eq_fi0 = d.symm(sel_i0, fi0, st_i0);
                let (_e, fi0_eq_k) = d.chain(fi0, &[(sel_i0, sel_eq_fi0), (k, heq0)]);
                let stays_p_ty = d.bool_eq(pi0, true_v);
                let eqk_ty = d.eq(fi0, k);
                let inner_and = d.const_app(logic.and_intro, &[stays_p_ty, eqk_ty, hpi0, fi0_eq_k]);
                let inner_and_ty = d.const_app(logic.and, &[stays_p_ty, eqk_ty]);
                let full_and =
                    d.const_app(logic.and_intro, &[hi0_ty, inner_and_ty, hi0, inner_and]);
                let exists_intro = d.kernel().const_(logic.exists_intro, vec![one]);
                d.apply(exists_intro, &[nat, target_predicate, i0, full_and])
            },
            &|d: &mut NatDev<'_>, hpi0: ExprId| -> ExprId {
                // Spurious fixed point: p i0 = false, but i0 = k and p k = true.
                let sf_i0 = select_nat_false(d, pi0, fi0, i0, hpi0);
                let i0_eq_sel_i0 = d.symm(sel_i0, i0, sf_i0);
                let (_e, i0_eq_k) = d.chain(i0, &[(sel_i0, i0_eq_sel_i0), (k, heq0)]);
                let congr_pred = congr_to_bool(d, i0, k, i0_eq_k, &|d, x| d.apply(pred, &[x]));
                let pi0_true = d.bool_trans(pi0, pk, true_v, congr_pred, hpk);
                let combined = {
                    let true_eq_pi0 = d.bool_symm(pi0, true_v, pi0_true);
                    d.bool_trans(true_v, pi0, false_v, true_eq_pi0, hpi0)
                };
                let bool_true_ne_false = d.kernel().const_(logic.bool_true_ne_false, vec![]);
                let false_pf = d.apply(bool_true_ne_false, &[combined]);
                ex_falso(d, &p, target, false_pf)
            },
        );

        let with_hand = d.lam_fv(hand_fv, hand_ty, body);
        d.lam_fv(i0_fv, nat, with_hand)
    };

    let surj_p_body_at_k = {
        let motive = {
            let w_fv = d.fresh_fvar();
            d.lam_fv(w_fv, full_exists_ty, target)
        };
        let exists_rec = d.kernel().const_(logic.exists_rec, vec![one]);
        d.apply(exists_rec, &[nat, full_predicate, motive, minor, witness])
    };

    let surj_p_full = {
        let pk_true_ty = d.bool_eq(pk, true_v);
        let with_hpk = d.lam_fv(hpk_fv, pk_true_ty, surj_p_body_at_k);
        let lt_k_n = d.lt(k, n);
        let with_hk = d.lam_fv(hk_fv, lt_k_n, with_hpk);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let with_maps = d.lam_fv(maps_fv, maps_p_ty, surj_p_full);
    let with_inj = d.lam_fv(inj_fv, inj_p_ty, with_maps);
    let with_n = d.lam_fv(n_fv, nat, with_inj);
    let with_f = d.lam_fv(f_fv, fn_ty, with_n);
    let value = d.lam_fv(pred_fv, pred_ty, with_f);

    let ty = {
        let inner = d.arrow(maps_p_ty, surj_p_ty);
        let with_maps_arrow = d.arrow(inj_p_ty, inner);
        let with_n = d.pi_fv(n_fv, nat, with_maps_arrow);
        let with_f = d.pi_fv(f_fv, fn_ty, with_n);
        d.pi_fv(pred_fv, pred_ty, with_f)
    };

    d.declare_theorem(p.injective_on_p_imp_surjective_on_p, ty, value)
}

/// Declare the predicate-scoped pigeonhole: `Nat.injectiveOnP`,
/// `Nat.mapsIntoP`, `Nat.surjectiveOnP`, and
/// `Nat.injective_on_p_imp_surjective_on_p`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_pigeonhole_p_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_injective_surjective_p(d, p)?;
    declare_pigeonhole_p(d, p)?;
    Ok(())
}
