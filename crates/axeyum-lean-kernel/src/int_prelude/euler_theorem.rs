//! `Int.prodRangeIf` — the `Int` counterpart of `Nat.prodRangeIf`
//! (`nat_prelude/subset_product.rs`): a product folded over a
//! *predicate-defined subset* of `[0,n)`, delegating to the already-declared
//! `Int.prodRange` with a `bool_select_int`-based selector, exactly as
//! `Nat.prodRangeIf` delegates to `Nat.prodRange`.
//!
//! ## Why `Int`, not `Nat`, for this slice — and a correction to ADR-0716
//!
//! ADR-0716 names Euler's totient theorem as within reach on the grounds
//! that both residue-permutation ingredients (`Int.euler_unit_coprime`,
//! `Int.euler_unit_injective`, `euler_totient.rs`) are landed. Both exist
//! and are correctly stated. But `euler_totient.rs`'s OWN module doc
//! already records, in detail, that the theorem does NOT land there: no
//! product restricted to a predicate-defined subset existed (`prodRangeIf`),
//! and no lemma showed such a product is invariant under a
//! predicate-preserving permutation. `nat_prelude/subset_product.rs` has
//! since landed `Nat.prodRangeIf` (definition, defining equations,
//! `congr_lt`) — but that file's own doc says the permutation-invariance
//! step is STILL missing, and sizes porting it (an adjacent-transposition
//! swap induction) as "same order of magnitude" as the whole file, because
//! **no such lemma exists for `Nat.prodRange` at all**. It DOES exist for
//! `Int.prodRange` (`Int.prodRange_permute`, `prod.rs`, built for Wilson's
//! theorem) — this file cashes that observation in: [`declare_prod_range_if_permute`]
//! gets the hard part for free by working over `Int` instead of porting the
//! swap induction to `Nat`.
//!
//! ## The predicate convention, copied verbatim from `Nat.prodRangeIf`
//!
//! The predicate is `Bool`-valued (`p : Nat → Bool`), selected via
//! `bool_select_int` (`prod.rs`) rather than a `Prop`-level case split, and
//! the "not in the subset" value is `Int.one`, the multiplicative identity
//! — the same convention `Nat.prodRangeIf` uses at `Nat`'s `1`.
//!
//! ## What is declared
//!
//! - [`declare_prod_range_if`] — `Int.prodRangeIf`, mirroring
//!   `Nat.prodRangeIf`'s definition
//!   (`Nat.prodRangeIf p f n := Nat.prodRange (fun i => bool_select_nat (p i)
//!   (f i) 1) n`) with `bool_select_int`/`Int.prodRange`/`Int.one` in place
//!   of `bool_select_nat`/`Nat.prodRange`/`1`.
//! - [`declare_prod_range_if_defining_equations`] — `Int.prodRangeIf_zero`/
//!   `Int.prodRangeIf_succ`, both `Eq.refl` (delta into `prodRangeIf`, then
//!   delta+iota into `Int.prodRange`'s own `Nat.rec`, exactly as
//!   `Nat.prodRangeIf`'s pair does). Following `Nat.prodRangeIf`'s own
//!   precedent (`subset_product.rs::prod_range_if`, its private helper), the
//!   STATED types of every theorem in this file use the unfolded
//!   `Int.prodRange (selector …) n` form directly rather than the
//!   `Int.prodRangeIf` constant — that loses nothing: any consumer applying
//!   `Int.prodRangeIf` gets the same fact by kernel-level delta unfolding at
//!   the point of use, and building every statement in the same shape as
//!   the proof term avoids any defeq bridging inside this file at all.
//! - [`declare_prod_range_if_permute`] — the headline: for `σ : Nat → Nat`
//!   an `InjectiveOn`/`MapsInto` self-map of `[0,n)` that additionally
//!   *preserves the predicate* on that range (`∀ i, Lt i n → Eq Bool
//!   (pred (σ i)) (pred i)` — the hypothesis a subset-restricted permutation
//!   needs and a full-range one does not), `prodRangeIf pred f n =
//!   prodRangeIf pred (f ∘ σ) n`. Proved by ONE call each to
//!   `Int.prodRange_permute` (full-range permutation invariance, already
//!   proved, applied to the UNRESTRICTED selector for `pred`/`f`) and
//!   `Int.prodRange_congr_lt` (bounded pointwise congruence, also already
//!   proved, rewriting the permuted selector's condition from `pred ∘ σ` to
//!   `pred` using the preservation hypothesis pointwise below `n`) —
//!   [`bool_select_int_congr_cond`] bridges the one-index step. No
//!   subset-specific pigeonhole or swap induction is needed anywhere, because
//!   the permutation happens on the FULL range and the predicate only
//!   decides which term contributes.
//!
//! ## What does NOT land here — the precise remaining gap to Euler's theorem
//!
//! Three more pieces, all real work, none of them this permutation lemma:
//!
//! 1. **Bridging `Int.euler_unit_injective`'s bounded-`Int` hypotheses to the
//!    `Nat`-typed self-map [`declare_prod_range_if_permute`] (and
//!    `Int.prodRange_permute` beneath it) actually quantifies over.** The
//!    unit-permutation map is `k ↦ emod (a*k) n : Int`; using it here needs a
//!    `Nat.ofNat`/`Int.natAbs` round trip to a genuine `Nat → Nat` function,
//!    plus re-deriving `Nat.InjectiveOn`/`Nat.MapsInto` in that shape from
//!    `Int.euler_unit_injective`'s `0 ≤ i → i < n → …` hypotheses (which are
//!    about `Int`-sorted `i`, `j`, not `Nat`-sorted indices).
//! 2. **The predicate-preservation hypothesis itself is an IFF, and only one
//!    direction is proved.** `preserve` needs `Eq Bool (coprime (emod (a*k) n)
//!    n) (coprime k n)` for every `k < n`, given `Coprime a n`. `∀ n a k, 0 <
//!    n → Coprime a n → Coprime k n → Coprime (emod (a*k) n) n` is exactly
//!    `Int.euler_unit_coprime` — one direction. The converse ("if the image
//!    is coprime, so was `k`") needs `a`'s own modular inverse `a'`
//!    (available *inside* `euler_unit_coprime`'s own proof via
//!    `Int.modEq_inverse_exists`, but not exposed as a standalone fact)
//!    applied a second time: `emod (a' * emod (a*k) n) n = emod (a'*a*k) n =
//!    emod k n = k` for `k` already in range, so `Coprime (emod (a*k) n) n`
//!    plus `euler_unit_coprime` at `a'` gives `Coprime k n` back.
//! 3. **The final assembly.** `prodRangeIf pred (fun _ => a) n = pow a
//!    (countRange pred n)` (a new induction: `Int.pow`/`Nat.countRange`
//!    stepping together, case-split on `pred n`); pointwise-factoring
//!    `prodRangeIf pred (fun k => a * f k) n = mul (prodRangeIf pred (fun _
//!    => a) n) (prodRangeIf pred f n)` (cheap — `bool_select_int (p i) (a *
//!    f i) 1 = mul (bool_select_int (p i) a 1) (bool_select_int (p i) (f i)
//!    1)` by cases on `p i`, since `1 = mul 1 1`, then `Int.prodRange_mul`
//!    supplies the rest); termwise `ModEq` transport from `emod (a*k) n` back
//!    to `a*k` (`Int.modEq_prodRange`-shaped machinery, `prod.rs`); and
//!    cancellation of `prodRangeIf pred id n` via `Int.modEq_cancel` (needs
//!    that product itself coprime to `n`, a short separate argument: every
//!    factor is coprime to `n` by construction of the predicate, and a
//!    product of things coprime to `n` is coprime to `n`).
//!
//! None of items 1–3 touches `Nat`, so all of it belongs in `int_prelude`.
//! `docs/plan/status/374-euler-theorem.md` has the full handoff.

use super::ops::IntDev;
use super::prod::bool_select_int;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// Local plumbing (per-file local copies, this development's own convention
// — see `nat_prelude/euler.rs`/`int_prelude/modinv.rs`'s doc comments on the
// same choice).
// ============================================================================

/// `fun k => f (g k)` — a local copy of `prod.rs`'s private `compose` (not
/// `pub(super)` there).
fn compose(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun i => bool_select_int (pred i) (f i) Int.one` — the selector
/// `Int.prodRangeIf` folds `Int.prodRange` over, mirroring `Nat.prodRangeIf`'s
/// private `selector` (`nat_prelude/subset_product.rs`).
fn selector(d: &mut IntDev<'_>, pred: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let pi = d.apply(pred, &[i]);
    let fi = d.apply(f, &[i]);
    let one = d.ione();
    let sel = bool_select_int(d, pi, fi, one);
    d.lam_fv(i_fv, nat, sel)
}

/// `Int.prodRange (selector pred f) n` — the unfolded form every statement
/// in this file is built in, matching `Nat.prodRangeIf`'s own precedent (see
/// the module doc).
fn prod_range_if(d: &mut IntDev<'_>, pred: ExprId, f: ExprId, n: ExprId) -> ExprId {
    let p = d.int();
    let sel = selector(d, pred, f);
    d.const_app(p.prod_range, &[sel, n])
}

// ============================================================================
// `Int.prodRangeIf`.
// ============================================================================

/// `Int.prodRangeIf : (Nat → Bool) → (Nat → Int) → Nat → Int := fun pred f n
///   => Int.prodRange (fun i => bool_select_int (pred i) (f i) one) n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, int_ty);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let body = prod_range_if(d, pred, f, n);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_f = d.lam_fv(f_fv, fn_ty, with_n);
        d.lam_fv(pred_fv, pred_ty, with_f)
    };
    let ty = {
        let over_n = d.arrow(nat, int_ty);
        let over_f = d.arrow(fn_ty, over_n);
        d.arrow(pred_ty, over_f)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.prod_range_if,
        uparams: vec![],
        ty,
        value,
        // Strictly greater than `Int.prodRange`'s own height
        // (`PROD_RANGE_HEIGHT = 23`, `prod.rs`), the definition this one
        // calls — matches `Nat.prodRangeIf`'s own `Regular(3)` relative to
        // `Nat.prodRange`'s `Regular(2)`.
        hint: ReducibilityHint::Regular(24),
    })?;
    Ok(())
}

/// `Int.prodRangeIf_zero`/`Int.prodRangeIf_succ`, both `Eq.refl` — mirrors
/// `Nat.prodRangeIf`'s pair
/// (`nat_prelude/subset_product.rs::declare_prod_range_if_defining_equations`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if_defining_equations(
    d: &mut IntDev<'_>,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty = d.arrow(nat, int_ty);

    {
        let pred_fv = d.fresh_fvar();
        let pred = d.kernel().fvar(pred_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = prod_range_if(d, pred, f, zero);
        let one_v = d.ione();
        let stmt = d.ieq(lhs, one_v);
        let proof = d.irefl(one_v);
        let ty = {
            let with_f = d.pi_fv(f_fv, fn_ty, stmt);
            d.pi_fv(pred_fv, pred_ty, with_f)
        };
        let value = {
            let with_f = d.lam_fv(f_fv, fn_ty, proof);
            d.lam_fv(pred_fv, pred_ty, with_f)
        };
        let p = d.int();
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
        let lhs = prod_range_if(d, pred, f, sn);
        let prior = prod_range_if(d, pred, f, n);
        let pn = d.apply(pred, &[n]);
        let fn_at_n = d.apply(f, &[n]);
        let one = d.ione();
        let sel = bool_select_int(d, pn, fn_at_n, one);
        let rhs = d.imul(prior, sel);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);
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
        let p = d.int();
        d.declare_theorem(p.prod_range_if_succ, ty, value)?;
    }
    Ok(())
}

// ============================================================================
// `Int.prodRangeIf_permute`.
// ============================================================================

/// `h : Eq Bool a b ⊢ Eq Int (bool_select_int a x y) (bool_select_int b x y)`
/// — congruence of `bool_select_int` in its `Bool` CONDITION alone, `x`/`y`
/// fixed. Simpler than `Nat.prodRangeIf`'s general `bool_select_congr`
/// (`subset_product.rs`, which also lets the payload change) because
/// [`declare_prod_range_if_permute`] only ever needs the condition to move —
/// the "true" payload is the same `f (σ i)` term on both sides.
///
/// `pub(super)`: reused unchanged by `euler_prod_coprime.rs` to rewrite a
/// `selector`-folded term's condition to a literal once a `Bool` equation is
/// in hand (item 3 of the Fermat -> Euler handoff).
pub(super) fn bool_select_int_congr_cond(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let sel_a = bool_select_int(d, a, x, y);
    let motive = d.bool_eq_motive(a, &|d, v| {
        let sel_v = bool_select_int(d, v, x, y);
        d.ieq(sel_a, sel_v)
    });
    let refl_case = d.irefl(sel_a);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Eq Int (prodRangeIf pred f n) (prodRangeIf pred (f ∘ σ) n)`, in the
/// unfolded form (see the module doc).
fn permute_concl(d: &mut IntDev<'_>, pred: ExprId, f: ExprId, sigma: ExprId, n: ExprId) -> ExprId {
    let f_comp_sigma = compose(d, f, sigma);
    let lhs = prod_range_if(d, pred, f, n);
    let rhs = prod_range_if(d, pred, f_comp_sigma, n);
    d.ieq(lhs, rhs)
}

/// `Int.prodRangeIf_permute :
///   ∀ pred f σ n, Nat.InjectiveOn σ n → Nat.MapsInto σ n →
///     (∀ i, Lt i n → Eq Bool (pred (σ i)) (pred i)) →
///     Eq Int (prodRangeIf pred f n) (prodRangeIf pred (f ∘ σ) n)`
///
/// Not an induction of its own — it reduces to one call each of
/// `Int.prodRange_permute` (full-range permutation invariance, ALREADY
/// proved for `Int.prodRange`, `prod.rs`, at the UNRESTRICTED selector for
/// `pred`/`f`) and `Int.prodRange_congr_lt` (bounded pointwise congruence,
/// also already proved, rewriting the permuted selector's condition from
/// `pred ∘ σ` back to `pred` using the preservation hypothesis pointwise
/// below `n`), bridged by [`bool_select_int_congr_cond`]. See the module doc
/// for why this is cheap over `Int` and is NOT (the swap induction is
/// undone) over `Nat`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_if_permute(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let pred_ty = d.arrow(nat, bool_ty);
    let fn_ty_int = d.arrow(nat, int_ty);
    let fn_ty_nat = d.arrow(nat, nat);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, n]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, n]);
    let preserve_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = d.lt(i, n);
        let pred_sigma_i = {
            let si = d.apply(sigma, &[i]);
            d.apply(pred, &[si])
        };
        let pred_i = d.apply(pred, &[i]);
        let eqn = d.bool_eq(pred_sigma_i, pred_i);
        let body = d.arrow(hyp, eqn);
        d.pi_fv(i_fv, nat, body)
    };

    let inj_fv = d.fresh_fvar();
    let inj = d.kernel().fvar(inj_fv);
    let maps_fv = d.fresh_fvar();
    let maps = d.kernel().fvar(maps_fv);
    let preserve_fv = d.fresh_fvar();
    let preserve = d.kernel().fvar(preserve_fv);

    // Step 1: `Int.prodRange_permute` at the UNRESTRICTED selector `h`.
    let h = selector(d, pred, f);
    let step1 = d.lemma(p.prod_range_permute, &[h, n, sigma, inj, maps]);
    // step1 : Eq Int (prodRange h n) (prodRange (h ∘ σ) n)

    // Step 2: `Int.prodRange_congr_lt` rewrites `h ∘ σ` to the selector for
    // `pred`/`f ∘ σ`, pointwise below `n`, using `preserve`.
    let h_comp_sigma = compose(d, h, sigma);
    let f_comp_sigma = compose(d, f, sigma);
    let target_selector = selector(d, pred, f_comp_sigma);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(k, n);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hp_k = d.apply(preserve, &[k, hk]);
        let sigma_k = d.apply(sigma, &[k]);
        let pred_sigma_k = d.apply(pred, &[sigma_k]);
        let pred_k = d.apply(pred, &[k]);
        let f_sigma_k = d.apply(f, &[sigma_k]);
        let one = d.ione();
        let proof_k = bool_select_int_congr_cond(d, pred_sigma_k, pred_k, hp_k, f_sigma_k, one);
        let with_hk = d.lam_fv(hk_fv, hk_ty, proof_k);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let step2 = d.lemma(
        p.prod_range_congr_lt,
        &[h_comp_sigma, target_selector, n, pointwise],
    );
    // step2 : Eq Int (prodRange (h ∘ σ) n) (prodRange target_selector n)

    let prod_h_n = d.const_app(p.prod_range, &[h, n]);
    let prod_hsigma_n = d.const_app(p.prod_range, &[h_comp_sigma, n]);
    let prod_target_n = d.const_app(p.prod_range, &[target_selector, n]);
    let (_e, proof) = d.ichain(prod_h_n, &[(prod_hsigma_n, step1), (prod_target_n, step2)]);
    // proof : Eq Int (prodRange h n) (prodRange target_selector n), which is
    // exactly `permute_concl`'s stated form.

    let concl = permute_concl(d, pred, f, sigma, n);

    let value = {
        let with_preserve = d.lam_fv(preserve_fv, preserve_ty, proof);
        let with_maps = d.lam_fv(maps_fv, maps_ty, with_preserve);
        let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
        let with_n = d.lam_fv(n_fv, nat, with_inj);
        let with_sigma = d.lam_fv(sigma_fv, fn_ty_nat, with_n);
        let with_f = d.lam_fv(f_fv, fn_ty_int, with_sigma);
        d.lam_fv(pred_fv, pred_ty, with_f)
    };
    let ty = {
        let with_preserve = d.arrow(preserve_ty, concl);
        let with_maps = d.arrow(maps_ty, with_preserve);
        let with_inj = d.arrow(inj_ty, with_maps);
        let with_n = d.pi_fv(n_fv, nat, with_inj);
        let with_sigma = d.pi_fv(sigma_fv, fn_ty_nat, with_n);
        let with_f = d.pi_fv(f_fv, fn_ty_int, with_sigma);
        d.pi_fv(pred_fv, pred_ty, with_f)
    };
    d.declare_theorem(p.prod_range_if_permute, ty, value)
}

/// Declare `Int.prodRangeIf`, its two defining equations, and its
/// permutation-invariance corollary — everything this slice lands (see the
/// module doc for what does NOT land here, and why).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_if_all(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    declare_prod_range_if(d)?;
    declare_prod_range_if_defining_equations(d)?;
    declare_prod_range_if_permute(d)?;
    Ok(())
}
