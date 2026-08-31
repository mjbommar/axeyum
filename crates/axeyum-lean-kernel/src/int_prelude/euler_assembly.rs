//! `Int.euler_totient_theorem : ∀ n a, 0 < n → Coprime a (ofNat n) →
//! ModEq (ofNat n) (pow a (totient n)) one` — Euler's totient theorem, the
//! final assembly of the Fermat -> Euler handoff
//! (`docs/plan/status/374-euler-theorem.md`,
//! `docs/plan/status/euler-theorem-spine.md`). Every ingredient item 3
//! needed is landed elsewhere (`euler_theorem.rs`, `euler_unit_range.rs`,
//! `euler_unit_preserve.rs`, `euler_prod_pow.rs`, `euler_prod_coprime.rs`,
//! `euler_prod_factor.rs`, `euler_prod_modeq.rs`); this file wires them into
//! one declaration and adds no new induction.
//!
//! ## The predicate and the permutation
//!
//! `pred := fun k => beq (gcd k n) 1` — a per-file local copy of
//! `nat_prelude/totient.rs`'s own private `totient_predicate`, built the
//! same way (`d.gcd`/`d.num(1)`/`d.beq`) so that `Nat.totient n` unfolds
//! (delta on `Nat.totient`) to exactly `countRange pred n` — no separate
//! bridging lemma needed, only kernel-level unfolding at the point of use
//! (this file's own convention, matching every sibling file's "unfolded
//! statement" choice).
//!
//! `sigma := euler_unit_range::sigma_term(a, ofNat n)` (`k => natAbs (emod
//! (a*ofNat k) (ofNat n))`), `Nat -> Nat`. `Int.euler_unit_perm_injective`/
//! `_maps_into` give `InjectiveOn sigma n`/`MapsInto sigma n` directly (no
//! Int/Nat bridging code needed — ADR-1025's finding that the order half is
//! free by defeq, confirmed again here by direct application).
//!
//! ## The nine-step chain
//!
//! `id_int := fun k => ofNat k` is the function `Int.prodRangeIf_permute`
//! permutes.
//!
//! 1. `preserve : ∀i, i<n → pred (sigma i) = pred i`, from
//!    `Int.euler_unit_coprime_iff` plus a Bool/Prop reflection bridge
//!    ([`bool_eq_of_iff_eq_one`], a per-file `IntDev`-typed port of
//!    `nat_prelude/totient_lemmas.rs`'s private `bool_eq_of_iff_eq_one`).
//! 2. `Int.prodRangeIf_permute` (with `InjectiveOn`/`MapsInto`/`preserve`):
//!    `prodRangeIf pred id_int n = prodRangeIf pred (id_int∘sigma) n`.
//! 3. `id_int∘sigma` and `g := fun k => emod (a*ofNat k) (ofNat n)` agree
//!    pointwise (`Int.of_nat_nat_abs_of_nonneg` — `ofNat` undoes `natAbs` on
//!    a nonnegative `emod`), lifted through the selector by
//!    `Int.prodRange_congr`.
//! 4. `Int.prodRangeIf_modeq` (pointwise `emod_modeq_self`, reversed):
//!    `ModEq n (prodRangeIf pred g n) (prodRangeIf pred h n)`, `h := fun k
//!    => a * ofNat k` (unreduced).
//! 5. `Int.prodRangeIf_factor_const_left`: `prodRangeIf pred h n =
//!    (prodRangeIf pred (fun _=>a) n) * (prodRangeIf pred id_int n)`.
//! 6. `Int.prodRangeIf_const_eq_pow_count`: `prodRangeIf pred (fun _=>a) n =
//!    pow a (countRange pred n)`.
//! 7. `Int.prodRangeIf_coprime` (every `k` with `pred k = true` has `ofNat k`
//!    coprime to `ofNat n`, from `Nat.eq_of_beq_eq_true`): `Coprime
//!    (prodRangeIf pred id_int n) (ofNat n)`.
//! 8. Chain steps 2-6 (via `int_eq_rewrite`, since a `Eq Int` step can
//!    rewrite inside an already-established `ModEq`) into one `ModEq (ofNat
//!    n) (prodRangeIf pred id_int n) (mul (pow a (countRange pred n))
//!    (prodRangeIf pred id_int n))`.
//! 9. `Int.modEq_cancel` (fed step 7's coprimality, after commuting/`mul_one`
//!    reshaping both sides into a common-left-factor form) cancels
//!    `prodRangeIf pred id_int n`, giving `ModEq (ofNat n) one (pow a
//!    (countRange pred n))`; `Int.ModEq.symm` plus `Nat.totient`'s own
//!    unfolding (`countRange pred n ≡ totient n`) finishes.

use super::euler_unit_range::{nat_abs, sigma_term};
use super::modeq::imodeq;
use super::ops::IntDev;
use super::prod::bool_select_int;
use super::wilson::{emod_modeq_self, int_ne_zero_of_pos};
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

// ============================================================================
// Local plumbing (per-file local copies, this development's own convention).
// ============================================================================

/// `fun k => f (g k)` — a local copy of `euler_theorem.rs`'s private
/// `compose`.
fn compose(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun i => bool_select_int (pred i) (f i) Int.one` — a per-file local copy
/// of `euler_theorem.rs`'s private `selector`.
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

/// `Or (Eq Bool b true) (Eq Bool b false)` at `b` — a local `IntDev`-typed
/// copy of `nat_prelude/subset_product.rs`'s (etc.) thrice-duplicated
/// `bool_true_or_false`.
fn bool_true_or_false_int(d: &mut IntDev<'_>, b: ExprId) -> ExprId {
    let p = d.int();
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let true_inner = d.bool_true();
        let false_inner = d.bool_false();
        let is_true = d.bool_eq(x, true_inner);
        let is_false = d.bool_eq(x, false_inner);
        let body = d.const_app(p.logic.or, &[is_true, is_false]);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let is_false = d.bool_eq(true_, false_);
        let refl_true = d.bool_refl(true_);
        d.const_app(p.logic.or_inl, &[is_true, is_false, refl_true])
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let is_false = d.bool_eq(false_, false_);
        let refl_false = d.bool_refl(false_);
        d.const_app(p.logic.or_inr, &[is_true, is_false, refl_false])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// From `iff_ab : Iff (Eq Nat a one) (Eq Nat b one)`, derive `Eq Bool (beq a
/// one) (beq b one)` — an `IntDev`-typed port of
/// `nat_prelude/totient_lemmas.rs`'s private `bool_eq_of_iff_eq_one`
/// (identical technique: decide `beq a one` via [`bool_true_or_false_int`],
/// push each case through `eq_of_beq_eq_true`/`ne_of_beq_eq_false` and
/// `beq_eq_true_of_eq`/`beq_eq_false_of_ne`).
fn bool_eq_of_iff_eq_one(d: &mut IntDev<'_>, a: ExprId, b: ExprId, iff_ab: ExprId) -> ExprId {
    let p = d.int();
    let one = d.num(1);
    let beq_a = d.beq(a, one);
    let beq_b = d.beq(b, one);
    let a_eq_one = d.eq(a, one);
    let b_eq_one = d.eq(b, one);
    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let cases = bool_true_or_false_int(d, beq_a);

    let is_true_ty = d.bool_eq(beq_a, true_v);
    let is_false_ty = d.bool_eq(beq_a, false_v);
    let target = d.bool_eq(beq_a, beq_b);

    let on_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let a_eq = d.lemma(p.nat.eq_of_beq_eq_true, &[a, one, h]);
        let mp = d.lemma(p.logic.iff_mp, &[a_eq_one, b_eq_one, iff_ab]);
        let b_eq = d.apply(mp, &[a_eq]);
        let beq_b_true = d.lemma(p.nat.beq_eq_true_of_eq, &[b, one, b_eq]);
        let beq_b_true_rev = d.bool_symm(beq_b, true_v, beq_b_true);
        let result = d.bool_trans(beq_a, true_v, beq_b, h, beq_b_true_rev);
        d.lam_fv(h_fv, is_true_ty, result)
    };
    let on_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let a_ne_one = d.lemma(p.nat.ne_of_beq_eq_false, &[a, one, h]);
        let not_b_eq_one = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let mpr = d.lemma(p.logic.iff_mpr, &[a_eq_one, b_eq_one, iff_ab]);
            let a_eq_from_b = d.apply(mpr, &[hb]);
            let absurd = d.apply(a_ne_one, &[a_eq_from_b]);
            d.lam_fv(hb_fv, b_eq_one, absurd)
        };
        let beq_b_false = d.lemma(p.nat.beq_eq_false_of_ne, &[b, one, not_b_eq_one]);
        let beq_b_false_rev = d.bool_symm(beq_b, false_v, beq_b_false);
        let result = d.bool_trans(beq_a, false_v, beq_b, h, beq_b_false_rev);
        d.lam_fv(h_fv, is_false_ty, result)
    };
    d.const_app(
        p.logic.or_elim,
        &[is_true_ty, is_false_ty, target, cases, on_true, on_false],
    )
}

/// `fun k => beq (gcd k n) 1` — a per-file local copy of
/// `nat_prelude/totient.rs`'s private `totient_predicate`, built the same
/// way so `Nat.totient n` unfolds to exactly `countRange (totient_predicate
/// n) n` (see the module doc).
fn totient_predicate(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let g = d.gcd(k, n);
    let one = d.num(1);
    let body = d.beq(g, one);
    d.lam_fv(k_fv, nat, body)
}

/// Declare `Int.euler_totient_theorem` (see the module doc for the full
/// nine-step derivation).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_euler_totient_theorem(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let zero_nat = d.zero();
    let pos_ty = d.lt(zero_nat, n); // Nat.lt 0 n
    let n_int = d.of_nat(n);
    let cop_a_ty = d.const_app(p.coprime, &[a, n_int]);

    let pred = totient_predicate(d, n);
    let sigma = sigma_term(d, a, n_int);
    let id_int = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ofk = d.of_nat(k);
        d.lam_fv(k_fv, nat, ofk)
    };

    let count_n = d.const_app(p.nat.count_range, &[pred, n]);
    let one_i = d.ione();
    let pow_a_count = d.ipow(a, count_n);
    let concl = imodeq(d, n_int, pow_a_count, one_i);

    let ty = {
        let inner = d.arrow(cop_a_ty, concl);
        let with_pos = d.arrow(pos_ty, inner);
        let with_a = d.pi_fv(a_fv, int_ty, with_pos);
        d.pi_fv(n_fv, nat, with_a)
    };

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);
    let h_cop_a_fv = d.fresh_fvar();
    let h_cop_a = d.kernel().fvar(h_cop_a_fv);

    // ------------------------------------------------------------------
    // Step 1: `preserve : forall i, i<n -> pred (sigma i) = pred i`.
    // ------------------------------------------------------------------
    let preserve = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, n);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);

        let ofi = d.of_nat(i);
        let zero_le_i = d.lemma(p.nat.zero_le, &[i]);
        let iff_i = d.const_app(
            p.euler_unit_coprime_iff,
            &[n_int, a, ofi, h_pos, zero_le_i, hi, h_cop_a],
        );
        // iff_i : Iff (Coprime ofi n_int) (Coprime (emod (a*ofi) n_int) n_int)

        let ak = d.imul(a, ofi);
        let r = d.iemod(ak, n_int);
        let sigma_i = nat_abs(d, r);

        let gi = d.gcd(i, n);
        let gsi = d.gcd(sigma_i, n);
        let bool_eq_i_si = bool_eq_of_iff_eq_one(d, gi, gsi, iff_i);
        // bool_eq_i_si : Eq Bool (beq gi 1) (beq gsi 1) = Eq Bool (pred i) (pred sigma_i)

        let one_nat = d.num(1);
        let pred_i = d.beq(gi, one_nat);
        let pred_si = d.beq(gsi, one_nat);
        let flipped = d.bool_symm(pred_i, pred_si, bool_eq_i_si);
        // flipped : Eq Bool pred_si pred_i

        let with_hi = d.lam_fv(hi_fv, hi_ty, flipped);
        d.lam_fv(i_fv, nat, with_hi)
    };

    // ------------------------------------------------------------------
    // Step 2: `Int.prodRangeIf_permute`.
    // ------------------------------------------------------------------
    let inj = d.const_app(p.euler_unit_perm_injective, &[n, a, h_pos, h_cop_a]);
    let maps = d.const_app(p.euler_unit_perm_maps_into, &[n, a, h_pos]);
    let permute_pf = d.const_app(
        p.prod_range_if_permute,
        &[pred, id_int, sigma, n, inj, maps, preserve],
    );
    // permute_pf : Eq Int (prodRangeIf pred id_int n) (prodRangeIf pred (id_int . sigma) n)

    let sel_id = selector(d, pred, id_int);
    let p_id = d.const_app(p.prod_range, &[sel_id, n]);
    let id_sigma = compose(d, id_int, sigma);
    let sel_idsigma0 = selector(d, pred, id_sigma);
    let p_idsigma = d.const_app(p.prod_range, &[sel_idsigma0, n]);

    // ------------------------------------------------------------------
    // Step 3: `id_int . sigma` and `g` agree pointwise; lift through the
    // selector via `Int.prodRange_congr`.
    // ------------------------------------------------------------------
    let g_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ofk = d.of_nat(k);
        let ak = d.imul(a, ofk);
        let body = d.iemod(ak, n_int);
        d.lam_fv(k_fv, nat, body)
    };
    let ne_n = int_ne_zero_of_pos(d, n_int, h_pos);

    let pointwise_sel = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pk = d.apply(pred, &[k]);
        let idsigma_k = {
            let sk = d.apply(sigma, &[k]);
            d.apply(id_int, &[sk])
        };
        // idsigma_k : App id_int (App sigma k)  -- beta -> ofNat (natAbs r_k)
        let ofk = d.of_nat(k);
        let ak = d.imul(a, ofk);
        let r_k = d.iemod(ak, n_int);
        let mag_k = nat_abs(d, r_k);
        let r_nonneg = d.const_app(p.emod_nonneg, &[ak, n_int, ne_n]);
        let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_k, r_nonneg]);
        // bridge : Eq Int (ofNat (natAbs r_k)) r_k
        let ofmag_k = d.of_nat(mag_k);
        // idsigma_k reduces (beta+delta+iota through sigma) to `ofmag_k`;
        // `bridge` therefore already has the type `Eq Int idsigma_k (g_fn k)`
        // once both sides are unfolded to their common `ofNat (natAbs r_k)`/
        // `r_k` normal forms -- `g_fn k` beta-reduces to `r_k` exactly.
        let gk = d.apply(g_fn, &[k]);
        let idsigma_eq_g = {
            // Re-anchor `bridge`'s stated type onto the exact (unreduced)
            // `idsigma_k`/`gk` forms via a `Eq.refl`-transparent transport:
            // `bridge : Eq Int ofmag_k r_k`, and `idsigma_k ~ ofmag_k`,
            // `gk ~ r_k` are both pure beta/delta/iota, so `bridge` itself
            // already checks at type `Eq Int idsigma_k gk`.
            let _ = ofmag_k;
            bridge
        };
        let one_i2 = d.ione();
        let congr_step = d.icongr(idsigma_k, gk, idsigma_eq_g, &|d, t| {
            bool_select_int(d, pk, t, one_i2)
        });
        d.lam_fv(k_fv, nat, congr_step)
    };

    let sel_g = selector(d, pred, g_fn);
    let congr_pf = d.lemma(p.prod_range_congr, &[sel_idsigma0, sel_g, n, pointwise_sel]);
    let p_g = d.const_app(p.prod_range, &[sel_g, n]);
    // congr_pf : Eq Int p_idsigma p_g

    let (_e, eq_chain) = d.ichain(p_id, &[(p_idsigma, permute_pf), (p_g, congr_pf)]);
    // eq_chain : Eq Int p_id p_g

    // ------------------------------------------------------------------
    // Step 4: `Int.prodRangeIf_modeq`, `g` -> `h` (unreduced product).
    // ------------------------------------------------------------------
    let h_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let idk = d.apply(id_int, &[k]);
        let body = d.imul(a, idk);
        d.lam_fv(k_fv, nat, body)
    };
    let modeq_pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let idk = d.apply(id_int, &[k]);
        let ak = d.imul(a, idk);
        let em = emod_modeq_self(d, ak, n_int, h_pos);
        // em : ModEq n_int ak (emod ak n_int) = ModEq n_int (h_fn k) (g_fn k)
        let ak_emod = d.iemod(ak, n_int);
        let em_symm = d.lemma(p.mod_eq_symm, &[n_int, ak, ak_emod, em]);
        d.lam_fv(k_fv, nat, em_symm)
    };
    let sel_h = selector(d, pred, h_fn);
    let p_h = d.const_app(p.prod_range, &[sel_h, n]);
    let modeq_gh = d.lemma(
        p.prod_range_if_modeq,
        &[n_int, pred, g_fn, h_fn, n, h_pos, modeq_pointwise],
    );
    // modeq_gh : ModEq n_int p_g p_h

    // Rewrite modeq_gh's LHS from `p_g` back to `p_id` via `eq_chain`.
    let eq_chain_rev = d.isymm(p_id, p_g, eq_chain);
    let modeq_id_h = d.int_eq_rewrite(p_g, p_id, eq_chain_rev, modeq_gh, &|d, x| {
        imodeq(d, n_int, x, p_h)
    });
    // modeq_id_h : ModEq n_int p_id p_h

    // ------------------------------------------------------------------
    // Step 5/6: `Int.prodRangeIf_factor_const_left`,
    // `Int.prodRangeIf_const_eq_pow_count`.
    // ------------------------------------------------------------------
    let factor_pf = d.const_app(p.prod_range_if_factor_const_left, &[pred, a, id_int, n]);
    // factor_pf : Eq Int p_h (mul p_a p_id)
    let const_a = {
        let unused_fv = d.fresh_fvar();
        d.lam_fv(unused_fv, nat, a)
    };
    let sel_a = selector(d, pred, const_a);
    let p_a = d.const_app(p.prod_range, &[sel_a, n]);
    let mul_pa_pid = d.imul(p_a, p_id);

    let modeq_id_factored = d.int_eq_rewrite(p_h, mul_pa_pid, factor_pf, modeq_id_h, &|d, x| {
        imodeq(d, n_int, p_id, x)
    });
    // modeq_id_factored : ModEq n_int p_id (mul p_a p_id)

    let count_pow_pf = d.const_app(p.prod_range_if_const_eq_pow_count, &[pred, a, n]);
    // count_pow_pf : Eq Int p_a (pow a count_n)
    let modeq_final_raw = d.int_eq_rewrite(
        p_a,
        pow_a_count,
        count_pow_pf,
        modeq_id_factored,
        &|d, x| {
            let mul_x_pid = d.imul(x, p_id);
            imodeq(d, n_int, p_id, mul_x_pid)
        },
    );
    // modeq_final_raw : ModEq n_int p_id (mul pow_a_count p_id)

    // ------------------------------------------------------------------
    // Step 7: `Int.prodRangeIf_coprime` — `p_id` is coprime to `n_int`.
    // ------------------------------------------------------------------
    let cop_pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_ty = d.lt(k, n);
        let hk_fv = d.fresh_fvar();
        let true_v = d.bool_true();
        let pk_true_ty = {
            let pk = d.apply(pred, &[k]);
            d.bool_eq(pk, true_v)
        };
        let pk_true_fv = d.fresh_fvar();
        let pk_true = d.kernel().fvar(pk_true_fv);

        let gk = d.gcd(k, n);
        let one_nat = d.num(1);
        let gk_eq_one = d.lemma(p.nat.eq_of_beq_eq_true, &[gk, one_nat, pk_true]);
        // gk_eq_one : Eq Nat gk one, defeq `Coprime (App id_int k) n_int`.

        let with_pk = d.lam_fv(pk_true_fv, pk_true_ty, gk_eq_one);
        let with_hk = d.lam_fv(hk_fv, hk_ty, with_pk);
        d.lam_fv(k_fv, nat, with_hk)
    };
    let cop_pf = d.const_app(
        p.prod_range_if_coprime,
        &[pred, id_int, n_int, n, h_pos, cop_pointwise],
    );
    // cop_pf : Coprime p_id n_int

    // ------------------------------------------------------------------
    // Step 8/9: cancel `p_id`.
    // ------------------------------------------------------------------
    let mul_pid_one = d.imul(p_id, one_i);
    let mul_one_pid = d.const_app(p.mul_one, &[p_id]);
    // mul_one_pid : Eq Int (mul p_id one) p_id
    let mul_one_pid_rev = d.isymm(mul_pid_one, p_id, mul_one_pid);
    // mul_one_pid_rev : Eq Int p_id (mul p_id one)

    let mul_pow_pid = d.imul(pow_a_count, p_id);
    let modeq_a = d.int_eq_rewrite(
        p_id,
        mul_pid_one,
        mul_one_pid_rev,
        modeq_final_raw,
        &|d, x| {
            let rhs = d.imul(pow_a_count, p_id);
            imodeq(d, n_int, x, rhs)
        },
    );
    // modeq_a : ModEq n_int (mul p_id one) (mul pow_a_count p_id)

    let comm_pf = d.const_app(p.mul_comm, &[pow_a_count, p_id]);
    // comm_pf : Eq Int (mul pow_a_count p_id) (mul p_id pow_a_count)
    let mul_pid_pow = d.imul(p_id, pow_a_count);
    let modeq_b = d.int_eq_rewrite(mul_pow_pid, mul_pid_pow, comm_pf, modeq_a, &|d, x| {
        let lhs = d.imul(p_id, one_i);
        imodeq(d, n_int, lhs, x)
    });
    // modeq_b : ModEq n_int (mul p_id one) (mul p_id pow_a_count)

    let cancel_pf = d.const_app(
        p.mod_eq_cancel,
        &[n_int, p_id, one_i, pow_a_count, h_pos, cop_pf, modeq_b],
    );
    // cancel_pf : ModEq n_int one pow_a_count

    let final_pf = d.lemma(p.mod_eq_symm, &[n_int, one_i, pow_a_count, cancel_pf]);
    // final_pf : ModEq n_int pow_a_count one, defeq the stated `concl`.

    let with_cop_a = d.lam_fv(h_cop_a_fv, cop_a_ty, final_pf);
    let with_pos = d.lam_fv(h_pos_fv, pos_ty, with_cop_a);
    let with_a = d.lam_fv(a_fv, int_ty, with_pos);
    let value = d.lam_fv(n_fv, nat, with_a);

    d.declare_theorem(p.euler_totient_theorem, ty, value)
}
