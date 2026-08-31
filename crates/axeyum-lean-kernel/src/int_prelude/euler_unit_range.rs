//! `Nat.injectiveOn`/`Nat.mapsInto` for the Euler unit-permutation self-map
//! `sigma(k) := natAbs (emod (a * ofNat k) (ofNat n))` -- item 1 of the
//! three-piece Fermat -> Euler handoff (`docs/plan/status/374-euler-theorem.md`,
//! re-sized in `docs/plan/status/euler-theorem-spine.md`/ADR-1025).
//!
//! `Int.prodRangeIf_permute` (`euler_theorem.rs`) needs a `Nat -> Nat`
//! self-map of the FULL range `[0,n)` -- `Nat.injectiveOn sigma n` and
//! `Nat.mapsInto sigma n` -- not a subset-restricted bijection, so neither
//! of `euler_totient.rs`'s two flagged missing pieces (the subset
//! pigeonhole, the subset product) is needed here. What is missing is
//! purely the `Int`/`Nat` bridge: `Int.euler_unit_injective`
//! (`euler_totient.rs`) is stated over `Int`-sorted, individually-bounded
//! `i`, `j`; `InjectiveOn`/`MapsInto` are stated over `Nat`-sorted `i`, `j`
//! bound by the SAME `Nat` `n` the range iterates over.
//!
//! ADR-1025 found most of that bridge is free by defeq, not a lemma to
//! write: `Int.le`/`Int.lt` iota-reduce their `ofNat`/`ofNat` branch
//! straight to the `Nat` comparison (`order_coercion.rs`), so a `Nat.lt i n`
//! proof already has type `Int.lt (ofNat i) (ofNat n)` up to unfolding, and
//! symmetrically a `Nat.zero_le i` proof already has type
//! `Int.le zero (ofNat i)`. This file supplies exactly those hypothesis
//! terms directly (no coercion lemma call, matching `order_coercion.rs`'s
//! own module doc) and reuses the `natAbs`/`Int.of_nat_nat_abs_of_nonneg`
//! residue-bridging pattern `wilson.rs`'s
//! `declare_inverse_index_injective`/`declare_inverse_index_maps_into`
//! already built for a structurally identical (but `-1`-shifted) self-map:
//! recovering `Eq Int r_i r_j` from `Eq Nat (natAbs r_i) (natAbs r_j)`
//! (needs both residues' nonnegativity), and recovering `Eq Nat i j` from
//! `Eq Int (ofNat i) (ofNat j)` (needs `natAbs (ofNat i) ≡ i`, again defeq).
//!
//! ## What is declared
//!
//! - [`declare_euler_unit_perm_injective`] -- `Int.euler_unit_perm_injective :
//!   ∀ n a, 0 < n → Coprime a (ofNat n) →
//!   InjectiveOn (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n`.
//!   One application of `Int.euler_unit_injective` per pair, bridged both
//!   ways through `natAbs`/`ofNat`.
//! - [`declare_euler_unit_perm_maps_into`] -- `Int.euler_unit_perm_maps_into :
//!   ∀ n a, 0 < n → MapsInto (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n`.
//!   Unconditional in `a` -- `Int.emod`'s bound (`emod_nonneg`/
//!   `emod_lt_of_pos`) needs no coprimality, matching `euler_totient.rs`'s
//!   own module doc on why `MapsInto` is the easy half.
//!
//! No new induction anywhere in this file -- both proofs are direct
//! applications of already-proved theorems, glued by the `natAbs`/`ofNat`
//! round trip. Both are admitted by the trusted kernel gate.

use super::wilson::int_ne_zero_of_pos;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

/// `Int.natAbs` applied -- a per-file local copy of the same one-line
/// helper every other file in this development that touches `natAbs`
/// re-derives locally (`gcd.rs`, `wilson.rs`, `fibonacci.rs`, …).
fn nat_abs(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let name = d.int().nat_abs;
    d.const_app(name, &[a])
}

/// `fun k => natAbs (emod (mul a (ofNat k)) (ofNat n))` -- the residue index
/// map, `Nat -> Nat`, folded `Int.prodRangeIf_permute` needs its self-map
/// argument to be.
fn sigma_term(d: &mut IntDev<'_>, a: ExprId, n_int: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let ofk = d.of_nat(k);
    let ak = d.imul(a, ofk);
    let r = d.iemod(ak, n_int);
    let mag = nat_abs(d, r);
    d.lam_fv(k_fv, nat, mag)
}

/// `Int.euler_unit_perm_injective : ∀ n a, 0 < n → Coprime a (ofNat n) →
/// InjectiveOn (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_euler_unit_perm_injective(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let n_fv = d.fresh_fvar();
    let n_nat = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let n_int = d.of_nat(n_nat);
    let sigma = sigma_term(d, a, n_int);
    let concl = d.const_app(p.nat.injective_on, &[sigma, n_nat]);

    let zero_nat = d.zero();
    let pos_ty = d.lt(zero_nat, n_nat);
    let cop_ty = d.const_app(p.coprime, &[a, n_int]);

    let ty = {
        let inner = d.arrow(cop_ty, concl);
        let with_pos = d.arrow(pos_ty, inner);
        let with_a = d.pi_fv(a_fv, int_ty, with_pos);
        d.pi_fv(n_fv, nat, with_a)
    };

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);
    let h_cop_fv = d.fresh_fvar();
    let h_cop = d.kernel().fvar(h_cop_fv);

    // `h_pos : Nat.lt 0 n` is used BELOW, unchanged, wherever
    // `Int.lt zero (ofNat n)` is expected -- `Int.lt`'s `ofNat`/`ofNat`
    // branch iota-reduces to `Nat.lt` (`order_coercion.rs`'s module doc).
    let ne_n = int_ne_zero_of_pos(d, n_int, h_pos);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hi_ty = d.lt(i, n_nat);
    let hj_ty = d.lt(j, n_nat);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);

    let ofi = d.of_nat(i);
    let ofj = d.of_nat(j);
    let ai = d.imul(a, ofi);
    let aj = d.imul(a, ofj);
    let r_i = d.iemod(ai, n_int);
    let r_j = d.iemod(aj, n_int);
    let mag_i = nat_abs(d, r_i);
    let mag_j = nat_abs(d, r_j);
    let heq_ty = d.eq(mag_i, mag_j);
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    // Bridge `heq : natAbs r_i = natAbs r_j` (Nat) to `r_i = r_j` (Int),
    // via nonnegativity of both residues -- the same
    // `of_nat_nat_abs_of_nonneg` round trip `wilson.rs::
    // declare_inverse_index_injective` uses for its (shifted) residue.
    let r_i_nonneg = d.const_app(p.emod_nonneg, &[ai, n_int, ne_n]);
    let r_j_nonneg = d.const_app(p.emod_nonneg, &[aj, n_int, ne_n]);
    let bridge_i = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_i, r_i_nonneg]);
    let bridge_j = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r_j, r_j_nonneg]);
    let ofnat_mag_i = d.of_nat(mag_i);
    let ofnat_mag_j = d.of_nat(mag_j);
    let congr_mag = d.nat_eq_to_int(mag_i, mag_j, heq, &|d, y| d.of_nat(y));
    let bridge_i_rev = d.isymm(ofnat_mag_i, r_i, bridge_i);
    let (_, r_i_eq_r_j) = d.ichain(
        r_i,
        &[
            (ofnat_mag_i, bridge_i_rev),
            (ofnat_mag_j, congr_mag),
            (r_j, bridge_j),
        ],
    );

    // `Nat.zero_le i`/`Nat.zero_le j` used directly wherever
    // `Int.le zero (ofNat i)`/`Int.le zero (ofNat j)` is expected -- same
    // defeq shortcut as `h_pos` above.
    let zero_le_i = d.lemma(p.nat.zero_le, &[i]);
    let zero_le_j = d.lemma(p.nat.zero_le, &[j]);

    let final_eq = d.const_app(
        p.euler_unit_injective,
        &[
            n_int, a, ofi, ofj, h_pos, h_cop, zero_le_i, hi, zero_le_j, hj, r_i_eq_r_j,
        ],
    );
    // final_eq : Eq Int (ofNat i) (ofNat j).

    // `natAbs (ofNat i) ≡ i` and `natAbs (ofNat j) ≡ j` by iota-reduction
    // (`nat_abs.rs`'s module doc), so `Eq.refl i` already has the type this
    // rewrite's base case needs, and the rewritten result already has the
    // type `Eq Nat i j` this theorem's conclusion needs -- no further step.
    let refl_i = d.refl(i);
    let result = d.int_eq_rewrite(ofi, ofj, final_eq, refl_i, &|d, x| {
        let nx = nat_abs(d, x);
        d.eq(i, nx)
    });

    let with_heq = d.lam_fv(heq_fv, heq_ty, result);
    let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
    let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
    let with_j = d.lam_fv(j_fv, nat, with_hi);
    let inj_body = d.lam_fv(i_fv, nat, with_j);

    let with_cop = d.lam_fv(h_cop_fv, cop_ty, inj_body);
    let with_pos = d.lam_fv(h_pos_fv, pos_ty, with_cop);
    let with_a = d.lam_fv(a_fv, int_ty, with_pos);
    let value = d.lam_fv(n_fv, nat, with_a);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euler_unit_perm_injective,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(())
}

/// `Int.euler_unit_perm_maps_into : ∀ n a, 0 < n →
/// MapsInto (fun k => natAbs (emod (a * ofNat k) (ofNat n))) n`.
///
/// Unconditional in `a`: `Int.emod`'s bound needs only `n ≠ 0`
/// (`emod_nonneg`) and `0 < n` (`emod_lt_of_pos`), no coprimality.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_euler_unit_perm_maps_into(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let n_fv = d.fresh_fvar();
    let n_nat = d.kernel().fvar(n_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let n_int = d.of_nat(n_nat);
    let sigma = sigma_term(d, a, n_int);
    let concl = d.const_app(p.nat.maps_into, &[sigma, n_nat]);

    let zero_nat = d.zero();
    let pos_ty = d.lt(zero_nat, n_nat);

    let ty = {
        let inner = d.arrow(pos_ty, concl);
        let with_a = d.pi_fv(a_fv, int_ty, inner);
        d.pi_fv(n_fv, nat, with_a)
    };

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hi_ty = d.lt(i, n_nat);
    // The `i < n` hypothesis is a required binder in `MapsInto`'s Pi type
    // but is genuinely unused in the proof: `Int.emod`'s bound holds for
    // ANY `i`, not just those already known to be in range.
    let hi_fv = d.fresh_fvar();

    let ofi = d.of_nat(i);
    let ai = d.imul(a, ofi);
    let r = d.iemod(ai, n_int);
    let mag = nat_abs(d, r);

    let ne_n = int_ne_zero_of_pos(d, n_int, h_pos);
    let r_nonneg = d.const_app(p.emod_nonneg, &[ai, n_int, ne_n]);
    let r_lt = d.const_app(p.emod_lt_of_pos, &[ai, n_int, h_pos]);
    let bridge = d.const_app(p.of_nat_nat_abs_of_nonneg, &[r, r_nonneg]);
    let ofnat_mag = d.of_nat(mag);
    let bridge_rev = d.isymm(ofnat_mag, r, bridge);
    let mag_lt_n = d.int_eq_rewrite(r, ofnat_mag, bridge_rev, r_lt, &|d, x| d.ilt(x, n_int));
    // mag_lt_n : Int.lt (ofNat mag) n_int = Int.lt (ofNat mag) (ofNat n_nat),
    // which is `Nat.lt mag n_nat` up to the same iota-reduction as above --
    // exactly the theorem's conclusion at this point.

    let with_hi = d.lam_fv(hi_fv, hi_ty, mag_lt_n);
    let maps_body = d.lam_fv(i_fv, nat, with_hi);
    let with_pos = d.lam_fv(h_pos_fv, pos_ty, maps_body);
    let with_a = d.lam_fv(a_fv, int_ty, with_pos);
    let value = d.lam_fv(n_fv, nat, with_a);

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.euler_unit_perm_maps_into,
        ty,
        uparams: vec![],
        value,
    })?;
    Ok(())
}
