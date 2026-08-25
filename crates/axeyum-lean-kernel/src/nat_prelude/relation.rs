//! `Nat.ReflexiveOn` / `Nat.SymmetricOn` / `Nat.TransitiveOn` /
//! `Nat.EquivalenceOn` — relation properties bounded on `{0, …, n-1}` — plus
//! `Nat.BijectiveOn` and `Nat.comp`, the pieces that connect the relation
//! layer to `finite.rs`'s already-proved `InjectiveOn`/`MapsInto`/
//! `SurjectiveOn`/`injective_on_imp_surjective_on`.
//!
//! ## `Bool` or `Prop`?
//!
//! **`Prop`.** A relation here is `r : Nat → Nat → Prop`, exactly the shape
//! `finite.rs`'s own `InjectiveOn`/`SurjectiveOn`/`MapsInto` already use
//! (`f i = f j`, `∃ i, i < n ∧ f i = k` — both `Prop`-valued, never `Bool`).
//! Every relation this module actually instantiates — `Eq Nat` and
//! `Nat.modEq m` — is itself `Prop`-valued already (`modEq d a b := ∃ u v, …`
//! is an `Exists`, not a `Nat.ble`-style computation), so there is no
//! executable content to preserve by going through `Bool`, and `Bool`'s own
//! recursor cannot eliminate into `Type`/`Sort 1` (`Or`'s recursor has the
//! same restriction, per the module brief) — a real cost with no
//! corresponding benefit here, since none of `ReflexiveOn`/`SymmetricOn`/
//! `TransitiveOn`/`EquivalenceOn` ever need to *compute* a `Bool` result, only
//! to *state* a property. `Prop` is the strictly simpler, strictly more
//! general choice for this slice.
//!
//! ## What's declared
//!
//! - `Nat.ReflexiveOn r n := ∀ i, i < n → r i i`
//! - `Nat.SymmetricOn r n := ∀ i j, i < n → j < n → r i j → r j i`
//! - `Nat.TransitiveOn r n := ∀ i j k, i < n → j < n → k < n → r i j → r j k → r i k`
//! - `Nat.EquivalenceOn r n := ReflexiveOn r n ∧ SymmetricOn r n ∧ TransitiveOn r n`
//!   (right-nested `And`, matching `finite.rs`'s own `And bound eqk` packing
//!   convention).
//! - `Nat.eq_equivalence_on : ∀ n, EquivalenceOn (Eq Nat) n` — equality is an
//!   equivalence relation, the canonical worked instance.
//! - `Nat.modEq_equivalence_on : ∀ m n, EquivalenceOn (Nat.modEq m) n` —
//!   congruence mod `m` is an equivalence relation. This is the connection to
//!   the `modular-arithmetic` curriculum node: `Nat.modEq` (`nat_prelude.rs`)
//!   already carries unbounded `mod_eq_refl`/`mod_eq_symm`/`mod_eq_trans`
//!   theorems (built for the 40-row `modular-arithmetic` nursery family), so
//!   this is a direct instantiation of those three at a bound, not new
//!   arithmetic.
//! - `Nat.BijectiveOn f n := InjectiveOn f n ∧ MapsInto f n ∧ SurjectiveOn f n`
//!   and `Nat.bijective_of_injective_on : ∀ n f, InjectiveOn f n →
//!   MapsInto f n → BijectiveOn f n` — **not** a new proof: `SurjectiveOn`
//!   already exists under that exact name, and the pigeonhole principle
//!   `Nat.injective_on_imp_surjective_on` (`finite.rs`) already proves exactly
//!   the missing conjunct, so this is packaging, applied directly.
//! - `Nat.comp f g := fun x => f (g x)` and `Nat.injective_on_comp : ∀ n f g,
//!   MapsInto g n → InjectiveOn g n → InjectiveOn f n →
//!   InjectiveOn (comp f g) n` — composition of self-maps preserves
//!   injectivity on the same bound. No case split: `MapsInto g n` puts `g i`,
//!   `g j` inside `f`'s injective domain, so `f`'s injectivity collapses
//!   `g i = g j` and `g`'s injectivity then collapses `i = j`.
//!
//! ## Status
//!
//! All of the above are declared here and axiom-free.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat → Nat → Prop`, the carrier type every relation in this module has.
fn rel_ty(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let inner = d.arrow(nat, prop);
    d.arrow(nat, inner)
}

/// Declare `Nat.ReflexiveOn`, `Nat.SymmetricOn`, `Nat.TransitiveOn`, and
/// `Nat.EquivalenceOn` — plain `Prop`-valued definitions over an arbitrary
/// `r : Nat → Nat → Prop`, bounded on `n`.
///
/// # Errors
///
/// Returns the kernel's rejection if any generated definition does not
/// type-check or a name is already taken.
pub(super) fn declare_relation_properties(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let carrier = rel_ty(d);

    // ReflexiveOn r n := ∀ i, i < n → r i i.
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);

        let hyp = d.lt(i, n);
        let rii = d.apply(r, &[i, i]);
        let inner = d.arrow(hyp, rii);
        let body = d.pi_fv(i_fv, nat, inner);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(r_fv, carrier, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(carrier, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.reflexive_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // SymmetricOn r n := ∀ i j, i < n → j < n → r i j → r j i.
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);

        let rij = d.apply(r, &[i, j]);
        let rji = d.apply(r, &[j, i]);
        let step_rel = d.arrow(rij, rji);
        let hyp_j = d.lt(j, n);
        let step_j = d.arrow(hyp_j, step_rel);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_j);
        let body = {
            let with_j = d.pi_fv(j_fv, nat, inner);
            d.pi_fv(i_fv, nat, with_j)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(r_fv, carrier, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(carrier, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.symmetric_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // TransitiveOn r n := ∀ i j k, i < n → j < n → k < n → r i j → r j k → r i k.
    {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let rij = d.apply(r, &[i, j]);
        let rjk = d.apply(r, &[j, k]);
        let rik = d.apply(r, &[i, k]);
        let step_jk = d.arrow(rjk, rik);
        let step_ij = d.arrow(rij, step_jk);
        let hyp_k = d.lt(k, n);
        let step_k = d.arrow(hyp_k, step_ij);
        let hyp_j = d.lt(j, n);
        let step_j = d.arrow(hyp_j, step_k);
        let hyp_i = d.lt(i, n);
        let inner = d.arrow(hyp_i, step_j);
        let body = {
            let with_k = d.pi_fv(k_fv, nat, inner);
            let with_j = d.pi_fv(j_fv, nat, with_k);
            d.pi_fv(i_fv, nat, with_j)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(r_fv, carrier, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(carrier, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.transitive_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // EquivalenceOn r n := ReflexiveOn r n ∧ (SymmetricOn r n ∧ TransitiveOn r n).
    {
        let logic = p.logic;
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let refl = d.const_app(p.reflexive_on, &[r, n]);
        let symm = d.const_app(p.symmetric_on, &[r, n]);
        let trans = d.const_app(p.transitive_on, &[r, n]);
        let inner = d.const_app(logic.and, &[symm, trans]);
        let body = d.const_app(logic.and, &[refl, inner]);
        let value = {
            let with_n = d.lam_fv(n_fv, nat, body);
            d.lam_fv(r_fv, carrier, with_n)
        };
        let ty = {
            let over_n = d.arrow(nat, prop);
            d.arrow(carrier, over_n)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.equivalence_on,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    Ok(())
}

/// Declare `Nat.eq_equivalence_on : ∀ n, EquivalenceOn (Eq Nat) n` —
/// equality is an equivalence relation on every bound.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_eq_equivalence_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.eq_equivalence_on, 1, &|d, values| {
        let n = values[0];
        let nat = d.nat_ty();
        let logic = p.logic;
        let one = d.level_one();
        let eq_const = d.kernel().const_(logic.eq, vec![one]);
        let eq_rel = d.apply(eq_const, &[nat]); // Eq Nat : Nat -> Nat -> Prop

        let stmt = d.const_app(p.equivalence_on, &[eq_rel, n]);

        // ReflexiveOn (Eq Nat) n.
        let refl_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let h_fv = d.fresh_fvar();
            let hyp_ty = d.lt(i, n);
            let body = d.refl(i);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        // SymmetricOn (Eq Nat) n.
        let symm_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hi_fv = d.fresh_fvar();
            let hj_fv = d.fresh_fvar();
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let heq_ty = d.eq(i, j);
            let body = d.symm(i, j, heq);
            let with_heq = d.lam_fv(heq_fv, heq_ty, body);
            let hj_ty = d.lt(j, n);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
            let hi_ty = d.lt(i, n);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_j = d.lam_fv(j_fv, nat, with_hi);
            d.lam_fv(i_fv, nat, with_j)
        };
        // TransitiveOn (Eq Nat) n.
        let trans_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hi_fv = d.fresh_fvar();
            let hj_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let h2_ty = d.eq(j, k);
            let body = d.trans(i, j, k, h1, h2);
            let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
            let h1_ty = d.eq(i, j);
            let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
            let hk_ty = d.lt(k, n);
            let with_hk = d.lam_fv(hk_fv, hk_ty, with_h1);
            let hj_ty = d.lt(j, n);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_hk);
            let hi_ty = d.lt(i, n);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_k = d.lam_fv(k_fv, nat, with_hi);
            let with_j = d.lam_fv(j_fv, nat, with_k);
            d.lam_fv(i_fv, nat, with_j)
        };

        let refl_ty = d.const_app(p.reflexive_on, &[eq_rel, n]);
        let symm_ty = d.const_app(p.symmetric_on, &[eq_rel, n]);
        let trans_ty = d.const_app(p.transitive_on, &[eq_rel, n]);
        let inner_ty = d.const_app(logic.and, &[symm_ty, trans_ty]);
        let inner_and = d.const_app(
            logic.and_intro,
            &[symm_ty, trans_ty, symm_proof, trans_proof],
        );
        let proof = d.const_app(logic.and_intro, &[refl_ty, inner_ty, refl_proof, inner_and]);

        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.modEq_equivalence_on : ∀ m n, EquivalenceOn (Nat.modEq m) n` —
/// congruence mod `m` is an equivalence relation on every bound. Direct from
/// the already-proved unbounded `mod_eq_refl`/`mod_eq_symm`/`mod_eq_trans`;
/// the bound hypotheses are threaded through but never used by the underlying
/// facts, exactly as `Nat.modEq` itself never needed a bound.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_mod_eq_equivalence_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_equivalence_on, 2, &|d, values| {
        let m = values[0];
        let n = values[1];
        let nat = d.nat_ty();
        let logic = p.logic;
        let mod_eq_rel = d.const_app(p.mod_eq, &[m]); // Nat.modEq m : Nat -> Nat -> Prop

        let stmt = d.const_app(p.equivalence_on, &[mod_eq_rel, n]);

        let refl_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let h_fv = d.fresh_fvar();
            let hyp_ty = d.lt(i, n);
            let body = d.lemma(p.mod_eq_refl, &[m, i]);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, with_h)
        };
        let symm_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let hi_fv = d.fresh_fvar();
            let hj_fv = d.fresh_fvar();
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let heq_ty = d.mod_eq(m, i, j);
            let body = d.lemma(p.mod_eq_symm, &[m, i, j, heq]);
            let with_heq = d.lam_fv(heq_fv, heq_ty, body);
            let hj_ty = d.lt(j, n);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
            let hi_ty = d.lt(i, n);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_j = d.lam_fv(j_fv, nat, with_hi);
            d.lam_fv(i_fv, nat, with_j)
        };
        let trans_proof = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hi_fv = d.fresh_fvar();
            let hj_fv = d.fresh_fvar();
            let hk_fv = d.fresh_fvar();
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let h2_ty = d.mod_eq(m, j, k);
            let body = d.lemma(p.mod_eq_trans, &[m, i, j, k, h1, h2]);
            let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
            let h1_ty = d.mod_eq(m, i, j);
            let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
            let hk_ty = d.lt(k, n);
            let with_hk = d.lam_fv(hk_fv, hk_ty, with_h1);
            let hj_ty = d.lt(j, n);
            let with_hj = d.lam_fv(hj_fv, hj_ty, with_hk);
            let hi_ty = d.lt(i, n);
            let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
            let with_k = d.lam_fv(k_fv, nat, with_hi);
            let with_j = d.lam_fv(j_fv, nat, with_k);
            d.lam_fv(i_fv, nat, with_j)
        };

        let refl_ty = d.const_app(p.reflexive_on, &[mod_eq_rel, n]);
        let symm_ty = d.const_app(p.symmetric_on, &[mod_eq_rel, n]);
        let trans_ty = d.const_app(p.transitive_on, &[mod_eq_rel, n]);
        let inner_ty = d.const_app(logic.and, &[symm_ty, trans_ty]);
        let inner_and = d.const_app(
            logic.and_intro,
            &[symm_ty, trans_ty, symm_proof, trans_proof],
        );
        let proof = d.const_app(logic.and_intro, &[refl_ty, inner_ty, refl_proof, inner_and]);

        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.BijectiveOn f n := InjectiveOn f n ∧ MapsInto f n ∧
/// SurjectiveOn f n` — right-nested `And`, matching `EquivalenceOn`'s own
/// packing convention.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_bijective_on(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let logic = p.logic;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let inj = d.const_app(p.injective_on, &[f, n]);
    let maps = d.const_app(p.maps_into, &[f, n]);
    let surj = d.const_app(p.surjective_on, &[f, n]);
    let inner = d.const_app(logic.and, &[maps, surj]);
    let body = d.const_app(logic.and, &[inj, inner]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, prop);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.bijective_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(())
}

/// `∀ f, InjectiveOn f n → MapsInto f n → BijectiveOn f n`.
fn bijective_of_injective_on_motive(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let inj = d.const_app(p.injective_on, &[f, n]);
    let maps = d.const_app(p.maps_into, &[f, n]);
    let bij = d.const_app(p.bijective_on, &[f, n]);
    let inner = d.arrow(maps, bij);
    let body = d.arrow(inj, inner);
    d.pi_fv(f_fv, fn_ty, body)
}

/// Declare `Nat.bijective_of_injective_on : ∀ n f, InjectiveOn f n →
/// MapsInto f n → BijectiveOn f n` — packaging, not new mathematics: the
/// missing conjunct is exactly `Nat.injective_on_imp_surjective_on`
/// (`finite.rs`)'s conclusion, applied directly.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_bijective_of_injective_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.bijective_of_injective_on, 1, &|d, values| {
        let n = values[0];
        let stmt = bijective_of_injective_on_motive(d, &p, n);

        let logic = p.logic;
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let inj_ty = d.const_app(p.injective_on, &[f, n]);
        let inj_fv = d.fresh_fvar();
        let inj = d.kernel().fvar(inj_fv);
        let maps_ty = d.const_app(p.maps_into, &[f, n]);
        let maps_fv = d.fresh_fvar();
        let maps = d.kernel().fvar(maps_fv);

        let surj_ty = d.const_app(p.surjective_on, &[f, n]);
        let surj_proof = d.lemma(p.injective_on_imp_surjective_on, &[n, f, inj, maps]);

        let inner_ty = d.const_app(logic.and, &[maps_ty, surj_ty]);
        let inner_and = d.const_app(logic.and_intro, &[maps_ty, surj_ty, maps, surj_proof]);
        let bij_proof = d.const_app(logic.and_intro, &[inj_ty, inner_ty, inj, inner_and]);

        let with_maps = d.lam_fv(maps_fv, maps_ty, bij_proof);
        let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
        let proof = d.lam_fv(f_fv, fn_ty, with_inj);

        (stmt, proof)
    })?;
    Ok(())
}

/// Declare `Nat.comp f g := fun x => f (g x)` — plain functional composition,
/// order matching mathematical convention `(f ∘ g)(x) = f(g(x))`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_comp(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let gx = d.apply(g, &[x]);
    let fgx = d.apply(f, &[gx]);
    let value = {
        let with_x = d.lam_fv(x_fv, nat, fgx);
        let with_g = d.lam_fv(g_fv, fn_ty, with_x);
        d.lam_fv(f_fv, fn_ty, with_g)
    };
    let ty = {
        let over_x = d.arrow(nat, nat);
        let over_g = d.arrow(fn_ty, over_x);
        d.arrow(fn_ty, over_g)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.comp,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(())
}

/// `∀ f g, MapsInto g n → InjectiveOn g n → InjectiveOn f n →
/// InjectiveOn (comp f g) n`.
fn injective_on_comp_motive(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let maps_g = d.const_app(p.maps_into, &[g, n]);
    let inj_g = d.const_app(p.injective_on, &[g, n]);
    let inj_f = d.const_app(p.injective_on, &[f, n]);
    let comp_fg = d.const_app(p.comp, &[f, g]);
    let inj_comp = d.const_app(p.injective_on, &[comp_fg, n]);

    let inner2 = d.arrow(inj_f, inj_comp);
    let inner1 = d.arrow(inj_g, inner2);
    let body = d.arrow(maps_g, inner1);
    let with_g = d.pi_fv(g_fv, fn_ty, body);
    d.pi_fv(f_fv, fn_ty, with_g)
}

/// Declare `Nat.injective_on_comp : ∀ n f g, MapsInto g n → InjectiveOn g n →
/// InjectiveOn f n → InjectiveOn (comp f g) n` — no case split: `MapsInto g n`
/// puts `g i`, `g j` inside `f`'s injective domain, so `f`'s injectivity
/// collapses `g i = g j` and `g`'s injectivity then collapses `i = j`.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated declaration does not
/// type-check or the name is already taken.
pub(super) fn declare_injective_on_comp(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.injective_on_comp, 1, &|d, values| {
        let n = values[0];
        let stmt = injective_on_comp_motive(d, &p, n);

        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);

        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let maps_g_ty = d.const_app(p.maps_into, &[g, n]);
        let maps_g_fv = d.fresh_fvar();
        let maps_g = d.kernel().fvar(maps_g_fv);
        let inj_g_ty = d.const_app(p.injective_on, &[g, n]);
        let inj_g_fv = d.fresh_fvar();
        let inj_g = d.kernel().fvar(inj_g_fv);
        let inj_f_ty = d.const_app(p.injective_on, &[f, n]);
        let inj_f_fv = d.fresh_fvar();
        let inj_f = d.kernel().fvar(inj_f_fv);

        let comp_fg = d.const_app(p.comp, &[f, g]);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let comp_i = d.apply(comp_fg, &[i]);
        let comp_j = d.apply(comp_fg, &[j]);
        let heq_ty = d.eq(comp_i, comp_j);

        let gi = d.apply(g, &[i]);
        let gj = d.apply(g, &[j]);
        let gi_lt_n = d.apply(maps_g, &[i, hi]);
        let gj_lt_n = d.apply(maps_g, &[j, hj]);

        // `heq : Eq Nat (comp f g i) (comp f g j)` is defeq (via `comp`'s
        // definitional unfolding) to `Eq Nat (f (g i)) (f (g j))`, exactly
        // what `inj_f` expects at `gi`, `gj`.
        let gi_eq_gj = d.apply(inj_f, &[gi, gj, gi_lt_n, gj_lt_n, heq]);
        let i_eq_j = d.apply(inj_g, &[i, j, hi, hj, gi_eq_gj]);

        let with_heq = d.lam_fv(heq_fv, heq_ty, i_eq_j);
        let hj_ty = d.lt(j, n);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let hi_ty = d.lt(i, n);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        let inj_comp_proof = d.lam_fv(i_fv, nat, with_j);

        let with_inj_f = d.lam_fv(inj_f_fv, inj_f_ty, inj_comp_proof);
        let with_inj_g = d.lam_fv(inj_g_fv, inj_g_ty, with_inj_f);
        let with_maps_g = d.lam_fv(maps_g_fv, maps_g_ty, with_inj_g);
        let with_g = d.lam_fv(g_fv, fn_ty, with_maps_g);
        let proof = d.lam_fv(f_fv, fn_ty, with_g);

        (stmt, proof)
    })?;
    Ok(())
}
