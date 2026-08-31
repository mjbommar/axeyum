//! Two more `Nat.size` `ml430` mirrors: `size_one` and `size_eq_zero`. A NEW
//! module rather than an addition to `binary.rs` (already the file that owns
//! `Nat.size`/`sizeAux`'s own dense definition-plus-boundary set).
//!
//! `size_one` is free by construction: `size 1 ≡ sizeAux 1 1`, and
//! `nat_prelude_tests::size_computes_binary_digit_counts` already confirms
//! (as a `def_eq` check) that this reduces all the way to the literal `1` --
//! `sizeAux`'s step row is `if beq n 0 then 0 else succ (sizeAux f (n/2))`,
//! and at `fuel=1,n=1` that is `succ (sizeAux 0 (1/2)) = succ (sizeAux 0 0) =
//! succ 0 = 1`, every step delta+iota. So the statement is provable by
//! `Eq.refl` with no lemma at all.
//!
//! `size_eq_zero` routes through [`NatPrelude::lt_pow_size`] (`n < 2^(size
//! n)`, already proved in `binary.rs`): if `size n = 0` then `n < 2^0 = 1`
//! (`pow_zero` is itself `refl`), giving `n <= 0` via
//! [`NatPrelude::le_of_lt_succ`], hence `n = 0` via
//! [`NatPrelude::le_antisymm`] against [`NatPrelude::zero_le`]. The converse
//! is `size_zero` transported along the hypothesis.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;

/// `Nat.size_one : Eq (size 1) 1` -- `refl`, per the module doc.
pub(super) fn declare_size_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.size_one, 0, &|d, _v| {
        let one = d.num(1);
        let lhs = d.const_app(p.size, &[one]);
        (d.eq(lhs, one), d.refl(one))
    })?;
    Ok(())
}

/// `Nat.size_eq_zero : ∀ n, Iff (Eq (size n) 0) (Eq n 0)`.
pub(super) fn declare_size_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero = d.zero();
    let sz = d.const_app(p.size, &[n]);
    let lhs_ty = d.eq(sz, zero);
    let rhs_ty = d.eq(n, zero);

    // forward : size n = 0 -> n = 0
    let forward = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let lt_proof = d.lemma(p.lt_pow_size, &[n]); // Lt n (pow 2 (size n))
        let motive = d.eq_motive(sz, &|d, x| {
            let two = d.num(2);
            let px = d.pow(two, x);
            d.lt(n, px)
        });
        let lt_n_pow_zero = d.transport(sz, motive, lt_proof, zero, h);
        // lt_n_pow_zero : Lt n (pow 2 zero), defeq Lt n 1 = Lt n (succ zero)
        // (`pow_zero` is refl).
        let zero2 = d.zero();
        let le_n_0 = d.lemma(p.le_of_lt_succ, &[n, zero2, lt_n_pow_zero]);
        let zero_le_n = d.lemma(p.zero_le, &[n]);
        let eq_n_0 = d.lemma(p.le_antisymm, &[n, zero2, le_n_0, zero_le_n]);
        d.lam_fv(h_fv, lhs_ty, eq_n_0)
    };

    // reverse : n = 0 -> size n = 0
    let reverse = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sz_zero = d.const_app(p.size, &[zero]);
        let congr_eq = d.congr(n, zero, h, &|d, x| d.const_app(p.size, &[x]));
        let size_zero_eq = d.lemma(p.size_zero, &[]);
        let (_e, combined) = d.chain(sz, &[(sz_zero, congr_eq), (zero, size_zero_eq)]);
        d.lam_fv(h_fv, rhs_ty, combined)
    };

    let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
    let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, forward, reverse]);

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.size_eq_zero, ty, value)
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_size_extra_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_size_one(d, p)?;
    declare_size_eq_zero(d, p)?;
    Ok(())
}
