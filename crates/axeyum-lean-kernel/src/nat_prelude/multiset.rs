//! `Nat.Multiset` — a multiplicity carrier, and **uniqueness** of prime
//! factorization stated as multiplicity agreement.
//!
//! # What this closes
//!
//! `docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`
//! §6 concedes that uniqueness of prime factorization "is not expressible here
//! at all": this kernel has no `List`, no `Finset`, no quotient by permutation,
//! so "the multiset of prime factors" cannot be written down and two
//! factorizations cannot be compared. `factorization.rs` says the same in its
//! own module doc, and it is right about the route it takes — a factorization
//! there is an anonymous `(k, f)` pair inside an `Exists`, and two of those can
//! only be compared by exhibiting a permutation.
//!
//! The concession is about a REPRESENTATION, not about the theorem. A multiset
//! over `Nat` is exactly a multiplicity function `Nat → Nat` that is eventually
//! zero, and "eventually zero" is witnessed by a `Nat` bound. Both are
//! expressible here today. So the carrier below is
//!
//! ```text
//! inductive Nat.Multiset : Type
//!   | mk : (Nat → Nat) → Nat → Nat.Multiset
//! ```
//!
//! — a raw multiplicity function together with a bound — and `count`
//! **truncates at the bound**:
//!
//! ```text
//! Nat.Multiset.count m p := if p < bound m then raw m p else 0
//! ```
//!
//! Truncating in the definition rather than carrying a well-formedness
//! hypothesis is the whole reason this stays cheap.
//! `Nat.Multiset.count_eq_zero_of_bound_le` is then a THEOREM about every
//! `Multiset` with no side condition, so nothing downstream ever has to thread
//! an "is bounded" premise, and `Nat.Multiset.mk` needs no proof obligation to
//! apply. The cost is that `raw` is not observable above the bound, which is
//! correct: two multisets that agree below their bounds and disagree above them
//! are the same multiset.
//!
//! What this carrier deliberately does NOT provide, and does not need:
//!
//! - **No permutation quotient.** Order is never represented, so there is
//!   nothing to quotient by. This is why no `propext`/`Quot.sound` appears
//!   anywhere below and the axiom footprint stays empty.
//! - **No `Finset`.** The support is bounded by construction, and every fold is
//!   `Nat.prodRange`/`Nat.sumRange` over `[0, bound)` — the machinery this
//!   prelude already has.
//! - **No extensional equality of multisets.** `Nat.Multiset.beq` is a
//!   `Bool`-valued bounded loop, and `Nat.Multiset.beq_refl`/`beq_comm` are the
//!   only two facts claimed about it. Two multisets with equal counts but
//!   different `raw` functions above the bound are NOT `Eq` at type
//!   `Nat.Multiset`, and nothing here pretends otherwise; the uniqueness
//!   theorem is stated at the level of counts for exactly that reason.
//!
//! # The three statements
//!
//! `Nat.Multiset.prod m := prodRange (fun q => q ^ count m q) (bound m)`.
//!
//! 1. `Nat.Multiset.pow_count_dvd_prod : ∀ m p, dvd (p ^ count m p) (prod m)` —
//!    no hypotheses at all. Below the bound it is the single factor
//!    `p ^ count m p` of the product; at or above it `count m p = 0` and
//!    `p ^ 0 = 1`.
//! 2. `Nat.Multiset.not_pow_succ_count_dvd_prod` — with `p` prime and every
//!    element of `m` prime, `p ^ (count m p + 1)` does NOT divide `prod m`.
//! 3. `Nat.Multiset.count_eq_of_prod_eq` — **uniqueness**: two prime-supported
//!    multisets with the same product have the same multiplicity everywhere.
//!
//! (1) and (2) together say `count m p` is the `p`-adic valuation of `prod m`
//! (this prelude's `Nat.valuationAt p (prod m) (count m p)`), and a valuation is
//! determined by the value it is a valuation of — which is (3).
//!
//! # Why this is the honest constructive form
//!
//! ADR-0603's graded statement family: (3) is row 1, the general constructive
//! form. It does not mention "the" factorization of anything, and it needs no
//! existence theorem — `Nat.exists_prime_factorization` (`factorization.rs`)
//! supplies existence in its own shape, and the two compose without either
//! having to be restated in the other's representation.
//!
//! # Proof of (2), which is the only hard one
//!
//! Everything reduces to two inductions over the bound, plus one reusable
//! prime-power lemma. Write `f q := q ^ count m q`, so
//! `prod m = prodRange f (bound m)`.
//!
//! - `Nat.not_dvd_prod_range_of_le` (`A`): if `k ≤ p` then
//!   `¬ p ∣ prodRange f k` — `p` is not among the factors below `k`. Induction
//!   on `k`. At `succ j` the new factor is `j ^ g j`; if `g j = 0` it is `1` and
//!   the induction hypothesis is the whole answer, and otherwise `j` is prime,
//!   so `p ∣ j ^ g j` forces `p ∣ j` (`prime_dvd_of_dvd_pow`) and then `p = j`,
//!   contradicting `j < p`. The `g j = 0` branch is not an optimisation: it is
//!   what rules out `j = 0`, where `f 0` would be `0` and every number would
//!   divide the product.
//! - `Nat.not_pow_succ_dvd_prod_range_of_lt` (`B`): if `p < k` then
//!   `¬ p ^ (g p + 1) ∣ prodRange f k`. Induction on `k`, splitting `p < succ j`
//!   into `p = j` and `p < j`.
//!   - `p = j`: the product is `X * p ^ c` with `X = prodRange f p`, and
//!     `p ^ (c+1) = p ^ c * p`, so cancelling `p ^ c` (positive) leaves
//!     `p ∣ X`, which `A` at `k := p` refutes.
//!   - `p < j`: `p ∤ j ^ g j` by the same argument as in `A`, and
//!     `Nat.prime_pow_dvd_of_dvd_mul_of_not_dvd` moves the whole prime power
//!     across that coprime factor onto `X`, where the induction hypothesis
//!     refutes it.
//!
//! `Nat.prime_pow_dvd_of_dvd_mul_of_not_dvd : p prime → ¬ p ∣ b → p^c ∣ a*b →
//! p^c ∣ a` is itself an induction on `c` using only `euclid_lemma` and
//! left-cancellation — no coprimality API, and no `Coprime` on prime POWERS,
//! which this prelude does not have.
//!
//! # House rules observed here
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! exactly as `factorization.rs` documents. Every numeral built by the tests is
//! tiny on purpose: this prelude's numerals are unary `succ` towers and cost is
//! superlinear in the largest magnitude FORMED.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

// ---------------------------------------------------------------------------
// Term builders for the carrier.
// ---------------------------------------------------------------------------

/// The carrier constant `Nat.Multiset`.
fn multiset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.multiset, vec![])
}

/// `Nat.Multiset.mk f b`.
pub(super) fn mk_multiset(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.multiset_mk, &[f, b])
}

/// `Nat.Multiset.raw m`, the untruncated multiplicity function.
pub(super) fn ms_raw(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    d.const_app(p.multiset_raw, &[m])
}

/// `Nat.Multiset.bound m`.
pub(super) fn ms_bound(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    d.const_app(p.multiset_bound, &[m])
}

/// `Nat.Multiset.count m x`.
pub(super) fn ms_count(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, x: ExprId) -> ExprId {
    d.const_app(p.multiset_count, &[m, x])
}

/// `Nat.Multiset.prod m`.
pub(super) fn ms_prod(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    d.const_app(p.multiset_prod, &[m])
}

/// `fun q => q ^ g q` — the factor function `Nat.Multiset.prod` folds.
pub(super) fn pow_factor(d: &mut NatDev<'_>, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let gq = d.apply(g, &[q]);
    let body = d.pow(q, gq);
    d.lam_fv(q_fv, nat, body)
}

/// `Nat.prodRange f k`.
pub(super) fn prod_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.prod_range, &[f, k])
}

/// Computational `if condition then on_true else on_false` at `Bool` — the
/// `Bool`-valued twin of [`NatOps::bool_select_nat`], needed by
/// `Nat.Multiset.eqBelow`'s accumulator (this prelude's logic package has no
/// `Bool.and`).
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

// ---------------------------------------------------------------------------
// The carrier, the projections, and the constructions over them.
// ---------------------------------------------------------------------------

/// `Nat.Multiset`, `Nat.Multiset.mk`, the two projections, and every
/// construction built on them.
fn declare_carrier(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let fn_ty = d.arrow(nat, nat);

    // Multiset : Type 0, with mk : (Nat -> Nat) -> Nat -> Multiset.
    {
        let mk_ty = {
            let concl = d.kernel().const_(p.multiset, vec![]);
            let inner = d.arrow(nat, concl);
            d.arrow(fn_ty, inner)
        };
        d.kernel()
            .add_inductive(p.multiset, &[], 0, type0, &[(p.multiset_mk, mk_ty)])?;
    }

    let ms = multiset_ty(d, &p);

    // raw : Multiset -> Nat -> Nat
    //     := fun m => Multiset.rec.{1} (fun _ => Nat -> Nat) (fun f _ => f) m
    {
        let motive = d.kernel().lam(anon, ms, fn_ty, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let b_fv = d.fresh_fvar();
            let inner = d.lam_fv(b_fv, nat, f);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let rec = d.kernel().const_(p.multiset_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, m]);
        let value = d.lam_fv(m_fv, ms, body);
        let ty = d.arrow(ms, fn_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_raw,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // bound : Multiset -> Nat
    //       := fun m => Multiset.rec.{1} (fun _ => Nat) (fun _ b => b) m
    {
        let motive = d.kernel().lam(anon, ms, nat, BinderInfo::Default);
        let minor = {
            let f_fv = d.fresh_fvar();
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let inner = d.lam_fv(b_fv, nat, b);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let rec = d.kernel().const_(p.multiset_rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, m]);
        let value = d.lam_fv(m_fv, ms, body);
        let ty = d.arrow(ms, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_bound,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // count : Multiset -> Nat -> Nat
    //       := fun m x => if ble (succ x) (bound m) then raw m x else 0
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let succ_x = d.succ(x);
        let b = ms_bound(d, &p, m);
        let cond = d.ble(succ_x, b);
        let raw_m = ms_raw(d, &p, m);
        let raw_at = d.apply(raw_m, &[x]);
        let zero = d.zero();
        let body = d.bool_select_nat(cond, raw_at, zero);
        let value = {
            let inner = d.lam_fv(x_fv, nat, body);
            d.lam_fv(m_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(nat, nat);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_count,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })?;
    }

    // zero : Multiset := mk (fun _ => 0) 0
    {
        let zero = d.zero();
        let const_zero = {
            let q_fv = d.fresh_fvar();
            let z = d.zero();
            d.lam_fv(q_fv, nat, z)
        };
        let value = mk_multiset(d, &p, const_zero, zero);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_zero,
            uparams: vec![],
            ty: ms,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // singleton : Nat -> Multiset
    //           := fun a => mk (fun q => if beq q a then 1 else 0) (succ a)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let f = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let cond = d.beq(q, a);
            let one_lit = d.num(1);
            let zero = d.zero();
            let body = d.bool_select_nat(cond, one_lit, zero);
            d.lam_fv(q_fv, nat, body)
        };
        let succ_a = d.succ(a);
        let built = mk_multiset(d, &p, f, succ_a);
        let value = d.lam_fv(a_fv, nat, built);
        let ty = d.arrow(nat, ms);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_singleton,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // add : Multiset -> Multiset -> Multiset
    //     := fun m1 m2 => mk (fun q => count m1 q + count m2 q)
    //                        (bound m1 + bound m2)
    //
    // The bound is the SUM, not the maximum. `Nat.max` lives in the `Max`
    // namespace here (`minmax.rs`, `Max.max`/`Nat.instMax`) and its comparison
    // lemmas are stated there; `Nat.add` needs none of that, is at least as
    // large as the maximum, and counts above either bound are already `0`, so
    // `count_add` holds unchanged. Nothing downstream reads the bound of a sum.
    {
        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let f = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let c1 = ms_count(d, &p, m1, q);
            let c2 = ms_count(d, &p, m2, q);
            let body = d.add(c1, c2);
            d.lam_fv(q_fv, nat, body)
        };
        let b1 = ms_bound(d, &p, m1);
        let b2 = ms_bound(d, &p, m2);
        let b = d.add(b1, b2);
        let built = mk_multiset(d, &p, f, b);
        let value = {
            let inner = d.lam_fv(m2_fv, ms, built);
            d.lam_fv(m1_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(ms, ms);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_add,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // Mem : Multiset -> Nat -> Prop := fun m x => Lt 0 (count m x)
    {
        let zero_level = d.kernel().level_zero();
        let prop = d.kernel().sort(zero_level);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let c = ms_count(d, &p, m, x);
        let zero = d.zero();
        let body = d.lt(zero, c);
        let value = {
            let inner = d.lam_fv(x_fv, nat, body);
            d.lam_fv(m_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(nat, prop);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_mem,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // prod : Multiset -> Nat
    //      := fun m => prodRange (fun q => q ^ count m q) (bound m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let g = d.const_app(p.multiset_count, &[m]);
        let f = pow_factor(d, g);
        let b = ms_bound(d, &p, m);
        let body = prod_range(d, &p, f, b);
        let value = d.lam_fv(m_fv, ms, body);
        let ty = d.arrow(ms, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_prod,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // card : Multiset -> Nat := fun m => sumRange (count m) (bound m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let g = d.const_app(p.multiset_count, &[m]);
        let b = ms_bound(d, &p, m);
        let body = d.sum_range(g, b);
        let value = d.lam_fv(m_fv, ms, body);
        let ty = d.arrow(ms, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_card,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // eqBelow : (Nat -> Nat) -> (Nat -> Nat) -> Nat -> Bool
    //   := fun f g k => Nat.rec.{1} (fun _ => Bool) true
    //                     (fun j ih => if beq (f j) (g j) then ih else false) k
    {
        let bool_ty = d.bool_ty();
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);
        let base = d.bool_true();
        let step = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let cond = d.beq(fj, gj);
            let false_val = d.bool_false();
            let body = bool_select_bool(d, &p, cond, ih, false_val);
            let inner = d.lam_fv(ih_fv, bool_ty, body);
            d.lam_fv(j_fv, nat, inner)
        };
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base, step, k]);
        let value = {
            let with_k = d.lam_fv(k_fv, nat, body);
            let with_g = d.lam_fv(g_fv, fn_ty, with_k);
            d.lam_fv(f_fv, fn_ty, with_g)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            let with_g = d.arrow(fn_ty, inner);
            d.arrow(fn_ty, with_g)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_eq_below,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // beq : Multiset -> Multiset -> Bool
    //     := fun m1 m2 => eqBelow (count m1) (count m2) (bound m1 + bound m2)
    {
        let bool_ty = d.bool_ty();
        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let c1 = d.const_app(p.multiset_count, &[m1]);
        let c2 = d.const_app(p.multiset_count, &[m2]);
        let b1 = ms_bound(d, &p, m1);
        let b2 = ms_bound(d, &p, m2);
        let b = d.add(b1, b2);
        let body = d.const_app(p.multiset_eq_below, &[c1, c2, b]);
        let value = {
            let inner = d.lam_fv(m2_fv, ms, body);
            d.lam_fv(m1_fv, ms, inner)
        };
        let ty = {
            let inner = d.arrow(ms, bool_ty);
            d.arrow(ms, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.multiset_beq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    Ok(())
}

/// Declare the whole `Nat.Multiset` package.
///
/// # Errors
///
/// Returns the kernel's rejection if any generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_multiset_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_carrier(d, p)?;
    Ok(())
}
