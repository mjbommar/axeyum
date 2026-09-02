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
use super::finite::{select_nat_false, select_nat_true};
use super::helpers::{transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_lt_or_ge};
use super::primes::prime_condition;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

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

// ---------------------------------------------------------------------------
// Local proof combinators. Per this development's per-file-copy convention
// (`divisibility.rs`, `lcm_gcd_lemmas.rs`, `dvd_mul_split.rs`, … each carry
// their own `dvd_intro`/`dvd_elim`/`or_cases`).
// ---------------------------------------------------------------------------

/// `Not a`, spelled as the arrow this prelude's proofs actually build.
fn not_ty(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    d.arrow(a, false_ty)
}

/// `False.rec` into `target` from a proof of `False`.
fn from_false(d: &mut NatDev<'_>, p: &NatPrelude, false_proof: ExprId, target: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Or.rec` with a non-dependent motive.
#[allow(clippy::too_many_arguments)]
fn or_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let split_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, split_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
}

/// `witness : Nat`, `eq_proof : Eq n (mul a witness) ⊢ dvd a n`.
fn dvd_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Eliminate `dvd_hyp : dvd divisor dividend`, continuing with the witness `q`
/// and `eq_proof : Eq dividend (mul divisor q)` to build a proof of `goal`
/// (which must not mention `q`).
fn dvd_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

/// Eliminate `hyp : Exists Nat predicate`, where `prop_at` rebuilds the
/// predicate's body at a witness.
#[allow(clippy::too_many_arguments)]
fn exists_elim_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    predicate: ExprId,
    prop_at: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    goal: ExprId,
    hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let ex_ty = {
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(ex, &[nat, predicate])
    };
    let motive = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
    let minor = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let prop_ty = prop_at(d, w);
        let hw_fv = d.fresh_fvar();
        let hw = d.kernel().fvar(hw_fv);
        let body = continuation(d, w, hw);
        let with_hw = d.lam_fv(hw_fv, prop_ty, body);
        d.lam_fv(w_fv, nat, with_hw)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, hyp])
}

/// `k_pos : Le 1 k`, `dvd_hyp : dvd (mul k a) (mul k b) ⊢ dvd a b`. Local copy
/// of `lcm_gcd_lemmas.rs`'s private helper of the same name and signature.
fn dvd_cancel_left_of_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    dvd_hyp: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let kb = d.mul(k, b);
    let goal = d.dvd(a, b);
    dvd_elim(d, &p, ka, kb, goal, dvd_hyp, &|d, q, eq_proof| {
        let ka_q = d.mul(ka, q);
        let aq = d.mul(a, q);
        let k_aq = d.mul(k, aq);
        let assoc = d.lemma(p.mul_assoc, &[k, a, q]);
        let (_, kb_eq_k_aq) = d.chain(kb, &[(ka_q, eq_proof), (k_aq, assoc)]);
        let cancelled = d.lemma(p.mul_left_cancel_of_pos, &[k, b, aq, k_pos, kb_eq_k_aq]);
        dvd_intro(d, &p, a, b, q, cancelled)
    })
}

/// Declare `theorem name : ∀ (b₀ : ty₀) …, stmt := fun … => proof`, binding the
/// supplied free variables at the supplied types.
///
/// [`NatOps::theorem`] only binds `Nat`-typed variables, and half the
/// statements here quantify over a `Nat → Nat` or a `Nat.Multiset`.
fn declare_forall(
    d: &mut NatDev<'_>,
    name: NameId,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, binder_ty) in binders.iter().rev() {
        ty = d.pi_fv(fv, binder_ty, ty);
        value = d.lam_fv(fv, binder_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

// ---------------------------------------------------------------------------
// General `Nat` lemmas this route needs and the prelude did not have.
// ---------------------------------------------------------------------------

/// `Nat.pow_dvd_pow_of_le`, `Nat.dvd_prodRange_of_lt`,
/// `Nat.prime_pow_dvd_of_dvd_mul_of_not_dvd` and
/// `Nat.exponent_unique_of_exact_dvd`. None mentions `Nat.Multiset`; they are
/// declared here because this is their first consumer.
fn declare_arithmetic_support(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // pow_dvd_pow_of_le : ∀ a i j, Le i j → dvd (pow a i) (pow a j)
    //
    // `le_dest` turns `Le i j` into `i + k = j`, and `pow_add` splits
    // `pow a (i+k)` into `pow a i * pow a k`, of which `pow a i` is a factor.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hyp_ty = d.le(i, j);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let pow_i = d.pow(a, i);
        let pow_j = d.pow(a, j);
        let goal = d.dvd(pow_i, pow_j);

        let predicate = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(i, k);
            let body = d.eq(sum, j);
            d.lam_fv(k_fv, nat, body)
        };
        let dest = d.lemma(p.le_dest, &[i, j, h]);
        let proof = exists_elim_nat(
            d,
            &p,
            predicate,
            &|d, w| {
                let sum = d.add(i, w);
                d.eq(sum, j)
            },
            goal,
            dest,
            &|d, w, hw| {
                // dvd (pow a i) (pow a i * pow a w)
                let pow_w = d.pow(a, w);
                let product = d.mul(pow_i, pow_w);
                let base = d.lemma(p.dvd_mul, &[pow_i, pow_w]);
                // pow a (i + w) = pow a i * pow a w
                let sum = d.add(i, w);
                let pow_sum = d.pow(a, sum);
                let split = d.lemma(p.pow_add, &[a, i, w]);
                let split_back = d.symm(pow_sum, product, split);
                let at_sum = transport_dvd_right(d, pow_i, product, pow_sum, split_back, base);
                // pow a (i + w) = pow a j
                let step = d.congr(sum, j, hw, &|d, x| d.pow(a, x));
                transport_dvd_right(d, pow_i, pow_sum, pow_j, step, at_sum)
            },
        );
        declare_forall(
            d,
            p.pow_dvd_pow_of_le,
            &[(a_fv, nat), (i_fv, nat), (j_fv, nat), (h_fv, hyp_ty)],
            goal,
            proof,
        )?;
    }

    // dvd_prodRange_of_lt : ∀ f i k, Lt i k → dvd (f i) (prodRange f k)
    //
    // Induction on `k`. `prodRange f (succ j) ≡ prodRange f j * f j`, so the
    // step is `dvd_mul_right_of_dvd` on the induction hypothesis when `i < j`
    // and `dvd_mul_left` transported along `f i = f j` when `i = j`.
    {
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
            let fi = d.apply(f, &[i]);
            let pr = prod_range(d, &p, f, bound);
            let concl = d.dvd(fi, pr);
            let hyp = d.lt(i, bound);
            d.arrow(hyp, concl)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hyp = d.lt(i, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let absurd = d.lemma(p.not_succ_le_zero, &[i, h]);
            let fi = d.apply(f, &[i]);
            let pr = prod_range(d, &p, f, zero);
            let target = d.dvd(fi, pr);
            let body = from_false(d, &p, absurd, target);
            d.lam_fv(h_fv, hyp, body)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let succ_j = d.succ(j);
            let hyp = d.lt(i, succ_j);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let fi = d.apply(f, &[i]);
            let pr_succ = prod_range(d, &p, f, succ_j);
            let goal = d.dvd(fi, pr_succ);

            let le_i_j = d.lemma(p.le_of_lt_succ, &[i, j, h]);
            let split = d.lemma(p.lt_or_eq_of_le, &[i, j, le_i_j]);
            let lt_ty = d.lt(i, j);
            let eq_ty = d.eq(i, j);
            let left = {
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let inner = d.apply(ih, &[hl]);
                let pr_j = prod_range(d, &p, f, j);
                let fj = d.apply(f, &[j]);
                let lifted = d.lemma(p.dvd_mul_right_of_dvd, &[fi, pr_j, fj, inner]);
                d.lam_fv(hl_fv, lt_ty, lifted)
            };
            let right = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                let pr_j = prod_range(d, &p, f, j);
                let fj = d.apply(f, &[j]);
                let at_j = d.lemma(p.dvd_mul_left, &[fj, pr_j]);
                let step_eq = d.congr(i, j, he, &|d, x| d.apply(f, &[x]));
                let back = d.symm(fi, fj, step_eq);
                let product = d.mul(pr_j, fj);
                let moved = transport_dvd_left(d, fj, fi, back, product, at_j);
                d.lam_fv(he_fv, eq_ty, moved)
            };
            let body = or_cases(d, &p, lt_ty, eq_ty, goal, left, right, split);
            d.lam_fv(h_fv, hyp, body)
        };
        let proof = d.induct(&claim, &base, &step, k);
        let stmt = claim(d, k);
        declare_forall(
            d,
            p.dvd_prod_range_of_lt,
            &[(f_fv, fn_ty), (i_fv, nat), (k_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // prime_pow_dvd_of_dvd_mul_of_not_dvd :
    //   ∀ pv b c, prime_condition pv → Not (dvd pv b) →
    //     ∀ a, dvd (pow pv c) (mul a b) → dvd (pow pv c) a
    //
    // Induction on the EXPONENT `c`, with `a` quantified inside the motive
    // because the step replaces `a` by `a / pv`. `euclid_lemma` peels one `pv`
    // off `a` (never off `b`, which the second hypothesis forbids), and
    // left-cancellation removes it from both sides.
    //
    // This is the whole of the coprimality reasoning the uniqueness proof
    // needs. It deliberately does NOT go through `Nat.Coprime`: this prelude
    // has `prime_coprime_pow_of_not_dvd` (coprimality of a prime with a POWER)
    // but nothing giving coprimality of a prime POWER with anything, and
    // `coprime_dvd_mul_right` needs exactly that.
    {
        let pv_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(pv_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let prime_ty = prime_condition(d, &p, pv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let dvd_pv_b = d.dvd(pv, b);
        let nd_ty = not_ty(d, &p, dvd_pv_b);
        let hnd_fv = d.fresh_fvar();
        let hnd = d.kernel().fvar(hnd_fv);

        let claim = |d: &mut NatDev<'_>, e: ExprId| -> ExprId {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let pow_e = d.pow(pv, e);
            let ab = d.mul(a, b);
            let hyp = d.dvd(pow_e, ab);
            let concl = d.dvd(pow_e, a);
            let body = d.arrow(hyp, concl);
            d.pi_fv(a_fv, nat, body)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let pow_zero_term = d.pow(pv, zero);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let ab = d.mul(a, b);
            let hyp = d.dvd(pow_zero_term, ab);
            let hd_fv = d.fresh_fvar();
            // `pow pv 0 * a = 1 * a = a`, so `a = pow pv 0 * a` and `a` is its
            // own cofactor.
            let product = d.mul(pow_zero_term, a);
            let one_lit = d.num(1);
            let pz = d.lemma(p.pow_zero, &[pv]);
            let to_one = d.congr(pow_zero_term, one_lit, pz, &|d, x| d.mul(x, a));
            let one_a = d.mul(one_lit, a);
            let om = d.lemma(p.one_mul, &[a]);
            let (_, product_eq_a) = d.chain(product, &[(one_a, to_one), (a, om)]);
            let a_eq_product = d.symm(product, a, product_eq_a);
            let witness = dvd_intro(d, &p, pow_zero_term, a, a, a_eq_product);
            let with_hd = d.lam_fv(hd_fv, hyp, witness);
            d.lam_fv(a_fv, nat, with_hd)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let succ_j = d.succ(j);
            let pow_j = d.pow(pv, j);
            let pow_succ_j = d.pow(pv, succ_j);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let ab = d.mul(a, b);
            let hyp = d.dvd(pow_succ_j, ab);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let goal = d.dvd(pow_succ_j, a);

            // pv ∣ pow pv (succ j) ∣ a * b
            let pow_succ_eq = d.lemma(p.pow_succ, &[pv, j]);
            let folded = d.mul(pow_j, pv);
            let pv_dvd_folded = d.lemma(p.dvd_mul_left, &[pv, pow_j]);
            let back = d.symm(pow_succ_j, folded, pow_succ_eq);
            let pv_dvd_pow = transport_dvd_right(d, pv, folded, pow_succ_j, back, pv_dvd_folded);
            let pv_dvd_ab = d.lemma(p.dvd_trans, &[pv, pow_succ_j, ab, pv_dvd_pow, hd]);
            let split = d.lemma(p.euclid_lemma, &[pv, a, b, hp, pv_dvd_ab]);
            let left_ty = d.dvd(pv, a);
            let right_ty = d.dvd(pv, b);
            let right = {
                let hr_fv = d.fresh_fvar();
                let hr = d.kernel().fvar(hr_fv);
                let contradiction = d.apply(hnd, &[hr]);
                let body = from_false(d, &p, contradiction, goal);
                d.lam_fv(hr_fv, right_ty, body)
            };
            let left = {
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let body = dvd_elim(d, &p, pv, a, goal, hl, &|d, w, heq| {
                    // heq : a = pv * w
                    let pv_w = d.mul(pv, w);
                    let wb = d.mul(w, b);
                    let pv_wb = d.mul(pv, wb);
                    // a * b = (pv * w) * b = pv * (w * b)
                    let to_pv_w = d.congr(a, pv_w, heq, &|d, x| d.mul(x, b));
                    let pv_w_b = d.mul(pv_w, b);
                    let assoc = d.lemma(p.mul_assoc, &[pv, w, b]);
                    let (_, ab_eq) = d.chain(ab, &[(pv_w_b, to_pv_w), (pv_wb, assoc)]);
                    let moved_right = transport_dvd_right(d, pow_succ_j, ab, pv_wb, ab_eq, hd);
                    // pow pv (succ j) = pow pv j * pv = pv * pow pv j
                    let comm = d.lemma(p.mul_comm, &[pow_j, pv]);
                    let pv_pow_j = d.mul(pv, pow_j);
                    let (_, pow_eq) =
                        d.chain(pow_succ_j, &[(folded, pow_succ_eq), (pv_pow_j, comm)]);
                    let moved_left =
                        transport_dvd_left(d, pow_succ_j, pv_pow_j, pow_eq, pv_wb, moved_right);
                    let pv_pos = d.lemma(p.prime_one_le, &[pv, hp]);
                    let cancelled =
                        dvd_cancel_left_of_pos(d, &p, pv, pow_j, wb, pv_pos, moved_left);
                    let recursed = d.apply(ih, &[w, cancelled]);
                    dvd_elim(d, &p, pow_j, w, goal, recursed, &|d, u, heq2| {
                        // heq2 : w = pow pv j * u
                        // a = pv * w = pv * (pow pv j * u)
                        //   = (pv * pow pv j) * u = (pow pv j * pv) * u
                        //   = pow pv (succ j) * u
                        let pow_j_u = d.mul(pow_j, u);
                        let pv_pow_j_u = d.mul(pv, pow_j_u);
                        let inner = d.congr(w, pow_j_u, heq2, &|d, x| d.mul(pv, x));
                        let assoc2 = d.lemma(p.mul_assoc, &[pv, pow_j, u]);
                        let pv_pow_j_times_u = d.mul(pv_pow_j, u);
                        let assoc2_back = d.symm(pv_pow_j_times_u, pv_pow_j_u, assoc2);
                        let comm_back = d.symm(folded, pv_pow_j, comm);
                        let to_folded = d.congr(pv_pow_j, folded, comm_back, &|d, x| d.mul(x, u));
                        let folded_u = d.mul(folded, u);
                        let pow_succ_back = d.symm(pow_succ_j, folded, pow_succ_eq);
                        let to_pow_succ =
                            d.congr(folded, pow_succ_j, pow_succ_back, &|d, x| d.mul(x, u));
                        let pow_succ_u = d.mul(pow_succ_j, u);
                        let (_, a_eq) = d.chain(
                            a,
                            &[
                                (pv_w, heq),
                                (pv_pow_j_u, inner),
                                (pv_pow_j_times_u, assoc2_back),
                                (folded_u, to_folded),
                                (pow_succ_u, to_pow_succ),
                            ],
                        );
                        dvd_intro(d, &p, pow_succ_j, a, u, a_eq)
                    })
                });
                d.lam_fv(hl_fv, left_ty, body)
            };
            let cases = or_cases(d, &p, left_ty, right_ty, goal, left, right, split);
            let with_hd = d.lam_fv(hd_fv, hyp, cases);
            d.lam_fv(a_fv, nat, with_hd)
        };
        let proof = d.induct(&claim, &base, &step, c);
        let stmt = claim(d, c);
        declare_forall(
            d,
            p.prime_pow_dvd_of_dvd_mul_of_not_dvd,
            &[
                (pv_fv, nat),
                (b_fv, nat),
                (c_fv, nat),
                (hp_fv, prime_ty),
                (hnd_fv, nd_ty),
            ],
            stmt,
            proof,
        )?;
    }

    // exponent_unique_of_exact_dvd :
    //   ∀ a n c1 c2, dvd (pow a c1) n → Not (dvd (pow a (succ c1)) n) →
    //                dvd (pow a c2) n → Not (dvd (pow a (succ c2)) n) →
    //                Eq c1 c2
    //
    // No primality needed: the four facts alone pin the exponent, because
    // `c1 < c2` makes `pow a (succ c1)` divide `pow a c2` and hence `n`.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let c1_fv = d.fresh_fvar();
        let c1 = d.kernel().fvar(c1_fv);
        let c2_fv = d.fresh_fvar();
        let c2 = d.kernel().fvar(c2_fv);

        let pow_c1 = d.pow(a, c1);
        let pow_c2 = d.pow(a, c2);
        let succ_c1 = d.succ(c1);
        let succ_c2 = d.succ(c2);
        let pow_s1 = d.pow(a, succ_c1);
        let pow_s2 = d.pow(a, succ_c2);

        let h1_ty = d.dvd(pow_c1, n);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let n1_inner = d.dvd(pow_s1, n);
        let n1_ty = not_ty(d, &p, n1_inner);
        let n1_fv = d.fresh_fvar();
        let n1 = d.kernel().fvar(n1_fv);
        let h2_ty = d.dvd(pow_c2, n);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let n2_inner = d.dvd(pow_s2, n);
        let n2_ty = not_ty(d, &p, n2_inner);
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);

        let goal = d.eq(c1, c2);

        // `Lt x y ⊢ False`, from `pow a (succ x) ∣ pow a y ∣ n` and the
        // exactness hypothesis at `x`.
        let contradiction = |d: &mut NatDev<'_>,
                             small: ExprId,
                             large: ExprId,
                             pow_large: ExprId,
                             pow_small_succ: ExprId,
                             refutation: ExprId,
                             big_dvd: ExprId,
                             hlt: ExprId|
         -> ExprId {
            let succ_small = d.succ(small);
            let ladder = d.lemma(p.pow_dvd_pow_of_le, &[a, succ_small, large, hlt]);
            let reaches = d.lemma(
                p.dvd_trans,
                &[pow_small_succ, pow_large, n, ladder, big_dvd],
            );
            d.apply(refutation, &[reaches])
        };

        let proof = {
            let outer = d.lemma(p.lt_or_ge, &[c1, c2]);
            let lt12 = d.lt(c1, c2);
            let ge12 = d.le(c2, c1);
            let left = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let bad = contradiction(d, c1, c2, pow_c2, pow_s1, n1, h2, h);
                let body = from_false(d, &p, bad, goal);
                d.lam_fv(h_fv, lt12, body)
            };
            let right = {
                let hge_fv = d.fresh_fvar();
                let hge = d.kernel().fvar(hge_fv);
                let inner_split = d.lemma(p.lt_or_ge, &[c2, c1]);
                let lt21 = d.lt(c2, c1);
                let ge21 = d.le(c1, c2);
                let inner_left = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let bad = contradiction(d, c2, c1, pow_c1, pow_s2, n2, h1, h);
                    let body = from_false(d, &p, bad, goal);
                    d.lam_fv(h_fv, lt21, body)
                };
                let inner_right = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let anti = d.lemma(p.le_antisymm, &[c1, c2, h, hge]);
                    d.lam_fv(h_fv, ge21, anti)
                };
                let body = or_cases(
                    d,
                    &p,
                    lt21,
                    ge21,
                    goal,
                    inner_left,
                    inner_right,
                    inner_split,
                );
                d.lam_fv(hge_fv, ge12, body)
            };
            or_cases(d, &p, lt12, ge12, goal, left, right, outer)
        };

        declare_forall(
            d,
            p.exponent_unique_of_exact_dvd,
            &[
                (a_fv, nat),
                (n_fv, nat),
                (c1_fv, nat),
                (c2_fv, nat),
                (h1_fv, h1_ty),
                (n1_fv, n1_ty),
                (h2_fv, h2_ty),
                (n2_fv, n2_ty),
            ],
            goal,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The `count` laws.
// ---------------------------------------------------------------------------

/// `count_eq_zero_of_bound_le`, `count_of_lt_bound` and `count_add`.
fn declare_count_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);

    // count_eq_zero_of_bound_le : ∀ m x, Le (bound m) x → Eq (count m x) 0
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let b = ms_bound(d, &p, m);
        let hyp_ty = d.le(b, x);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let succ_x = d.succ(x);
        let cond = d.ble(succ_x, b);
        let raw_m = ms_raw(d, &p, m);
        let raw_at = d.apply(raw_m, &[x]);
        let zero = d.zero();
        let lt_b_succ_x = d.lemma(p.le_succ_succ, &[b, x, h]);
        let cond_false = d.lemma(p.ble_eq_false_of_lt, &[succ_x, b, lt_b_succ_x]);
        let proof = select_nat_false(d, cond, raw_at, zero, cond_false);
        let count = ms_count(d, &p, m, x);
        let stmt = d.eq(count, zero);
        declare_forall(
            d,
            p.multiset_count_eq_zero_of_bound_le,
            &[(m_fv, ms), (x_fv, nat), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    // count_of_lt_bound : ∀ m x, Lt x (bound m) → Eq (count m x) (raw m x)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let b = ms_bound(d, &p, m);
        let hyp_ty = d.lt(x, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let succ_x = d.succ(x);
        let cond = d.ble(succ_x, b);
        let raw_m = ms_raw(d, &p, m);
        let raw_at = d.apply(raw_m, &[x]);
        let zero = d.zero();
        let cond_true = d.lemma(p.ble_eq_true_of_le, &[succ_x, b, h]);
        let proof = select_nat_true(d, cond, raw_at, zero, cond_true);
        let count = ms_count(d, &p, m, x);
        let stmt = d.eq(count, raw_at);
        declare_forall(
            d,
            p.multiset_count_of_lt_bound,
            &[(m_fv, ms), (x_fv, nat), (h_fv, hyp_ty)],
            stmt,
            proof,
        )?;
    }

    // count_add : ∀ m1 m2 x, Eq (count (add m1 m2) x)
    //                           (add (count m1 x) (count m2 x))
    //
    // Below the sum's bound `count` reads `raw`, which IS the pointwise sum by
    // construction. At or above it, all three counts are `0` — the summands'
    // own bounds are below the sum (`le_add_right`, and `add_comm` for the
    // right one), so `count_eq_zero_of_bound_le` applies to each.
    {
        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let joined = d.const_app(p.multiset_add, &[m1, m2]);
        let b = ms_bound(d, &p, joined);
        let c1 = ms_count(d, &p, m1, x);
        let c2 = ms_count(d, &p, m2, x);
        let sum = d.add(c1, c2);
        let count_joined = ms_count(d, &p, joined, x);
        let stmt = d.eq(count_joined, sum);

        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let joined = d.const_app(p.multiset_add, &[m1, m2]);
            let lhs = ms_count(d, &p, joined, x);
            let c1 = ms_count(d, &p, m1, x);
            let c2 = ms_count(d, &p, m2, x);
            let rhs = d.add(c1, c2);
            d.eq(lhs, rhs)
        };
        let small = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            // `raw joined x` iota-reduces to `count m1 x + count m2 x`, so
            // `count_of_lt_bound` is already the statement.
            d.lemma(p.multiset_count_of_lt_bound, &[joined, x, h])
        };
        let big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            let b1 = ms_bound(d, &p, m1);
            let b2 = ms_bound(d, &p, m2);
            let le_b1 = d.lemma(p.le_add_right, &[b1, b2]);
            let le_b1_x = d.lemma(p.le_trans, &[b1, b, x, le_b1, h]);
            let flipped = d.lemma(p.le_add_right, &[b2, b1]);
            let comm = d.lemma(p.add_comm, &[b2, b1]);
            let b2_b1 = d.add(b2, b1);
            let le_b2 = {
                let motive = d.eq_motive(b2_b1, &|d, y| d.le(b2, y));
                d.transport(b2_b1, motive, flipped, b, comm)
            };
            let le_b2_x = d.lemma(p.le_trans, &[b2, b, x, le_b2, h]);
            let z1 = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[m1, x, le_b1_x]);
            let z2 = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[m2, x, le_b2_x]);
            let zj = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[joined, x, h]);
            let zero = d.zero();
            let to_zero_left = d.congr(c1, zero, z1, &|d, y| d.add(y, c2));
            let zero_c2 = d.add(zero, c2);
            let to_zero_right = d.congr(c2, zero, z2, &|d, y| d.add(zero, y));
            let zero_zero = d.add(zero, zero);
            let (_, sum_eq_zero) =
                d.chain(sum, &[(zero_c2, to_zero_left), (zero_zero, to_zero_right)]);
            // `0 + 0` reduces to `0`, so `sum = 0 = count joined x`.
            let zero_refl = d.refl(zero);
            let sum_eq = d.trans(sum, zero_zero, zero, sum_eq_zero, zero_refl);
            let back = d.symm(sum, zero, sum_eq);
            d.trans(count_joined, zero, sum, zj, back)
        };
        let proof = cases_lt_or_ge(d, &p, x, b, &motive, &small, &big);
        declare_forall(
            d,
            p.multiset_count_add,
            &[(m1_fv, ms), (m2_fv, ms), (x_fv, nat)],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The two inductions over the bound, and the three headline statements.
// ---------------------------------------------------------------------------

/// `∀ q, Lt 0 (g q) → prime_condition q` — "every element of this multiplicity
/// function is prime".
fn prime_support_ty(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let gq = d.apply(g, &[q]);
    let zero = d.zero();
    let positive = d.lt(zero, gq);
    let prime = prime_condition(d, p, q);
    let body = d.arrow(positive, prime);
    d.pi_fv(q_fv, nat, body)
}

/// From `hy : dvd pv (pow j (g j))` and `ne : Not (Eq pv j)`, derive `False`.
///
/// The two branches are the two ways `pow j (g j)` can fail to be divisible by
/// a prime other than `j`, and the FIRST is what rules out `j = 0`: if `g j` is
/// zero the factor is `1` (and `j` need not be prime at all), while otherwise
/// `j` is prime by the support hypothesis and `prime_dvd_of_dvd_pow` reduces
/// the goal to `pv ∣ j`, which for two primes forces `pv = j`.
#[allow(clippy::too_many_arguments)]
fn refute_dvd_pow_factor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    hps: ExprId,
    pv: ExprId,
    hp: ExprId,
    j: ExprId,
    ne: ExprId,
    hy: ExprId,
) -> ExprId {
    let p = *p;
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let gj = d.apply(g, &[j]);
    let one_lit = d.num(1);
    let motive =
        |d: &mut NatDev<'_>, _y: ExprId| -> ExprId { d.kernel().const_(p.logic.false_, vec![]) };
    let small = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
        // `g j < 1`, so `g j = 0` and the factor is `pow j 0 = 1`.
        let zero = d.zero();
        let le_zero = d.lemma(p.le_of_lt_succ, &[gj, zero, h]);
        let zero_le = d.lemma(p.zero_le, &[gj]);
        let is_zero = d.lemma(p.le_antisymm, &[gj, zero, le_zero, zero_le]);
        let pow_gj = d.pow(j, gj);
        let pow_zero_term = d.pow(j, zero);
        let to_zero = d.congr(gj, zero, is_zero, &|d, x| d.pow(j, x));
        let pz = d.lemma(p.pow_zero, &[j]);
        let (_, factor_is_one) = d.chain(pow_gj, &[(pow_zero_term, to_zero), (one_lit, pz)]);
        let at_one = transport_dvd_right(d, pv, pow_gj, one_lit, factor_is_one, hy);
        let refute = d.lemma(p.prime_not_dvd_one, &[pv, hp]);
        d.apply(refute, &[at_one])
    };
    let big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
        // `0 < g j`, so `j` is prime, and a prime dividing `j ^ (g j)` divides
        // `j` itself -- forcing `pv = 1` (impossible) or `pv = j` (excluded).
        let prime_j = d.apply(hps, &[j, h]);
        let dvd_j = d.lemma(p.prime_dvd_of_dvd_pow, &[pv, j, gj, hp, hy]);
        let split = d.lemma(p.prime_eq_one_or_self_of_dvd, &[j, pv, prime_j, dvd_j]);
        let is_one = d.eq(pv, one_lit);
        let is_j = d.eq(pv, j);
        let left = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let one_lt = d.lemma(p.prime_one_lt, &[pv, hp]);
            let moved = {
                let motive = d.eq_motive(pv, &|d, y| {
                    let one_inner = d.num(1);
                    d.lt(one_inner, y)
                });
                d.transport(pv, motive, one_lt, one_lit, he)
            };
            let bad = d.lemma(p.lt_irrefl, &[one_lit, moved]);
            d.lam_fv(he_fv, is_one, bad)
        };
        let right = {
            let he_fv = d.fresh_fvar();
            let he = d.kernel().fvar(he_fv);
            let bad = d.apply(ne, &[he]);
            d.lam_fv(he_fv, is_j, bad)
        };
        or_cases(d, &p, is_one, is_j, false_ty, left, right, split)
    };
    cases_lt_or_ge(d, &p, gj, one_lit, &motive, &small, &big)
}

/// `hlt : Lt a b ⊢ Not (Eq a b)` — the same fact in the other orientation.
/// Both are needed: `refute_dvd_pow_factor` always wants `Not (Eq pv j)`, and
/// the two callers hold the strict inequality in opposite directions.
fn ne_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let eq_ty = d.eq(a, b);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);
    // `Eq a b` moves `Lt a b` to `Lt b b`.
    let motive = d.eq_motive(a, &|d, y| d.lt(y, b));
    let moved = d.transport(a, motive, hlt, b, he);
    let bad = d.lemma(p.lt_irrefl, &[b, moved]);
    d.lam_fv(he_fv, eq_ty, bad)
}

/// `hlt : Lt a b ⊢ Not (Eq b a)` — the two are distinct because one is
/// strictly below the other.
fn ne_of_lt_rev(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let eq_ty = d.eq(b, a);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);
    // `Eq b a` moves `Lt a b` to `Lt a a`.
    let motive = d.eq_motive(b, &|d, y| d.lt(a, y));
    let moved = d.transport(b, motive, hlt, a, he);
    let bad = d.lemma(p.lt_irrefl, &[a, moved]);
    d.lam_fv(he_fv, eq_ty, bad)
}

/// `Nat.not_dvd_prodRange_of_le` and `Nat.not_pow_succ_dvd_prodRange_of_lt` —
/// the two inductions over the fold's bound.
fn declare_prod_range_valuation(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    // not_dvd_prodRange_of_le :
    //   ∀ g pv k, prime_condition pv → (∀ q, Lt 0 (g q) → prime_condition q) →
    //     Le k pv → Not (dvd pv (prodRange (fun q => pow q (g q)) k))
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let pv_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(pv_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let prime_ty = prime_condition(d, &p, pv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let ps_ty = prime_support_ty(d, &p, g);
        let hps_fv = d.fresh_fvar();
        let hps = d.kernel().fvar(hps_fv);
        let factors = pow_factor(d, g);

        let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
            let pr = prod_range(d, &p, factors, bound);
            let divides = d.dvd(pv, pr);
            let refute = not_ty(d, &p, divides);
            let hyp = d.le(bound, pv);
            d.arrow(hyp, refute)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hyp = d.le(zero, pv);
            let h_fv = d.fresh_fvar();
            let pr = prod_range(d, &p, factors, zero);
            let divides = d.dvd(pv, pr);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let refute = d.lemma(p.prime_not_dvd_one, &[pv, hp]);
            let bad = d.apply(refute, &[hd]);
            let with_hd = d.lam_fv(hd_fv, divides, bad);
            d.lam_fv(h_fv, hyp, with_hd)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let succ_j = d.succ(j);
            let hyp = d.le(succ_j, pv);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pr_succ = prod_range(d, &p, factors, succ_j);
            let divides = d.dvd(pv, pr_succ);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);

            let le_succ_j = d.lemma(p.le_succ, &[j]);
            let le_j_pv = d.lemma(p.le_trans, &[j, succ_j, pv, le_succ_j, h]);
            let ih_applied = d.apply(ih, &[le_j_pv]);
            let pr_j = prod_range(d, &p, factors, j);
            let gj = d.apply(g, &[j]);
            let factor = d.pow(j, gj);
            let split = d.lemma(p.euclid_lemma, &[pv, pr_j, factor, hp, hd]);
            let left_ty = d.dvd(pv, pr_j);
            let right_ty = d.dvd(pv, factor);
            let left = {
                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                let bad = d.apply(ih_applied, &[hx]);
                d.lam_fv(hx_fv, left_ty, bad)
            };
            let right = {
                let hy_fv = d.fresh_fvar();
                let hy = d.kernel().fvar(hy_fv);
                let ne = ne_of_lt_rev(d, &p, j, pv, h);
                let bad = refute_dvd_pow_factor(d, &p, g, hps, pv, hp, j, ne, hy);
                d.lam_fv(hy_fv, right_ty, bad)
            };
            let cases = or_cases(d, &p, left_ty, right_ty, false_ty, left, right, split);
            let with_hd = d.lam_fv(hd_fv, divides, cases);
            d.lam_fv(h_fv, hyp, with_hd)
        };
        let proof = d.induct(&claim, &base, &step, k);
        let stmt = claim(d, k);
        declare_forall(
            d,
            p.not_dvd_prod_range_of_le,
            &[
                (g_fv, fn_ty),
                (pv_fv, nat),
                (k_fv, nat),
                (hp_fv, prime_ty),
                (hps_fv, ps_ty),
            ],
            stmt,
            proof,
        )?;
    }

    // not_pow_succ_dvd_prodRange_of_lt :
    //   ∀ g pv k, prime_condition pv → (∀ q, Lt 0 (g q) → prime_condition q) →
    //     Lt pv k → Not (dvd (pow pv (succ (g pv)))
    //                        (prodRange (fun q => pow q (g q)) k))
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let pv_fv = d.fresh_fvar();
        let pv = d.kernel().fvar(pv_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let prime_ty = prime_condition(d, &p, pv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let ps_ty = prime_support_ty(d, &p, g);
        let hps_fv = d.fresh_fvar();
        let hps = d.kernel().fvar(hps_fv);
        let factors = pow_factor(d, g);
        let c = d.apply(g, &[pv]);
        let succ_c = d.succ(c);
        let pow_c = d.pow(pv, c);
        let pow_succ_c = d.pow(pv, succ_c);

        let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
            let pr = prod_range(d, &p, factors, bound);
            let divides = d.dvd(pow_succ_c, pr);
            let refute = not_ty(d, &p, divides);
            let hyp = d.lt(pv, bound);
            d.arrow(hyp, refute)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hyp = d.lt(pv, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pr = prod_range(d, &p, factors, zero);
            let divides = d.dvd(pow_succ_c, pr);
            let hd_fv = d.fresh_fvar();
            let bad = d.lemma(p.not_succ_le_zero, &[pv, h]);
            let with_hd = d.lam_fv(hd_fv, divides, bad);
            d.lam_fv(h_fv, hyp, with_hd)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let succ_j = d.succ(j);
            let hyp = d.lt(pv, succ_j);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pr_succ = prod_range(d, &p, factors, succ_j);
            let divides = d.dvd(pow_succ_c, pr_succ);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);

            let pr_j = prod_range(d, &p, factors, j);
            let gj = d.apply(g, &[j]);
            let factor = d.pow(j, gj);
            let le_pv_j = d.lemma(p.le_of_lt_succ, &[pv, j, h]);
            let split = d.lemma(p.lt_or_eq_of_le, &[pv, j, le_pv_j]);
            let lt_ty = d.lt(pv, j);
            let eq_ty = d.eq(pv, j);

            let left = {
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let ih_applied = d.apply(ih, &[hl]);
                // `pv /= j` because `pv < j`. Note the ORIENTATION:
                // `refute_dvd_pow_factor` wants `Not (Eq pv j)`, and here the
                // strict inequality runs the other way from the first
                // induction's, so this is `ne_of_lt` rather than
                // `ne_of_lt_rev`.
                let ne = ne_of_lt(d, &p, pv, j, hl);
                let nd_factor = {
                    let hy_fv = d.fresh_fvar();
                    let hy = d.kernel().fvar(hy_fv);
                    let divides_factor = d.dvd(pv, factor);
                    let bad = refute_dvd_pow_factor(d, &p, g, hps, pv, hp, j, ne, hy);
                    d.lam_fv(hy_fv, divides_factor, bad)
                };
                let moved = d.lemma(
                    p.prime_pow_dvd_of_dvd_mul_of_not_dvd,
                    &[pv, factor, succ_c, hp, nd_factor, pr_j, hd],
                );
                let bad = d.apply(ih_applied, &[moved]);
                d.lam_fv(hl_fv, lt_ty, bad)
            };
            let right = {
                let he_fv = d.fresh_fvar();
                let he = d.kernel().fvar(he_fv);
                // `pv = j`, so the new factor IS `pow pv c` and cancelling it
                // leaves `pv ∣ prodRange factors j`, which the first induction
                // refutes at `k := j` (`Le j pv` holds because `j = pv`).
                let j_eq_pv = d.symm(pv, j, he);
                let factor_eq = d.congr(j, pv, j_eq_pv, &|d, x| {
                    let gx = d.apply(g, &[x]);
                    d.pow(x, gx)
                });
                let product = d.mul(pr_j, factor);
                let product_c = d.mul(pr_j, pow_c);
                let to_pow_c = d.congr(factor, pow_c, factor_eq, &|d, x| d.mul(pr_j, x));
                let comm = d.lemma(p.mul_comm, &[pr_j, pow_c]);
                let flipped = d.mul(pow_c, pr_j);
                let (_, product_eq) = d.chain(product, &[(product_c, to_pow_c), (flipped, comm)]);
                let moved_right =
                    transport_dvd_right(d, pow_succ_c, product, flipped, product_eq, hd);
                let folded = d.mul(pow_c, pv);
                let pow_succ_eq = d.lemma(p.pow_succ, &[pv, c]);
                let moved_left =
                    transport_dvd_left(d, pow_succ_c, folded, pow_succ_eq, flipped, moved_right);
                let pv_pos = d.lemma(p.prime_pos, &[pv, hp]);
                let pow_pos = d.lemma(p.pow_pos, &[pv, c, pv_pos]);
                let cancelled = dvd_cancel_left_of_pos(d, &p, pow_c, pv, pr_j, pow_pos, moved_left);
                let le_j_j = d.lemma(p.le_refl, &[j]);
                let le_j_pv = {
                    let motive = d.eq_motive(j, &|d, y| d.le(j, y));
                    d.transport(j, motive, le_j_j, pv, j_eq_pv)
                };
                let refute = d.lemma(p.not_dvd_prod_range_of_le, &[g, pv, j, hp, hps, le_j_pv]);
                let bad = d.apply(refute, &[cancelled]);
                d.lam_fv(he_fv, eq_ty, bad)
            };
            let cases = or_cases(d, &p, lt_ty, eq_ty, false_ty, left, right, split);
            let with_hd = d.lam_fv(hd_fv, divides, cases);
            d.lam_fv(h_fv, hyp, with_hd)
        };
        let proof = d.induct(&claim, &base, &step, k);
        let stmt = claim(d, k);
        declare_forall(
            d,
            p.not_pow_succ_dvd_prod_range_of_lt,
            &[
                (g_fv, fn_ty),
                (pv_fv, nat),
                (k_fv, nat),
                (hp_fv, prime_ty),
                (hps_fv, ps_ty),
            ],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

/// The three headline statements: the two halves of "`count m p` is the
/// `p`-adic valuation of `prod m`", and uniqueness.
fn declare_uniqueness(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let ms = multiset_ty(d, &p);

    // pow_count_dvd_prod : ∀ m x, dvd (pow x (count m x)) (prod m)
    //
    // No hypotheses. Below the bound `pow x (count m x)` IS one of the folded
    // factors; at or above it the count is `0` and the power is `1`.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let g = d.const_app(p.multiset_count, &[m]);
        let factors = pow_factor(d, g);
        let b = ms_bound(d, &p, m);
        let count = ms_count(d, &p, m, x);
        let pow_count = d.pow(x, count);
        let prod = ms_prod(d, &p, m);
        let stmt = d.dvd(pow_count, prod);

        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let count = ms_count(d, &p, m, x);
            let pow_count = d.pow(x, count);
            let prod = ms_prod(d, &p, m);
            d.dvd(pow_count, prod)
        };
        let small = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            d.lemma(p.dvd_prod_range_of_lt, &[factors, x, b, h])
        };
        let big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            let zero = d.zero();
            let one_lit = d.num(1);
            let is_zero = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[m, x, h]);
            let pow_zero_term = d.pow(x, zero);
            let to_zero = d.congr(count, zero, is_zero, &|d, y| d.pow(x, y));
            let pz = d.lemma(p.pow_zero, &[x]);
            let (_, is_one) = d.chain(pow_count, &[(pow_zero_term, to_zero), (one_lit, pz)]);
            let one_eq = d.symm(pow_count, one_lit, is_one);
            let one_prod = d.mul(one_lit, prod);
            let om = d.lemma(p.one_mul, &[prod]);
            let prod_eq = d.symm(one_prod, prod, om);
            let one_dvd = dvd_intro(d, &p, one_lit, prod, prod, prod_eq);
            transport_dvd_left(d, one_lit, pow_count, one_eq, prod, one_dvd)
        };
        let proof = cases_lt_or_ge(d, &p, x, b, &motive, &small, &big);
        declare_forall(
            d,
            p.multiset_pow_count_dvd_prod,
            &[(m_fv, ms), (x_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // not_pow_succ_count_dvd_prod :
    //   ∀ m x, prime_condition x → (∀ q, Lt 0 (count m q) → prime_condition q) →
    //     Not (dvd (pow x (succ (count m x))) (prod m))
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let g = d.const_app(p.multiset_count, &[m]);
        let b = ms_bound(d, &p, m);
        let prime_ty = prime_condition(d, &p, x);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let ps_ty = prime_support_ty(d, &p, g);
        let hps_fv = d.fresh_fvar();
        let hps = d.kernel().fvar(hps_fv);
        let count = ms_count(d, &p, m, x);
        let succ_count = d.succ(count);
        let pow_succ_count = d.pow(x, succ_count);
        let prod = ms_prod(d, &p, m);
        let divides = d.dvd(pow_succ_count, prod);
        let stmt = not_ty(d, &p, divides);

        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let count = ms_count(d, &p, m, x);
            let succ_count = d.succ(count);
            let pow_succ_count = d.pow(x, succ_count);
            let prod = ms_prod(d, &p, m);
            let divides = d.dvd(pow_succ_count, prod);
            not_ty(d, &p, divides)
        };
        let small = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            d.lemma(p.not_pow_succ_dvd_prod_range_of_lt, &[g, x, b, hp, hps, h])
        };
        let big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            // `count m x = 0`, so the exponent is `1` and `pow x 1 = x`; the
            // first induction refutes `x ∣ prodRange factors (bound m)`.
            let zero = d.zero();
            let one_lit = d.num(1);
            let is_zero = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[m, x, h]);
            let pow_one_term = d.pow(x, one_lit);
            let to_one = d.congr(count, zero, is_zero, &|d, y| {
                let s = d.succ(y);
                d.pow(x, s)
            });
            let ps = d.lemma(p.pow_succ, &[x, zero]);
            let pow_zero_term = d.pow(x, zero);
            let folded = d.mul(pow_zero_term, x);
            let pz = d.lemma(p.pow_zero, &[x]);
            let to_one_mul = d.congr(pow_zero_term, one_lit, pz, &|d, y| d.mul(y, x));
            let one_x = d.mul(one_lit, x);
            let om = d.lemma(p.one_mul, &[x]);
            let (_, collapses) = d.chain(
                pow_succ_count,
                &[
                    (pow_one_term, to_one),
                    (folded, ps),
                    (one_x, to_one_mul),
                    (x, om),
                ],
            );
            let refute = d.lemma(p.not_dvd_prod_range_of_le, &[g, x, b, hp, hps, h]);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let moved = transport_dvd_left(d, pow_succ_count, x, collapses, prod, hd);
            let bad = d.apply(refute, &[moved]);
            d.lam_fv(hd_fv, divides, bad)
        };
        let proof = cases_lt_or_ge(d, &p, x, b, &motive, &small, &big);
        declare_forall(
            d,
            p.multiset_not_pow_succ_count_dvd_prod,
            &[(m_fv, ms), (x_fv, nat), (hp_fv, prime_ty), (hps_fv, ps_ty)],
            stmt,
            proof,
        )?;
    }

    // count_eq_of_prod_eq : UNIQUENESS.
    //   ∀ m1 m2, (∀ q, Lt 0 (count m1 q) → prime_condition q)
    //          → (∀ q, Lt 0 (count m2 q) → prime_condition q)
    //          → Eq (prod m1) (prod m2)
    //          → ∀ x, Eq (count m1 x) (count m2 x)
    {
        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let g1 = d.const_app(p.multiset_count, &[m1]);
        let g2 = d.const_app(p.multiset_count, &[m2]);
        let ps1_ty = prime_support_ty(d, &p, g1);
        let hps1_fv = d.fresh_fvar();
        let hps1 = d.kernel().fvar(hps1_fv);
        let ps2_ty = prime_support_ty(d, &p, g2);
        let hps2_fv = d.fresh_fvar();
        let hps2 = d.kernel().fvar(hps2_fv);
        let prod1 = ms_prod(d, &p, m1);
        let prod2 = ms_prod(d, &p, m2);
        let prod_eq_ty = d.eq(prod1, prod2);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let c1 = ms_count(d, &p, m1, x);
        let c2 = ms_count(d, &p, m2, x);
        let stmt = d.eq(c1, c2);

        // The valuation argument, available as soon as `x` is known prime.
        let settle = |d: &mut NatDev<'_>, hx: ExprId| -> ExprId {
            let d1 = d.lemma(p.multiset_pow_count_dvd_prod, &[m1, x]);
            let n1 = d.lemma(p.multiset_not_pow_succ_count_dvd_prod, &[m1, x, hx, hps1]);
            let d2_raw = d.lemma(p.multiset_pow_count_dvd_prod, &[m2, x]);
            let n2_raw = d.lemma(p.multiset_not_pow_succ_count_dvd_prod, &[m2, x, hx, hps2]);
            let pow_c2 = d.pow(x, c2);
            let back = d.symm(prod1, prod2, heq);
            let d2 = transport_dvd_right(d, pow_c2, prod2, prod1, back, d2_raw);
            let succ_c2 = d.succ(c2);
            let pow_s2 = d.pow(x, succ_c2);
            let n2 = {
                let hd_fv = d.fresh_fvar();
                let hd = d.kernel().fvar(hd_fv);
                let at_prod1 = d.dvd(pow_s2, prod1);
                let moved = transport_dvd_right(d, pow_s2, prod1, prod2, heq, hd);
                let bad = d.apply(n2_raw, &[moved]);
                d.lam_fv(hd_fv, at_prod1, bad)
            };
            d.lemma(
                p.exponent_unique_of_exact_dvd,
                &[x, prod1, c1, c2, d1, n1, d2, n2],
            )
        };

        let one_lit = d.num(1);
        let outer_motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let c1 = ms_count(d, &p, m1, x);
            let c2 = ms_count(d, &p, m2, x);
            d.eq(c1, c2)
        };
        let outer_big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
            // `0 < count m1 x`, so `x` is prime by `m1`'s support hypothesis.
            let hx = d.apply(hps1, &[x, h]);
            settle(d, hx)
        };
        let outer_small = |d: &mut NatDev<'_>, _y: ExprId, h1: ExprId| -> ExprId {
            // `count m1 x = 0`. Either `m2` still has `x`, which makes `x`
            // prime and hands the argument back to the valuation route, or
            // both counts are zero and the goal is a chain through `0`.
            let zero = d.zero();
            let le_zero = d.lemma(p.le_of_lt_succ, &[c1, zero, h1]);
            let zero_le = d.lemma(p.zero_le, &[c1]);
            let c1_zero = d.lemma(p.le_antisymm, &[c1, zero, le_zero, zero_le]);
            let inner_motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
                let c1 = ms_count(d, &p, m1, x);
                let c2 = ms_count(d, &p, m2, x);
                d.eq(c1, c2)
            };
            let inner_big = |d: &mut NatDev<'_>, _y: ExprId, h: ExprId| -> ExprId {
                let hx = d.apply(hps2, &[x, h]);
                settle(d, hx)
            };
            let inner_small = |d: &mut NatDev<'_>, _y: ExprId, h2: ExprId| -> ExprId {
                let zero = d.zero();
                let le_zero2 = d.lemma(p.le_of_lt_succ, &[c2, zero, h2]);
                let zero_le2 = d.lemma(p.zero_le, &[c2]);
                let c2_zero = d.lemma(p.le_antisymm, &[c2, zero, le_zero2, zero_le2]);
                let back = d.symm(c2, zero, c2_zero);
                d.trans(c1, zero, c2, c1_zero, back)
            };
            cases_lt_or_ge(d, &p, c2, one_lit, &inner_motive, &inner_small, &inner_big)
        };
        let proof = cases_lt_or_ge(d, &p, c1, one_lit, &outer_motive, &outer_small, &outer_big);
        declare_forall(
            d,
            p.multiset_count_eq_of_prod_eq,
            &[
                (m1_fv, ms),
                (m2_fv, ms),
                (hps1_fv, ps1_ty),
                (hps2_fv, ps2_ty),
                (heq_fv, prod_eq_ty),
                (x_fv, nat),
            ],
            stmt,
            proof,
        )?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// `Nat.Multiset.beq`: reflexivity and symmetry.
// ---------------------------------------------------------------------------

/// `heq : Eq Bool cond true ⊢ Eq Bool (bool_select_bool cond a b) a` — the
/// `Bool`-valued twin of `finite.rs`'s [`select_nat_true`].
fn select_bool_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let true_val = d.bool_true();
    let back = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, a)
    });
    let refl_case = d.bool_refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, back)
}

/// `heq : Eq Bool cond false ⊢ Eq Bool (bool_select_bool cond a b) b`.
fn select_bool_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let p = *p;
    let false_val = d.bool_false();
    let back = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_bool(d, &p, value, a, b);
        d.bool_eq(sel, b)
    });
    let refl_case = d.bool_refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, back)
}

/// `h : Eq Bool a b ⊢ Eq Bool (f a) (f b)` — [`NatOps::congr`] always closes
/// into `Eq Nat`, and `gauss_lemma.rs`'s `congr_nat_to_bool` transports along a
/// `Nat` equality; this one transports along a `Bool` one.
fn congr_bool_to_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `Nat.beq_comm`, `Nat.Multiset.eqBelow_self`, `Nat.Multiset.eqBelow_comm`,
/// `Nat.Multiset.beq_refl` and `Nat.Multiset.beq_comm`.
fn declare_beq_laws(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let fn_ty = d.arrow(nat, nat);
    let ms = multiset_ty(d, &p);

    // beq_comm : ∀ a b, Eq Bool (beq a b) (beq b a)
    //
    // `Nat.beq` is a double recursion, so this is NOT `refl`. Decide `beq a b`
    // (`bool_true_or_false`, two constructors, no excluded middle): if it is
    // `true` the arguments are equal and `beq_refl` closes the swap; if it is
    // `false` then `beq b a` must be `false` too, since `beq b a = true` would
    // give `b = a` and hence `beq a b = true`.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let beq_ab = d.beq(a, b);
        let beq_ba = d.beq(b, a);
        let stmt = d.bool_eq(beq_ab, beq_ba);
        let true_val = d.bool_true();
        let false_val = d.bool_false();

        let split = bool_true_or_false(d, &p, beq_ab);
        let is_true = d.bool_eq(beq_ab, true_val);
        let is_false = d.bool_eq(beq_ab, false_val);
        let left = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hab = d.lemma(p.eq_of_beq_eq_true, &[a, b, h]);
            let beq_aa = d.beq(a, a);
            let refl_a = d.lemma(p.beq_refl, &[a]);
            let back = d.bool_symm(beq_aa, true_val, refl_a);
            let at_a = d.bool_trans(beq_ab, true_val, beq_aa, h, back);
            let motive = d.eq_motive(a, &|d, y| {
                let lhs = d.beq(a, b);
                let rhs = d.beq(y, a);
                d.bool_eq(lhs, rhs)
            });
            let moved = d.transport(a, motive, at_a, b, hab);
            d.lam_fv(h_fv, is_true, moved)
        };
        let right = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inner_split = bool_true_or_false(d, &p, beq_ba);
            let ba_true = d.bool_eq(beq_ba, true_val);
            let ba_false = d.bool_eq(beq_ba, false_val);
            let inner_left = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let hba = d.lemma(p.eq_of_beq_eq_true, &[b, a, h2]);
                let hab = d.symm(b, a, hba);
                let ab_true = d.lemma(p.beq_eq_true_of_eq, &[a, b, hab]);
                let flipped = d.bool_symm(beq_ab, false_val, h);
                let bad_eq = d.bool_trans(false_val, beq_ab, true_val, flipped, ab_true);
                let refute = d.kernel().const_(p.logic.bool_false_ne_true, vec![]);
                let bad = d.apply(refute, &[bad_eq]);
                let body = from_false(d, &p, bad, stmt);
                d.lam_fv(h2_fv, ba_true, body)
            };
            let inner_right = {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let back = d.bool_symm(beq_ba, false_val, h2);
                let body = d.bool_trans(beq_ab, false_val, beq_ba, h, back);
                d.lam_fv(h2_fv, ba_false, body)
            };
            let body = or_cases(
                d,
                &p,
                ba_true,
                ba_false,
                stmt,
                inner_left,
                inner_right,
                inner_split,
            );
            d.lam_fv(h_fv, is_false, body)
        };
        let proof = or_cases(d, &p, is_true, is_false, stmt, left, right, split);
        declare_forall(d, p.beq_comm, &[(a_fv, nat), (b_fv, nat)], stmt, proof)?;
    }

    // eqBelow_self : ∀ f k, Eq Bool (eqBelow f f k) Bool.true
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
            let loop_ = d.const_app(p.multiset_eq_below, &[f, f, bound]);
            let true_val = d.bool_true();
            d.bool_eq(loop_, true_val)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let true_val = d.bool_true();
            d.bool_refl(true_val)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let fj = d.apply(f, &[j]);
            let cond = d.beq(fj, fj);
            let inner = d.const_app(p.multiset_eq_below, &[f, f, j]);
            let false_val = d.bool_false();
            let cond_true = d.lemma(p.beq_refl, &[fj]);
            let sel = select_bool_true(d, &p, cond, inner, false_val, cond_true);
            let selected = bool_select_bool(d, &p, cond, inner, false_val);
            let true_val = d.bool_true();
            d.bool_trans(selected, inner, true_val, sel, ih)
        };
        let proof = d.induct(&claim, &base, &step, k);
        let stmt = claim(d, k);
        declare_forall(
            d,
            p.multiset_eq_below_self,
            &[(f_fv, fn_ty), (k_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // eqBelow_comm : ∀ f g k, Eq Bool (eqBelow f g k) (eqBelow g f k)
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
            let left = d.const_app(p.multiset_eq_below, &[f, g, bound]);
            let right = d.const_app(p.multiset_eq_below, &[g, f, bound]);
            d.bool_eq(left, right)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let true_val = d.bool_true();
            d.bool_refl(true_val)
        };
        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let cond1 = d.beq(fj, gj);
            let cond2 = d.beq(gj, fj);
            let x1 = d.const_app(p.multiset_eq_below, &[f, g, j]);
            let x2 = d.const_app(p.multiset_eq_below, &[g, f, j]);
            let false_val = d.bool_false();
            let left_sel = bool_select_bool(d, &p, cond1, x1, false_val);
            let mid_sel = bool_select_bool(d, &p, cond1, x2, false_val);
            let right_sel = bool_select_bool(d, &p, cond2, x2, false_val);
            let comm = d.lemma(p.beq_comm, &[fj, gj]);
            let align = congr_bool_to_bool(d, cond1, cond2, comm, &|d, c| {
                bool_select_bool(d, &p, c, x2, false_val)
            });
            let goal = d.bool_eq(left_sel, right_sel);
            let split = bool_true_or_false(d, &p, cond1);
            let true_val = d.bool_true();
            let is_true = d.bool_eq(cond1, true_val);
            let is_false = d.bool_eq(cond1, false_val);
            let branch_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let sel1 = select_bool_true(d, &p, cond1, x1, false_val, h);
                let sel2 = select_bool_true(d, &p, cond1, x2, false_val, h);
                let sel2_back = d.bool_symm(mid_sel, x2, sel2);
                let a = d.bool_trans(left_sel, x1, x2, sel1, ih);
                let b = d.bool_trans(left_sel, x2, mid_sel, a, sel2_back);
                let body = d.bool_trans(left_sel, mid_sel, right_sel, b, align);
                d.lam_fv(h_fv, is_true, body)
            };
            let branch_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let sel1 = select_bool_false(d, &p, cond1, x1, false_val, h);
                let sel2 = select_bool_false(d, &p, cond1, x2, false_val, h);
                let sel2_back = d.bool_symm(mid_sel, false_val, sel2);
                let a = d.bool_trans(left_sel, false_val, mid_sel, sel1, sel2_back);
                let body = d.bool_trans(left_sel, mid_sel, right_sel, a, align);
                d.lam_fv(h_fv, is_false, body)
            };
            or_cases(
                d,
                &p,
                is_true,
                is_false,
                goal,
                branch_true,
                branch_false,
                split,
            )
        };
        let proof = d.induct(&claim, &base, &step, k);
        let stmt = claim(d, k);
        declare_forall(
            d,
            p.multiset_eq_below_comm,
            &[(f_fv, fn_ty), (g_fv, fn_ty), (k_fv, nat)],
            stmt,
            proof,
        )?;
    }

    // beq_refl : ∀ m, Eq Bool (beq m m) Bool.true
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let g = d.const_app(p.multiset_count, &[m]);
        let b = ms_bound(d, &p, m);
        let width = d.add(b, b);
        let proof = d.lemma(p.multiset_eq_below_self, &[g, width]);
        let beq_mm = d.const_app(p.multiset_beq, &[m, m]);
        let true_val = d.bool_true();
        let stmt = d.bool_eq(beq_mm, true_val);
        declare_forall(d, p.multiset_beq_refl, &[(m_fv, ms)], stmt, proof)?;
    }

    // beq_comm : ∀ m1 m2, Eq Bool (beq m1 m2) (beq m2 m1)
    //
    // Two steps, because the two sides fold over `b1 + b2` and `b2 + b1`:
    // `eqBelow_comm` swaps the functions at a FIXED width, and `add_comm`
    // moves the width.
    {
        let m1_fv = d.fresh_fvar();
        let m1 = d.kernel().fvar(m1_fv);
        let m2_fv = d.fresh_fvar();
        let m2 = d.kernel().fvar(m2_fv);
        let c1 = d.const_app(p.multiset_count, &[m1]);
        let c2 = d.const_app(p.multiset_count, &[m2]);
        let b1 = ms_bound(d, &p, m1);
        let b2 = ms_bound(d, &p, m2);
        let width = d.add(b1, b2);
        let swapped_width = d.add(b2, b1);
        let start = d.const_app(p.multiset_eq_below, &[c1, c2, width]);
        let middle = d.const_app(p.multiset_eq_below, &[c2, c1, width]);
        let finish = d.const_app(p.multiset_eq_below, &[c2, c1, swapped_width]);
        let swap = d.lemma(p.multiset_eq_below_comm, &[c1, c2, width]);
        let widen = {
            let motive = d.eq_motive(width, &|d, y| {
                let lhs = d.const_app(p.multiset_eq_below, &[c2, c1, width]);
                let rhs = d.const_app(p.multiset_eq_below, &[c2, c1, y]);
                d.bool_eq(lhs, rhs)
            });
            let refl_case = d.bool_refl(middle);
            let comm = d.lemma(p.add_comm, &[b1, b2]);
            d.transport(width, motive, refl_case, swapped_width, comm)
        };
        let proof = d.bool_trans(start, middle, finish, swap, widen);
        let left = d.const_app(p.multiset_beq, &[m1, m2]);
        let right = d.const_app(p.multiset_beq, &[m2, m1]);
        let stmt = d.bool_eq(left, right);
        declare_forall(
            d,
            p.multiset_beq_comm,
            &[(m1_fv, ms), (m2_fv, ms)],
            stmt,
            proof,
        )?;
    }

    let _ = bool_ty;
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
    declare_arithmetic_support(d, p)?;
    declare_count_laws(d, p)?;
    declare_prod_range_valuation(d, p)?;
    declare_uniqueness(d, p)?;
    declare_beq_laws(d, p)?;
    Ok(())
}
