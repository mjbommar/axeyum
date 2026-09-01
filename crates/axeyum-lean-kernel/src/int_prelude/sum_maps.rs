//! `Int.sumMaps` — a finite sum **indexed by a function space**, and the
//! generalized distributive law that ADR-1135 recorded as inexpressible in
//! this kernel.
//!
//! # What this file refutes
//!
//! [ADR-1135](../../../../docs/research/09-decisions/adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
//! sized determinant multiplicativity and wrote, of the Cauchy–Binet route:
//!
//! > The Cauchy-Binet / multilinearity route expands `det (A*B)` as a sum over
//! > *functions* `[0,n) -> [0,n)`, then kills the non-injective ones by
//! > alternation. Same missing type, one level up: the index set of the outer
//! > sum is a function space, not a `Nat` range, so `Rat.sumRange` cannot
//! > express it.
//!
//! That is measurably false, and this file is the measurement. **A finite sum
//! does not need its index set to exist as a type — it needs a FOLD over the
//! index set, and a fold is a function.** `Int.sumMaps m n F` folds `Int.add`
//! over `F g` for every `g : [0,m) -> [0,n)`, by structural recursion on `m`
//! with a *higher-order* motive:
//!
//! ```text
//! sumMaps 0       n F = F (fun _ => 0)
//! sumMaps (m + 1) n F = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n
//! ```
//!
//! where `cons k g` is the `Nat -> Nat` that is `k` at `0` and `g (i - 1)`
//! after — built inline as a `Nat.rec` so that **both of its equations are
//! `Eq.refl`**, needing no `Nat.beq`, no `bool_select_nat`, and no ordering
//! lemma. That choice is load-bearing: the obvious alternative, "write index
//! `m` of `g` with `Nat.beq i m`", makes every step of the proof below carry
//! an `i < m` side condition, and buys nothing.
//!
//! The motive is `fun _ : Nat => ((Nat -> Nat) -> Int) -> Int`, constant in
//! the index and *not* `Int` — the same trick `Rat.det` already uses (its
//! motive is `fun _ : Nat => (Nat -> Nat -> Rat) -> Rat`, because its
//! recursive call is at a different matrix). Nothing new was added to the
//! kernel to make this work.
//!
//! # The theorem that demonstrates it
//!
//! [`declare_prod_range_sum_range_expand`] admits
//!
//! ```text
//! Int.prodRange_sumRange_expand :
//!   forall n m (c : Nat -> Nat -> Int),
//!     prodRange (fun i => sumRange (c i) n) m
//!       = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)
//! ```
//!
//! — the generalized distributive law: a product of `m` sums, each of `n`
//! terms, expands into a sum over all `n^m` functions `[0,m) -> [0,n)`. This
//! is **exactly** the expansion step of the Cauchy–Binet / multilinearity
//! proof of `det (A*B) = det A * det B`, and it is the step ADR-1135 named as
//! the wall. It is proved here by an ordinary induction on `m`, with no new
//! inductive type, no `List`, no `Finset`, no `Prod`, and no `funext`.
//!
//! Note what makes the induction go through: the motive quantifies over `c`,
//! because the successor step applies the induction hypothesis at
//! `fun i => c (succ i)` — a *different* coefficient family. This is the same
//! shape `Int.prodRange_permute` needs for its `sigma`, and the same shape
//! `Rat.det_congr` needs for its matrices.
//!
//! # What is NOT claimed
//!
//! `sumMaps` enumerates every `g : [0,m) -> [0,n)` exactly once *as a
//! summation schedule*; it does not give you a permutation type, an injectivity
//! predicate over that schedule, or a sign. The Cauchy–Binet proof needs those
//! next, and they are real work — see the "what actually blocks
//! multiplicativity" section of ADR-1310. The claim this file establishes is
//! narrower and precise: **the index set being a function space is not the
//! obstruction.**
//!
//! The definition's correctness is checked by *evaluation*, not by the trusted
//! gate — `Nat -> Nat -> ((Nat -> Nat) -> Int) -> Int` is that type whatever
//! the function returns. See `sum_maps_tests.rs`.

use super::defs::POW_HEIGHT;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.sumMaps`: one above `Int.sumRange`
/// (`POW_HEIGHT + 1`), which it unfolds to, following the
/// "outranks everything it unfolds to" convention.
const SUM_MAPS_HEIGHT: u16 = POW_HEIGHT + 2;

/// `(Nat -> Nat) -> Int`, the type of a summand indexed by a map.
fn fam_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_nat = d.arrow(nat, nat);
    d.arrow(fn_nat, int_ty)
}

/// `Nat -> Nat`, the type of an index map.
fn map_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `cons k g : Nat -> Nat` — `k` at index `0`, `g j` at index `succ j`.
///
/// Built inline as `fun i => Nat.rec.{1} (fun _ => Nat) k (fun j _ => g j) i`
/// so that **both** equations hold by `ι`-reduction alone. Deliberately NOT a
/// declared definition: it appears only inside `Int.sumMaps`'s own body and
/// inside proofs about it, so naming it would add a delta height and a name to
/// the shared `Nat` namespace for no reuse. (`CLAUDE.md` records that a prelude
/// declaring into another prelude's namespace is a measured hazard.)
fn cons_fn(d: &mut IntDev<'_>, k: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let gj = d.apply(g, &[j]);
        let inner = d.lam_fv(ih_fv, nat, gj);
        d.lam_fv(j_fv, nat, inner)
    };
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, k, minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun _ : Nat => Nat.zero` — the junk map the empty product is evaluated at.
///
/// Any total `Nat -> Nat` would do: `sumMaps 0 n F` is `F` applied to *some*
/// map, and the only consumer is a `prodRange _ 0`, which does not look at it.
fn junk_map(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let zero = d.zero();
    d.kernel().lam(anon, nat, zero, BinderInfo::Default)
}

/// `zero = mul zero z`, derived inline from `mul_comm` and `mul_zero` rather
/// than declared — `Int.zero_mul` does not exist in this prelude (checked:
/// only `Nat.zero_mul` does), and it is needed only by the two
/// `sumRange_mul_*` base cases in this file.
///
/// Stated in the **reversed** direction on purpose. At `n = 0` the goal is
/// `sumRange _ 0 = mul (sumRange f 0) z`, whose left side reduces to `zero`
/// and whose right side reduces to `mul zero z` — so what the induction wants
/// is `zero = mul zero z`, not the natural reading `mul zero z = zero`. The
/// first draft had it the natural way round and the kernel rejected the whole
/// prelude with an opaque `TypeMismatch` naming neither side.
fn zero_eq_zero_mul_proof(d: &mut IntDev<'_>, z: ExprId) -> ExprId {
    let p = d.int();
    let zero = d.izero();
    let comm = d.lemma(p.mul_comm, &[zero, z]);
    let mz = d.lemma(p.mul_zero, &[z]);
    let lhs = d.imul(zero, z);
    let mid = d.imul(z, zero);
    let fwd = d.itrans(lhs, mid, zero, comm, mz);
    d.isymm(lhs, zero, fwd)
}

/// Admit `Int.sumMaps : Nat -> Nat -> ((Nat -> Nat) -> Int) -> Int`.
///
/// Structural recursion on the FIRST argument with the higher-order motive
/// `fun _ : Nat => ((Nat -> Nat) -> Int) -> Int`; see the module doc.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_sum_maps(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fam = fam_ty(d);
    let map_t = map_ty(d);
    let fam_to_int = d.arrow(fam, int_ty);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // motive := fun _ : Nat => ((Nat -> Nat) -> Int) -> Int
    let motive = d.kernel().lam(anon, nat, fam_to_int, BinderInfo::Default);

    // base := fun F => F (fun _ => 0)
    let minor_zero = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let junk = junk_map(d);
        let body = d.apply(f, &[junk]);
        d.lam_fv(f_fv, fam, body)
    };

    // step := fun _j ih F => sumRange (fun k => ih (fun g => F (cons k g))) n
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let summand = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let shifted = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let c = cons_fn(d, k, g);
                let body = d.apply(f, &[c]);
                d.lam_fv(g_fv, map_t, body)
            };
            let body = d.apply(ih, &[shifted]);
            d.lam_fv(k_fv, nat, body)
        };
        let body = d.const_app(p.sum_range, &[summand, n]);
        let over_f = d.lam_fv(f_fv, fam, body);
        let over_ih = d.lam_fv(ih_fv, fam_to_int, over_f);
        d.lam_fv(j_fv, nat, over_ih)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let rec_app = d.apply(rec, &[motive, minor_zero, minor_succ, m]);

    let f_outer_fv = d.fresh_fvar();
    let f_outer = d.kernel().fvar(f_outer_fv);
    let applied = d.apply(rec_app, &[f_outer]);

    let value = {
        let over_f = d.lam_fv(f_outer_fv, fam, applied);
        let over_n = d.lam_fv(n_fv, nat, over_f);
        d.lam_fv(m_fv, nat, over_n)
    };
    let ty = {
        let over_f = d.arrow(fam, int_ty);
        let over_n = d.arrow(nat, over_f);
        d.arrow(nat, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sum_maps,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUM_MAPS_HEIGHT),
    })
}

/// `Int.sumMaps` applied at `m`, `n`, `f`.
fn sum_maps(d: &mut IntDev<'_>, m: ExprId, n: ExprId, f: ExprId) -> ExprId {
    let p = d.int();
    d.const_app(p.sum_maps, &[m, n, f])
}

/// The defining equations `Int.sumMaps_zero` and `Int.sumMaps_succ`, each an
/// `Eq.refl` at `Int` — `Int.sumMaps` computes on both minor premises.
///
/// # Errors
///
/// Returns the kernel's rejection if a generated proof does not check.
pub(super) fn declare_sum_maps_equations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    // sumMaps_zero : ∀ n F, Eq Int (sumMaps 0 n F) (F (fun _ => 0)).
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = sum_maps(d, zero_n, n, f);
        let junk = junk_map(d);
        let rhs = d.apply(f, &[junk]);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);
        let ty = {
            let over_f = d.pi_fv(f_fv, fam, stmt);
            d.pi_fv(n_fv, nat, over_f)
        };
        let value = {
            let over_f = d.lam_fv(f_fv, fam, proof);
            d.lam_fv(n_fv, nat, over_f)
        };
        d.declare_theorem(p.sum_maps_zero, ty, value)?;
    }

    // sumMaps_succ : ∀ m n F,
    //   Eq Int (sumMaps (succ m) n F)
    //          (sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n).
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let sm = d.succ(m);
        let lhs = sum_maps(d, sm, n, f);
        let summand = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let shifted = {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let c = cons_fn(d, k, g);
                let body = d.apply(f, &[c]);
                d.lam_fv(g_fv, map_t, body)
            };
            let body = sum_maps(d, m, n, shifted);
            d.lam_fv(k_fv, nat, body)
        };
        let rhs = d.const_app(p.sum_range, &[summand, n]);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);
        let ty = {
            let over_f = d.pi_fv(f_fv, fam, stmt);
            let over_n = d.pi_fv(n_fv, nat, over_f);
            d.pi_fv(m_fv, nat, over_n)
        };
        let value = {
            let over_f = d.lam_fv(f_fv, fam, proof);
            let over_n = d.lam_fv(n_fv, nat, over_f);
            d.lam_fv(m_fv, nat, over_n)
        };
        d.declare_theorem(p.sum_maps_succ, ty, value)?;
    }
    Ok(())
}

/// `Int.sumRange_mul_right :
///   ∀ f z n, Eq Int (sumRange (fun k => mul (f k) z) n) (mul (sumRange f n) z)`
/// — pull a constant RIGHT factor out of a finite sum.
///
/// Induction on `n`. Base: both sides are `mul zero z`, closed by
/// [`zero_mul_proof`]. Step: `Int.add_mul` read backwards.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_sum_range_mul_right(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // fun k => mul (f k) z
    let scaled = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = d.imul(fk, z);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let lhs = d.const_app(p.sum_range, &[scaled, x]);
        let prior = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.imul(prior, z);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| zero_eq_zero_mul_proof(d, z),
        &|d, j, ih| {
            // LHS(succ j) ≡ add (sumRange scaled j) (mul (f j) z)
            //            = add (mul (sumRange f j) z) (mul (f j) z)   [ih]
            //            = mul (add (sumRange f j) (f j)) z           [add_mul, symm]
            //            ≡ RHS(succ j)
            let prior_scaled = d.const_app(p.sum_range, &[scaled, j]);
            let prior = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let term = d.imul(fj, z);
            let start = d.iadd(prior_scaled, term);
            let scaled_prior = d.imul(prior, z);
            let mid = d.iadd(scaled_prior, term);
            let h1 = d.icongr(prior_scaled, scaled_prior, ih, &|d, t| d.iadd(t, term));
            let sum_succ = d.iadd(prior, fj);
            let end = d.imul(sum_succ, z);
            let dist = d.lemma(p.add_mul, &[prior, fj, z]);
            let h2 = d.isymm(end, mid, dist);
            let (_, proof) = d.ichain(start, &[(mid, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_z = d.pi_fv(z_fv, int_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_z)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_z = d.lam_fv(z_fv, int_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_z)
    };
    d.declare_theorem(p.sum_range_mul_right, ty, value)
}

/// `Int.sumRange_mul_left :
///   ∀ z f n, Eq Int (sumRange (fun k => mul z (f k)) n) (mul z (sumRange f n))`
/// — pull a constant LEFT factor out of a finite sum.
///
/// Induction on `n`. Base: `Int.mul_zero`. Step: `Int.left_distrib` backwards.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_sum_range_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let scaled = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let body = d.imul(z, fk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let lhs = d.const_app(p.sum_range, &[scaled, x]);
        let prior = d.const_app(p.sum_range, &[f, x]);
        let rhs = d.imul(z, prior);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // Goal at n = 0: `zero = mul z zero`. `mul_zero` states the
            // opposite direction, so it needs `isymm`.
            let zero = d.izero();
            let mz = d.lemma(p.mul_zero, &[z]);
            let lhs = d.imul(z, zero);
            d.isymm(lhs, zero, mz)
        },
        &|d, j, ih| {
            let prior_scaled = d.const_app(p.sum_range, &[scaled, j]);
            let prior = d.const_app(p.sum_range, &[f, j]);
            let fj = d.apply(f, &[j]);
            let term = d.imul(z, fj);
            let start = d.iadd(prior_scaled, term);
            let scaled_prior = d.imul(z, prior);
            let mid = d.iadd(scaled_prior, term);
            let h1 = d.icongr(prior_scaled, scaled_prior, ih, &|d, t| d.iadd(t, term));
            let sum_succ = d.iadd(prior, fj);
            let end = d.imul(z, sum_succ);
            let dist = d.lemma(p.left_distrib, &[z, prior, fj]);
            let h2 = d.isymm(end, mid, dist);
            let (_, proof) = d.ichain(start, &[(mid, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_f = d.pi_fv(f_fv, fn_ty, over_n);
        d.pi_fv(z_fv, int_ty, over_f)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_f = d.lam_fv(f_fv, fn_ty, over_n);
        d.lam_fv(z_fv, int_ty, over_f)
    };
    d.declare_theorem(p.sum_range_mul_left, ty, value)
}

/// `Int.sumMaps_congr :
///   ∀ n m F G, (∀ g, Eq Int (F g) (G g)) -> Eq Int (sumMaps m n F) (sumMaps m n G)`
/// — the pointwise congruence for a function-space-indexed sum.
///
/// Induction on `m` with the motive quantified over BOTH `F` and `G`: the
/// successor step applies the induction hypothesis at
/// `fun g => F (cons k g)` / `fun g => G (cons k g)`, a different pair, so a
/// motive that fixed them would give an unusable hypothesis. Same shape as
/// [`super::prod::declare_prod_range_permute`]'s generalization over `sigma`
/// and `Rat.det_congr`'s over its matrices.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_sum_maps_congr(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // motive x := ∀ F G, (∀ g, F g = G g) -> sumMaps x n F = sumMaps x n G
    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let pointwise = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let fa = d.apply(f, &[a]);
            let ga = d.apply(gg, &[a]);
            let eq = d.ieq(fa, ga);
            d.pi_fv(a_fv, map_t, eq)
        };
        let lhs = sum_maps(d, x, n, f);
        let rhs = sum_maps(d, x, n, gg);
        let concl = d.ieq(lhs, rhs);
        let with_h = d.arrow(pointwise, concl);
        let over_g = d.pi_fv(g_fv, fam, with_h);
        d.pi_fv(f_fv, fam, over_g)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // fun F G h => h (fun _ => 0)
            //   : F junk = G junk, defeq to sumMaps 0 n F = sumMaps 0 n G.
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let pointwise = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let fa = d.apply(f, &[a]);
                let ga = d.apply(gg, &[a]);
                let eq = d.ieq(fa, ga);
                d.pi_fv(a_fv, map_t, eq)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let junk = junk_map(d);
            let body = d.apply(h, &[junk]);
            let with_h = d.lam_fv(h_fv, pointwise, body);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
        },
        &|d, j, ih| {
            let f_fv = d.fresh_fvar();
            let f = d.kernel().fvar(f_fv);
            let g_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(g_fv);
            let pointwise = {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let fa = d.apply(f, &[a]);
                let ga = d.apply(gg, &[a]);
                let eq = d.ieq(fa, ga);
                d.pi_fv(a_fv, map_t, eq)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // shift F at k := fun g => F (cons k g)
            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            // pointwise summand equality at each k, from the ih.
            let summand_lhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift(d, f, k);
                let body = sum_maps(d, j, n, sf);
                d.lam_fv(k_fv, nat, body)
            };
            let summand_rhs = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sg = shift(d, gg, k);
                let body = sum_maps(d, j, n, sg);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sf = shift(d, f, k);
                let sg = shift(d, gg, k);
                let inner_h = {
                    let a_fv = d.fresh_fvar();
                    let a = d.kernel().fvar(a_fv);
                    let c = cons_fn(d, k, a);
                    let body = d.apply(h, &[c]);
                    d.lam_fv(a_fv, map_t, body)
                };
                let body = d.apply(ih, &[sf, sg, inner_h]);
                d.lam_fv(k_fv, nat, body)
            };
            let congr = d.lemma(p.sum_range_congr, &[summand_lhs, summand_rhs, n, per_k]);
            let with_h = d.lam_fv(h_fv, pointwise, congr);
            let over_g = d.lam_fv(g_fv, fam, with_h);
            d.lam_fv(f_fv, fam, over_g)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.sum_maps_congr, ty, value)
}

/// `Int.sumMaps_mul_left :
///   ∀ n m z H, Eq Int (sumMaps m n (fun g => mul z (H g))) (mul z (sumMaps m n H))`
/// — pull a constant LEFT factor out of a function-space-indexed sum.
///
/// Induction on `m`, motive quantified over `H` for the same reason as
/// [`declare_sum_maps_congr`]. The step is
/// [`declare_sum_range_mul_left`] composed with the induction hypothesis under
/// `Int.sumRange_congr`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_sum_maps_mul_left(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fam = fam_ty(d);
    let map_t = map_ty(d);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // scale H := fun g => mul z (H g)
    let scale = |d: &mut IntDev<'_>, hh: ExprId| {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let ha = d.apply(hh, &[a]);
        let body = d.imul(z, ha);
        d.lam_fv(a_fv, map_t, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let scaled = scale(d, hh);
        let lhs = sum_maps(d, x, n, scaled);
        let prior = sum_maps(d, x, n, hh);
        let rhs = d.imul(z, prior);
        let eq = d.ieq(lhs, rhs);
        d.pi_fv(h_fv, fam, eq)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // sumMaps 0 n (scale H) ≡ mul z (H junk) ≡ mul z (sumMaps 0 n H).
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);
            let junk = junk_map(d);
            let h_junk = d.apply(hh, &[junk]);
            let body = d.imul(z, h_junk);
            let refl = d.irefl(body);
            d.lam_fv(h_fv, fam, refl)
        },
        &|d, j, ih| {
            let h_fv = d.fresh_fvar();
            let hh = d.kernel().fvar(h_fv);

            let shift = |d: &mut IntDev<'_>, target: ExprId, k: ExprId| {
                let a_fv = d.fresh_fvar();
                let a = d.kernel().fvar(a_fv);
                let c = cons_fn(d, k, a);
                let body = d.apply(target, &[c]);
                d.lam_fv(a_fv, map_t, body)
            };

            // start ≡ sumMaps (succ j) n (scale H)
            //       ≡ sumRange (fun k => sumMaps j n (fun g => scale H (cons k g))) n
            // Note (fun g => (scale H) (cons k g)) is defeq to
            //      (fun g => mul z (H (cons k g))) = scale (shift H k).
            let inner_scaled = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let sc = scale(d, sh);
                let body = sum_maps(d, j, n, sc);
                d.lam_fv(k_fv, nat, body)
            };
            let inner_plain = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let prior = sum_maps(d, j, n, sh);
                let body = d.imul(z, prior);
                d.lam_fv(k_fv, nat, body)
            };
            let per_k = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = d.apply(ih, &[sh]);
                d.lam_fv(k_fv, nat, body)
            };
            let start = d.const_app(p.sum_range, &[inner_scaled, n]);
            let mid = d.const_app(p.sum_range, &[inner_plain, n]);
            let h1 = d.lemma(p.sum_range_congr, &[inner_scaled, inner_plain, n, per_k]);

            // mid = mul z (sumRange (fun k => sumMaps j n (shift H k)) n)
            //     ≡ mul z (sumMaps (succ j) n H)
            let bare = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sh = shift(d, hh, k);
                let body = sum_maps(d, j, n, sh);
                d.lam_fv(k_fv, nat, body)
            };
            let bare_sum = d.const_app(p.sum_range, &[bare, n]);
            let end = d.imul(z, bare_sum);
            let h2 = d.lemma(p.sum_range_mul_left, &[z, bare, n]);
            let (_, chained) = d.ichain(start, &[(mid, h1), (end, h2)]);
            d.lam_fv(h_fv, fam, chained)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        let over_z = d.pi_fv(z_fv, int_ty, over_m);
        d.pi_fv(n_fv, nat, over_z)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        let over_z = d.lam_fv(z_fv, int_ty, over_m);
        d.lam_fv(n_fv, nat, over_z)
    };
    d.declare_theorem(p.sum_maps_mul_left, ty, value)
}

/// `Int.prodRange_sumRange_expand :
///   ∀ n m (c : Nat -> Nat -> Int),
///     Eq Int (prodRange (fun i => sumRange (c i) n) m)
///            (sumMaps m n (fun g => prodRange (fun i => c i (g i)) m))`
///
/// **The generalized distributive law** — a product of `m` sums of `n` terms
/// each expands into a sum over all `n^m` maps `[0,m) -> [0,n)`. This is the
/// expansion step of the Cauchy–Binet / multilinearity proof of determinant
/// multiplicativity, which ADR-1135 recorded as inexpressible here.
///
/// Induction on `m`, motive quantified over `c` because the successor step
/// applies the induction hypothesis at `fun i => c (succ i)`. Both ends of the
/// step peel their FIRST factor with [`super::prod::declare_prod_range_shift_front`],
/// which is what makes `cons`'s two `Eq.refl` equations line up with no side
/// conditions.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not check.
pub(super) fn declare_prod_range_sum_range_expand(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let map_t = map_ty(d);
    let coef_ty = {
        let inner = d.arrow(nat, int_ty);
        d.arrow(nat, inner)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    // rows c := fun i => sumRange (c i) n
    let rows = |d: &mut IntDev<'_>, c: ExprId| {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let body = d.const_app(p.sum_range, &[ci, n]);
        d.lam_fv(i_fv, nat, body)
    };
    // picks c x := fun g => prodRange (fun i => c i (g i)) x
    let picks = |d: &mut IntDev<'_>, c: ExprId, x: ExprId| {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let inner = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let gi = d.apply(g, &[i]);
            let body = d.apply(c, &[i, gi]);
            d.lam_fv(i_fv, nat, body)
        };
        let body = d.const_app(p.prod_range, &[inner, x]);
        d.lam_fv(g_fv, map_t, body)
    };
    // tail c := fun i => c (succ i)
    let tail = |d: &mut IntDev<'_>, c: ExprId| {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let si = d.succ(i);
        let body = d.apply(c, &[si]);
        d.lam_fv(i_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let r = rows(d, c);
        let lhs = d.const_app(p.prod_range, &[r, x]);
        let pk = picks(d, c, x);
        let rhs = sum_maps(d, x, n, pk);
        let eq = d.ieq(lhs, rhs);
        d.pi_fv(c_fv, coef_ty, eq)
    };
    let stmt = motive(d, m);

    let proof = d.induct(
        &motive,
        &|d| {
            // Both sides reduce to Int.one: prodRange _ 0 ≡ one, and
            // sumMaps 0 n (picks c 0) ≡ picks c 0 junk ≡ prodRange _ 0 ≡ one.
            let c_fv = d.fresh_fvar();
            let one = d.ione();
            let refl = d.irefl(one);
            d.lam_fv(c_fv, coef_ty, refl)
        },
        &|d, j, ih| {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let sj = d.succ(j);

            let r = rows(d, c);
            let start = d.const_app(p.prod_range, &[r, sj]);

            // t1 := mul (sumRange (c 0) n) (prodRange (rows (tail c)) j)
            let zero_n = d.zero();
            let c0 = d.apply(c, &[zero_n]);
            let head_sum = d.const_app(p.sum_range, &[c0, n]);
            let tc = tail(d, c);
            let tail_rows = rows(d, tc);
            let tail_prod = d.const_app(p.prod_range, &[tail_rows, j]);
            let t1 = d.imul(head_sum, tail_prod);
            let h1 = d.lemma(p.prod_range_shift_front, &[r, j]);

            // t2 := mul (sumRange (c 0) n) (sumMaps j n (picks (tail c) j))
            let tail_picks = picks(d, tc, j);
            let tail_maps = sum_maps(d, j, n, tail_picks);
            let t2 = d.imul(head_sum, tail_maps);
            let ih_at_tail = d.apply(ih, &[tc]);
            let h2 = d.icongr(tail_prod, tail_maps, ih_at_tail, &|d, t| {
                d.imul(head_sum, t)
            });

            // The other end: RHS ≡ sumRange (fun k => sumMaps j n (fun g =>
            //   picks c (succ j) (cons k g))) n, and each inner body peels to
            //   mul (c 0 k) (picks (tail c) j g) by prod_range_shift_front,
            //   because cons k g 0 ≡ k and cons k g (succ i) ≡ g i.
            let shifted_body = |d: &mut IntDev<'_>, k: ExprId| {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let cg = cons_fn(d, k, g);
                let pk = picks(d, c, sj);
                let body = d.apply(pk, &[cg]);
                d.lam_fv(g_fv, map_t, body)
            };
            let scaled_body = |d: &mut IntDev<'_>, k: ExprId| {
                let g_fv = d.fresh_fvar();
                let g = d.kernel().fvar(g_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let tp = picks(d, tc, j);
                let tpg = d.apply(tp, &[g]);
                let body = d.imul(ck, tpg);
                d.lam_fv(g_fv, map_t, body)
            };

            let rhs_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = shifted_body(d, k);
                let body = sum_maps(d, j, n, sb);
                d.lam_fv(k_fv, nat, body)
            };
            let mid_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = scaled_body(d, k);
                let body = sum_maps(d, j, n, sb);
                d.lam_fv(k_fv, nat, body)
            };
            let pulled_summand = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let body = d.imul(ck, tail_maps);
                d.lam_fv(k_fv, nat, body)
            };

            // per-k: sumMaps j n (shifted_body k) = sumMaps j n (scaled_body k)
            let per_k_congr = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sb = shifted_body(d, k);
                let cb = scaled_body(d, k);
                let pointwise = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let cg = cons_fn(d, k, g);
                    let inner = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let cgi = d.apply(cg, &[i]);
                        let body = d.apply(c, &[i, cgi]);
                        d.lam_fv(i_fv, nat, body)
                    };
                    let sf = d.lemma(p.prod_range_shift_front, &[inner, j]);
                    d.lam_fv(g_fv, map_t, sf)
                };
                let body = d.lemma(p.sum_maps_congr, &[n, j, sb, cb, pointwise]);
                d.lam_fv(k_fv, nat, body)
            };
            // per-k: sumMaps j n (scaled_body k) = mul (c 0 k) (sumMaps j n (picks (tail c) j))
            let per_k_pull = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let ck = d.apply(c, &[zero_n, k]);
                let tp = picks(d, tc, j);
                let body = d.lemma(p.sum_maps_mul_left, &[n, ck, j, tp]);
                d.lam_fv(k_fv, nat, body)
            };

            let rhs_full = d.const_app(p.sum_range, &[rhs_summand, n]);
            let mid_full = d.const_app(p.sum_range, &[mid_summand, n]);
            let pulled_full = d.const_app(p.sum_range, &[pulled_summand, n]);
            let s1 = d.lemma(
                p.sum_range_congr,
                &[rhs_summand, mid_summand, n, per_k_congr],
            );
            let s2 = d.lemma(
                p.sum_range_congr,
                &[mid_summand, pulled_summand, n, per_k_pull],
            );
            // pulled_full = mul (sumRange (c 0) n) tail_maps = t2
            let s3 = d.lemma(p.sum_range_mul_right, &[c0, tail_maps, n]);
            let (_, rhs_to_t2) = d.ichain(rhs_full, &[(mid_full, s1), (pulled_full, s2), (t2, s3)]);
            let h3 = d.isymm(rhs_full, t2, rhs_to_t2);

            let (_, chained) = d.ichain(start, &[(t1, h1), (t2, h2), (rhs_full, h3)]);
            d.lam_fv(c_fv, coef_ty, chained)
        },
        m,
    );

    let ty = {
        let over_m = d.pi_fv(m_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_m)
    };
    let value = {
        let over_m = d.lam_fv(m_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_m)
    };
    d.declare_theorem(p.prod_range_sum_range_expand, ty, value)
}
